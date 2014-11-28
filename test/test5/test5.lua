lqueso = require('lqueso')

local DEPTH = 128



function inTable (haystack, needle)
    for k,v in pairs(haystack) do
        if v == needle then
            return true
        end
    end
    return false
end


function map (f, t)
    local result = {}
    for k,v in pairs(t) do
        result[k] = f(v)
    end
    return result
end

function reduce (f, t)
    local result = nil
    for k,v in pairs(t) do
        result = f(result, v)
    end
    return result
end


function vertexMap_ (quesoGraph)
    local result = {}
    for k,v in pairs(quesoGraph:g_vertices()) do
        result[v:g_vIndex():number()] = v
    end
    return result
end


function dominatorMap_ (vertexMap)
    local dominators = {}
    local stack = {}
    for vIndex,instruction in pairs(vertexMap) do
        -- if dominators already set for the vertex, skip it
        if dominators[vIndex] == nil then
            -- add this to the stack
            table.insert(stack, 1, vIndex)
            -- process the stack
            while #stack > 0 do
                vIndex = stack[1]
                table.remove(stack, 1)
                instruction = vertexMap[vIndex]

                local predecessors = instruction:g_predecessors()

                if #predecessors == 0 then
                    dominators[vIndex] = {vIndex}
                else

                    local predecessors = instruction:g_predecessors()

                    -- check if all predecessors are set
                    local predecessorsSet = true
                    for k,vIndex in pairs(predecessors) do
                        if dominators[vIndex:number()] == nil then
                            predecessorsSet = false
                            break
                        end
                    end
                    -- if set, then this vertex's dominators are its
                    -- immediate dominators, and all their dominators
                    if predecessorsSet then
                        dominators[vIndex] = {vIndex}
                        for k,predecessor in pairs(predecessors) do
                            local predecessor = predecessor:number()
                            for k,dominator in pairs(dominators[predecessor]) do
                                table.insert(dominators[vIndex], dominator)
                            end
                        end

                        -- remove duplicates
                        table.sort(dominators[vIndex])
                        local i = 1
                        while i <= #dominators[vIndex] - 1 do
                            if dominators[vIndex][i] == dominators[vIndex][i + 1] then
                                table.remove(dominators[vIndex], i)
                            else
                                i = i + 1
                            end
                        end
                    -- if not set, we add this vertex to the stack, and then
                    -- its predecessors
                    else
                        table.insert(stack, 1, vIndex)
                        for k,predecessor in pairs(predecessors) do
                            table.insert(stack, 1, predecessor:number())
                        end
                    end
                end
            end
        end
    end
    return dominators
end


function assertControlFlow (graph)
    local declarations = {}
    local assertions = {}
    local vertexMap = vertexMap_(graph)
    local dominatorMap = dominatorMap_(vertexMap)

    for k,instruction in pairs(graph:g_vertices()) do
        table.insert(declarations, '(declare-fun vIndex_' .. instruction:g_vIndex():number() .. ' () Bool)')
        vertexMap[instruction:g_vIndex():number()] = instruction
    end

    for k, instruction in pairs(graph:g_vertices()) do
        
        local predecessors = instruction:g_predecessors()
        if #predecessors > 1 then
            -- we create a clause for each predecessor, based on whether other
            -- predecessors are a dominator of each predecessor
            local dominators = {}
            for k, predecessor in pairs(predecessors) do
                dominators[predecessor:number()] = {predecessor:number()}
                for k2, predecessor2 in pairs(predecessors) do
                    if k ~= k2 and inTable(dominatorMap[predecessor:number()], predecessor2:number()) then
                        table.insert(dominators[predecessor:number()], predecessor2:number())
                    end
                end
            end

            local clauses = {}
            for k, predecessor in pairs(predecessors) do
                function predecessorClause (a, b)
                    if a == nil then return b end
                    return '(and ' .. a .. ' ' .. b .. ')'
                end
                table.insert(clauses, reduce(predecessorClause,
                                             map(function (x) return 'vIndex_' .. x end,
                                                 dominators[predecessor:number()])))
            end

            -- one, and only one, clause can hold true
            function xorClauses (clauses)
                local result = {}
                if #clauses == 0 then return '' end
                if #clauses == 1 then return clauses[1] end
                if #clauses == 2 then
                    return '(xor ' .. clauses[1] .. ' ' .. clauses[2] .. ')'
                end

                -- no table slicing in lua :/
                local a = {}
                local b = {}
                for i=1,#clauses do
                    if i < #clauses / 2 then
                        table.insert(a, clauses[i])
                    else
                        table.insert(b, clauses[i])
                    end
                end
                return '(xor ' .. xorClauses(a) .. ' ' .. xorClauses(b) .. ')'
            end

            table.insert(assertions, '(assert (= vIndex_' .. instruction:g_vIndex():number() .. ' ' ..
                                     xorClauses(clauses) .. '))')
        end

        if #predecessors == 1 then
            table.insert(assertions, '(assert (= vIndex_' .. instruction:g_vIndex():number() ..
                                     ' vIndex_' .. predecessors[1]:number() .. '))')
        end
    end
    return assertions, declarations
end


function tieEiptovIndex (quesoGraph)
    local assertions = {}

    for k, instruction in pairs(quesoGraph:g_vertices()) do
        local instructions = instruction:flatten()
        local lastpc = nil
        for k, ins in pairs(instructions) do
            if ins:g_pc() ~= nil then lastpc = ins:g_pc() end
            local operands_read = ins:operands_read()
            local eipSet = false
            for k, operand in pairs(operands_read) do
                if operand:name() == 'eip' then
                    if lastpc ~= nil then
                        local assertion = '(assert (= vIndex_' .. instruction:g_vIndex():number() ..
                            ' (ite (= ' .. operand:smtlib2() .. ' #x' .. 
                            string.format('%08x', lastpc:number()) .. ') true false)))'
                        table.insert(assertions, assertion)
                        eipSet = true
                        break
                    end
                end
            end
            if eipSet then
                break
            end
        end
    end

    return assertions
end


function forZ3 (quesoGraph, declarations, assertions, values)
    local smtlib2Header = "(set-option :produce-models true)\n"
    smtlib2Header = smtlib2Header .. "(set-logic QF_AUFBV)\n"
    smtlib2Header = smtlib2Header .. "(set-info :smt-lib-version 2.0)\n"

    local smtlib2 = smtlib2Header .. 
                    quesoGraph:smtlib2Declarations() .. '\n' ..
                    quesoGraph:smtlib2() .. '\n' ..
                    table.concat(declarations, '\n') .. '\n' ..
                    table.concat(assertions, '\n') .. '\n' ..
                    '(check-sat)' .. '\n' ..
                    '(get-value (' .. table.concat(values, ' ') .. '))'
    return smtlib2
end


local elf32 = lqueso.elf32('test5')

local memoryModel = elf32:memoryModel()


-- this is where we go to crazy town, replacing PLT entries with ret for certain
-- relocations
local reloc_rets = {'puts'}
local relocs = elf32:relocs()
for name,reloc in pairs(relocs) do
    if inTable(reloc_rets, name) then
        pattern = {}
        address = reloc['address']:number()
        table.insert(pattern, 0xff)
        table.insert(pattern, 0x25)
        table.insert(pattern, bit32.band(address, 0xff))
        table.insert(pattern, bit32.band(bit32.rshift(address, 8), 0xff))
        table.insert(pattern, bit32.band(bit32.rshift(address, 16), 0xff))
        table.insert(pattern, bit32.band(bit32.rshift(address, 24), 0xff))
        print(table.concat(map(tostring, pattern), ' '))

        -- search for pattern
        local plt = elf32:sections()['.plt']
        local needle = 1
        for haystack = plt['address']:number(),plt['address']:number() + plt['size']:number() do
            if memoryModel:g_byte(haystack) == pattern[needle] then
                if needle == #pattern then
                    print('found plt entry for ' .. name)
                    print('haystack = ' .. luint64.luint64(haystack):string())
                    print('setting ' .. luint64.luint64(haystack - #pattern + 1):string() .. ' to 0xc3')
                    memoryModel:s_byte(haystack - #pattern + 1, 0xc3)
                    break
                end
                needle = needle + 1
            else
                needle = 1
            end
        end
    end
    print(name, reloc, inTable(reloc_rets, name))
end


print('getting graph', elf32:symbols()['main']['address'])
local quesoGraph = lqueso.x86acyclicDepth(elf32:symbols()['main']['address'], memoryModel, DEPTH)

print(#quesoGraph:g_vertices() .. " vertices")

quesoGraph:blockize()
print(#quesoGraph:g_vertices() .. " vertices blocketized")

print('applying ssa')
quesoGraph:ssa()

print('setting some constants')
local eip_0_constant = lqueso.constant(32, elf32:symbols()['main']['address'])
local esp_0_constant = lqueso.constant(32, luint64.luint64("0xbe000000"))
local ebp_0_constant = lqueso.constant(32, luint64.luint64("0xbf000000"))
quesoGraph:replace_operand(lqueso.variable(32, "eip", 0), eip_0_constant)
quesoGraph:replace_operand(lqueso.variable(32, "ebp", 0), ebp_0_constant)
quesoGraph:replace_operand(lqueso.variable(32, "esp", 0), esp_0_constant)

quesoGraph:dead_code_elimination()
quesoGraph:dead_code_elimination()

quesoGraph:constant_fold_propagate()

quesoGraph:dead_code_elimination()
quesoGraph:dead_code_elimination()
quesoGraph:dead_code_elimination()
quesoGraph:dead_code_elimination()
quesoGraph:dead_code_elimination()
quesoGraph:dead_code_elimination()

print('writing dot graph')
local fh = io.open('test.dot', 'w')
fh:write(quesoGraph:dotGraph())
fh:close()

local fh = io.open('test.json', 'w')
--fh:write(quesoGraph:json())
fh:close()

print('asserting control flow')
local assertions, declarations = assertControlFlow(quesoGraph)
for k, assertion in pairs(tieEiptovIndex(quesoGraph)) do
    table.insert(assertions, assertion)
end


--table.insert(assertions, '(assert (= eip_0 #x080483dc))')
--table.insert(assertions, '(assert (= esp_0 #xbf000000))')

print('creating z3 code')

local z3code = forZ3(quesoGraph, declarations, assertions,
                     {'eip_15', 'eip_92', 'eip_172'})

local fh = io.open('test.smt2', 'w')
fh:write(z3code)
fh:close()