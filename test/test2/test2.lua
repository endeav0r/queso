lqueso = require('lqueso')


function inTable (haystack, needle)
    for k,v in pairs(haystack) do
        if v == needle then
            return true
        end
    end
    return false
end


function map (f, t)
    local r = {}
    for k,v in pairs(t) do
        r[k] = f(v)
    end
    return r
end


function mapInstruction (f, instruction)
    local r = {}
    table.insert(r, f(instruction))
    for i,depth_instruction in pairs(instrution:depth_instructions()) do
        local subR = mapInstruction(f, depth_instruction)
        for k,v in pairs(subR) do
            table.insert(r, v)
        end
    end
    return r
end


function graphFindIndex (graph, index)
    for k,v in pairs(graph:g_vertices()) do
        if v:g_vIndex() == index then return v end
    end
    return nil
end


function assertControlFlow (graph)
    local declarations = {}
    local assertions = {}

    for k,instruction in pairs(graph:g_vertices()) do
        table.insert(declarations, '(declare-fun vIndex_' .. instruction:g_vIndex():number() .. ' () Bool)')
    end

    for k, instruction in pairs(graph:g_vertices()) do
        
        local successors = instruction:g_successors()
        if #successors == 1 then
            table.insert(assertions, '(assert (= vIndex_' .. instruction:g_vIndex():number() .. ' vIndex_' .. successors[1]:number() .. '))')
        elseif #successors == 2 then
            local a = '(assert (= vIndex_' .. instruction:g_vIndex():number() .. ' '
            a = a ..  '(xor vIndex_' .. successors[1]:number() .. ' vIndex_' .. successors[2]:number() .. ')))'
            table.insert(assertions, a)
        elseif #successors > 2 then
            print('ERROR, ' .. #successors .. ' successors')
        end
    end
    return assertions, declarations
end


function assertPC (graph)
    local assertions = {}
    for k, instruction in pairs(graph:g_vertices()) do
        -- assert control flow after every call
        --[[
        if string.match(instruction:queso(), 'call') then
            local successors = instruction:g_successors()
            for k, successor in pairs(map(function (s) return graphFindIndex(graph, s) end, successors)) do
                -- get value of eip at start of this instruction
                local eip = successor:flatten()[2]:operands_read()[1]
                for k,v in pairs(successor:flatten()) do print('-- ' .. v:queso()) end
                local assertion =  '(assert (= vIndex_' .. successor:g_vIndex():number() .. 
                                   ' (ite (= ' .. eip:smtlib2() .. ' #x' ..
                                   string.format('%08x', successor:g_pc():number()) .. ') true false)))'
                --table.insert(assertions, assertion)
                print(assertion)
                print(successor:g_pc())
            end

        end
        ]]--
        for k, subIns in pairs(instruction:flatten()) do
            if string.match(subIns:queso(), 'ite') ~= nil and
               subIns:operand_written():name() == 'eip'
               and string.match(instruction:queso(), 'jmp') == nil then
                -- we've reached a conditional jump
                -- assert eip before this conditional jump
                -- get the first eip value of this instruction
                local opsRead = instruction:flatten()[1]:operands_read()
                local eip = opsRead[1]
                -- we will assert the successor addresses of this jump
                local successors = instruction:g_successors()
                -- we are going to tie EIP values with vIndex values
                for k, successor in pairs(successors) do
                    local successorInstruction = graphFindIndex(graph, successor)
                    local assertion = '(assert (= vIndex_' ..
                                      successor:number() .. ' (ite (= ' ..
                                      subIns:operand_written():smtlib2() ..
                                      ' #x' .. string.format('%08x', successorInstruction:g_pc():number()) ..
                                      ') true false)))'
                    table.insert(assertions, assertion)
                end
                -- we are also going to require that one of the successors is true
                -- as long as this node is also true
                table.insert(assertions, '(assert (= true (ite (= vIndex_' ..
                                         instruction:g_vIndex():number() .. ' true) ' ..
                                         '(xor vIndex_' ..
                                         successors[1]:number() .. ' vIndex_' ..
                                         successors[2]:number() .. ') true)))')
            end
        end
    end
    return assertions
end


function createAssertion (variableName, value)
    return "(assert (= "
           .. variableName
           .. " "
           .. value
           .. "))"
end


function getValue32Load (memory, address)
    return '(concat (select ' .. memory .. ' (bvadd ' .. address .. ' #x00000003)) ' ..
                   '(select ' .. memory .. ' (bvadd ' .. address .. ' #x00000002)) ' ..
                   '(select ' .. memory .. ' (bvadd ' .. address .. ' #x00000001)) ' ..
                   '(select ' .. memory .. ' (bvadd ' .. address .. ' #x00000000)))'
end


function solver (quesoGraph, assertions, values, declarations)
    local smtlib2Header = "(set-option :produce-models true)\n"
    smtlib2Header = smtlib2Header .. "(set-logic QF_AUFBV)\n"
    smtlib2Header = smtlib2Header .. "(set-info :smt-lib-version 2.0)\n"

    local smtlib2 = quesoGraph:smtlib2Declarations() 
    if declarations then smtlib2 = smtlib2 .. table.concat(declarations, '\n') .. '\n' end
    smtlib2  = smtlib2 .. quesoGraph:smtlib2()

    local daFile = smtlib2Header .. smtlib2
    daFile = daFile .. table.concat(assertions, '\n') .. '\n'
    daFile = daFile .. "(check-sat)\n"
    --daFile = daFile .. '(get-model)\n'
    daFile = daFile .. "(get-value (" .. table.concat(values, " ") .. "))"

    local fh = io.open('test2.smt2', 'w')
    fh:write(daFile)
    fh:close()
end


local test2 = lqueso.elf32('test2')

local memoryModel = test2:memoryModel()

-- this is where we go to crazy town, replacing PLT entries with ret for certain
-- relocations
local reloc_rets = {'puts'}
local relocs = test2:relocs()
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
        local plt = test2:sections()['.plt']
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

print('getting acyclic graph')
local mainAddress = test2:symbols()['main']['address']
local quesoGraph = lqueso.x86treeDepth(mainAddress, memoryModel, 256)

print('applying ssa')
quesoGraph:ssa(0)

print('gathering eip variables')

function find_last_ret_eip (graph)
    local last_eip = nil
    for i,instruction in pairs(graph:g_vertices()) do
        -- for every ret instruction, find the last eip that's set
        if instruction:g_pc():number() == 0x804845f then
        --if string.match(instruction:queso(), 'ret') then
            local flattened = instruction:flatten()
            for k, instruction in pairs(flattened) do
                local operandWritten = instruction:operand_written()
                if operandWritten ~= nil then 
                    if operandWritten:name() == 'eip' then
                        last_eip = operandWritten
                    end
                end
            end
        end
    end
    return last_eip
end

last_eip = find_last_ret_eip(quesoGraph)
--local sliceGraph = quesoGraph:slice_backward(last_eip)
--sliceGraph:ssa(#sliceGraph:g_vertices() - 1)

--local vertices = sliceGraph:g_vertices()
--print(vertices[1])

--last_eip = sliceGraph:g_vertices()[1]:operand_written()
--last_eip = find_last_ret_eip(sliceGraph)
print('last eip => ' .. last_eip:smtlib2())

--quesoGraph = sliceGraph

-- pass to solver, solving for eip
--local assertions = assertControlFlow(quesoGraph)
local controlFlowAssertions, declarations = assertControlFlow(quesoGraph)
local pcAssertions = assertPC(quesoGraph)

local assertions = {}
for k,v in pairs(controlFlowAssertions) do table.insert(assertions, v) end
for k,v in pairs(pcAssertions) do table.insert(assertions, v) end

--for k,assertion in pairs(assertions) do print(assertion) end
table.insert(assertions, createAssertion('eip_0', '#x08048430'))
table.insert(assertions, createAssertion('esp_0', '#xbfff0000'))
--table.insert(assertions, createAssertion('al_57', '#x00'))

table.insert(assertions, createAssertion('(select memory_0 esp_0)', '#x41'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd esp_0 #x00000001))', '#x41'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd esp_0 #x00000002))', '#x41'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd esp_0 #x00000003))', '#x41'))


table.insert(assertions, createAssertion('(select memory_0 (bvadd #xbfff0008))', '#x40'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd #xbfff0009))', '#x40'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd #xbfff000a))', '#x40'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd #xbfff000b))', '#x40'))

table.insert(assertions, createAssertion('(select memory_0 (bvadd #x40404044))', '#x4c'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd #x40404045))', '#x40'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd #x40404046))', '#x40'))
table.insert(assertions, createAssertion('(select memory_0 (bvadd #x40404047))', '#x40'))

table.insert(assertions, createAssertion(last_eip:smtlib2(), '#xdeadbeef'))


--table.insert(assertions, '(assert (= vIndex_609 true))')
--table.insert(assertions, createAssertion('notZF_34', '#b0'))

for k, instruction in pairs(quesoGraph:g_vertices()) do
    if string.match(instruction:queso(), 'ret') ~= nil then
        local eip = instruction:flatten()[3]:operand_written()
        if eip:smtlib2() == last_eip:smtlib2() then
            print(eip:smtlib2())
            print(instruction:g_vIndex():number())
        end
    end
end

solver(quesoGraph, assertions,
       {last_eip:smtlib2(),
       'vIndex_18', 'vIndex_19',
       'vIndex_17', 'vIndex_35', 'vIndex_53', 'vIndex_71',
       'vIndex_89', 'vIndex_107', 'vIndex_124', 'vIndex_143',
       'vIndex_609',
       'rhs_sext_1',
       'eip_10',
       'eip_11',
       'eip_12',
       
        'eip_752',
        'eip_21',
        'eip_44',
        'eip_45',
        'eip_774',
        'eip_772',
        'eip_767',
        'esp_0',
        'esp_10',
        'eip_214',
        'rhs_sext_2',
        'eip_215',
        'eip_759',
        'eax_91',
        'ZF_52',
        'notZF_1',  'eip_21',
        'notZF_2',  'eip_44',
        'notZF_3',  'eip_67',
        'notZF_4',  'eip_90',
        'notZF_5',  'eip_113',
        'notZF_6',  'eip_136',
        'notZF_7',  'eip_159',
        'notZF_8',  'eip_182',
        'notZF_9',  'eip_205',
        'notZF_10', 'eip_228',
        'notZF_11', 'eip_251',
        'notZF_12', 'eip_274',
        'notZF_13', 'eip_297',
        'notZF_14', 'eip_320',
        'notZF_15', 'eip_343',
        'notZF_16', 'eip_366',
        'notZF_17', 'eip_389',
        'notZF_18', 'eip_412',
        'notZF_19', 'eip_435',
        'notZF_20', 'eip_458',
        'notZF_21', 'eip_481',
        'notZF_22', 'eip_504',
        'notZF_23', 'eip_527',
        'notZF_24', 'eip_550',
        'notZF_25', 'eip_573',
        'notZF_26', 'eip_596',
        'notZF_27', 'eip_619',
        'notZF_28', 'eip_642',
        'notZF_29', 'eip_665',
        'notZF_30', 'eip_688',
        'notZF_31', 'eip_711',
        'notZF_32', 'eip_734',
        'notZF_33', 'eip_757',
        'notZF_34', 'eip_780',
        'vIndex_594',
        'vIndex_595',
        'eip_759',
        getValue32Load('memory_0', '#xbfff0000'),
        getValue32Load('memory_0', '#xbfff0008'),
        getValue32Load('memory_0', '#xbfff000c'),
        getValue32Load('memory_0', '#x40404040'),
        getValue32Load('memory_0', '#x40404044'),
        getValue32Load('memory_0', '#x40404048'),
        getValue32Load('memory_0', '#x4040404c'),
        getValue32Load('memory_0', '#x40404050'),
        getValue32Load('memory_0', '#x40404054'),
        getValue32Load('memory_0', '#x40404058'),
        getValue32Load('memory_0', '#x4040405c'),
        getValue32Load('memory_0', '#x40404060'),
        getValue32Load('memory_0', '#x40404064'),
        getValue32Load('memory_0', '#x40404068'),
        getValue32Load('memory_0', '#x4040406c'),
        getValue32Load('memory_0', '#x40404070'),
        getValue32Load('memory_0', '#x40404074'),
        getValue32Load('memory_0', '#x40404078'),
        getValue32Load('memory_0', '#x4040407c'),
        getValue32Load('memory_0', '#x40404080'),
        getValue32Load('memory_0', '#x40404084'),
        getValue32Load('memory_0', '#x40404088'),
        getValue32Load('memory_0', '#x4040408c'),
        getValue32Load('memory_0', '#x40404090'),
        getValue32Load('memory_0', '#x40404094'),
        
        getValue32Load('memory_0', 'esp_0')},
        declarations)
--[[
    local flattened = instruction:flatten()
    for k, instruction in pairs(flattened) do
        local operandWritten = instruction:operand_written()
        if operandWritten ~= nil then
            if operandWritten:name() == "eip" then
                table.insert(eips, operandWritten)
            end
        end
    end
end

for k,eip in pairs(eips) do 
    local sliceGraph = quesoGraph:slice_backward(eip)

    local fh = io.open('eip_graphs/' .. eip:smtlib2() .. '.dot', 'w')
    fh:write(sliceGraph:dotGraph())
    fh:close()

    print('eip done: ' .. eip:smtlib2() .. ', num_vertices: ' .. #sliceGraph:g_vertices())
end

print('total vertices: ', #quesoGraph:g_vertices())
--]]
print('writing dot graph')
local fh = io.open('test2.dot', 'w')
fh:write(quesoGraph:dotGraph())
fh:close()
