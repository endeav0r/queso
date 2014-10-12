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


function solver (quesoGraph, assertions, values)
    local smtlib2Header = "(set-option :produce-models true)\n"
    smtlib2Header = smtlib2Header .. "(set-logic QF_AUFBV)\n"
    smtlib2Header = smtlib2Header .. "(set-info :smt-lib-version 2.0)\n"

    local smtlib2 = quesoGraph:smtlib2Declarations() .. quesoGraph:smtlib2()

    local daFile = smtlib2Header .. smtlib2
    daFile = daFile .. table.concat(assertions, '\n') .. '\n'
    daFile = daFile .. "(check-sat)\n"
    --daFile = daFile .. '(get-model)\n'
    daFile = daFile .. "(get-value (" .. table.concat(values, " ") .. "))"

    local fh = io.open('/tmp/smtlib2.smt2', 'w')
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
local quesoGraph = lqueso.x86acyclicDepth(mainAddress, memoryModel, 350)

print('applying ssa')
quesoGraph:ssa(0)

print('gathering eip variables')

function find_last_ret_eip (graph)
    local last_eip = nil
    for i,instruction in pairs(graph:g_vertices()) do
        -- for every ret instruction, find the last eip that's set
        if instruction:g_pc():number() == 0x804845f then
        --if string.match(instruction:queso(), 'ret') then
            print('found ret', instruction:g_pc())
            local flattened = instruction:flatten()
            for k, instruction in pairs(flattened) do
                local operandWritten = instruction:operand_written()
                if operandWritten ~= nil then 
                    if operandWritten:name() == 'eip' then
                        last_eip = operandWritten
                    end
                end
            end
            print('last eip = ' .. last_eip:smtlib2())
        end
    end
    return last_eip
end

last_eip = find_last_ret_eip(quesoGraph)
local sliceGraph = quesoGraph:slice_backward_thin(last_eip)
sliceGraph:ssa(#sliceGraph:g_vertices() - 1)

local vertices = sliceGraph:g_vertices()
print(vertices[1])

last_eip = sliceGraph:g_vertices()[1]:operand_written()
--last_eip = find_last_ret_eip(sliceGraph)
print('last eip => ' .. last_eip:smtlib2())

quesoGraph = sliceGraph

-- pass to solver, solving for eip
solver(quesoGraph, 
       {
        createAssertion('eip_0', '#x08048430'),
        createAssertion('esp_0', '#xbfff0000'),
        createAssertion('(select memory_0 esp_0)', '#x41'),
        createAssertion('(select memory_0 (bvadd esp_0 #x00000001))', '#x41'),
        createAssertion('(select memory_0 (bvadd esp_0 #x00000002))', '#x41'),
        createAssertion('(select memory_0 (bvadd esp_0 #x00000003))', '#x41'),


        createAssertion('(select memory_0 (bvadd #xbfff0008))', '#x40'),
        createAssertion('(select memory_0 (bvadd #xbfff0009))', '#x40'),
        createAssertion('(select memory_0 (bvadd #xbfff000a))', '#x40'),
        createAssertion('(select memory_0 (bvadd #xbfff000b))', '#x40'),

        createAssertion('(select memory_0 (bvadd #x40404044))', '#x4c'),
        createAssertion('(select memory_0 (bvadd #x40404045))', '#x40'),
        createAssertion('(select memory_0 (bvadd #x40404046))', '#x40'),
        createAssertion('(select memory_0 (bvadd #x40404047))', '#x40'),
        --createAssertion('argv_1_1', getValue32Load('memory_0', '(bvadd argv_1_1 #x00000004)')),
        --createAssertion('argv', getValue32Load('memory_0', 'argv_1_1')),
        createAssertion(last_eip:smtlib2(), '#xdeadbeef')
       },
       {last_eip:smtlib2(),
        'esp_0',
        'esp_10',
        --[[
        'argv_1',
        'argv_1_1',
        'argv',
        getValue32Load('memory_0', '(bvadd argv #x00000000)'),
        getValue32Load('memory_0', '(bvadd argv #x00000004)'),
        getValue32Load('memory_0', '(bvadd argv #x00000008)'),
        getValue32Load('memory_0', '(bvadd argv #x0000000c)'),
        getValue32Load('memory_0', '(bvadd argv #x00000010)'),
        getValue32Load('memory_0', '(bvadd argv #x00000014)'),
        getValue32Load('memory_0', '(bvadd argv #x0000001c)'),
        getValue32Load('memory_0', '(bvadd argv #x00000020)'),
        getValue32Load('memory_0', '(bvadd argv #x00000024)'),
        getValue32Load('memory_0', '(bvadd argv #x0000002c)'),
        getValue32Load('memory_0', '(bvadd argv #x00000030)'),
        getValue32Load('memory_0', '(bvadd argv #x00000034)'),
        getValue32Load('memory_0', '(bvadd argv #x00000038)'),
        ]]--
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
        
        getValue32Load('memory_0', 'esp_0')})
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
