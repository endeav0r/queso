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


function sliceOpcode (quesoGraph, opcode)
    local result = {}
    for k,instruction in pairs(quesoGraph:g_vertices()) do
        for k,flatIns in pairs(instruction:flatten()) do
            if flatIns:opcode() == opcode then
                table.insert(result, flatIns)
            end
        end
    end
    return result
end


function phiReduce (phiOperands)
    if #phiOperands == 1 then
        return phiOperands[1].operand:smtlib2()
    else
        local phiOperand = phiOperands[1]
        table.remove(phiOperands, 1)
        local result = '(ite (= v' .. tostring(phiOperand.vIndex) .. '_0 #b1) ' ..
                       phiOperand.operand:smtlib2() .. ' ' ..
                       phiReduce(phiOperands) .. ')'
        return result
    end
end


function phiAssertions (quesoGraph)
    local assertions = {}
    for k,phi in pairs(sliceOpcode(quesoGraph, "phi")) do
        local assertion = '(assert (= ' .. phi:dst():smtlib2() .. ' ' ..
                          phiReduce(phi:phiOperands()) .. '))'
        table.insert(assertions, assertion)
    end
    return table.concat(assertions, '\n')
end



local elf32 = lqueso.elf32('test3')

local memoryModel = elf32:memoryModel()

-- this is where we go to crazy town, replacing PLT entries with ret for certain
-- relocations
local reloc_rets = {'puts'}
local relocs = elf32:relocs()
for name,reloc in pairs(relocs) do
    if inTable(reloc_rets, name) then
        pattern = {}
        address = reloc['address']
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
        for haystack = plt['address'],plt['address'] + plt['size'] do
            if memoryModel:g_byte(haystack) == pattern[needle] then
                if needle == #pattern then
                    print('found plt entry for ' .. name)
                    print('haystack = ' .. string.format("%016x", haystack))
                    print('setting ' .. string.format("%016x", (haystack - #pattern + 1)) .. ' to 0xc3')
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
print(#quesoGraph:g_vertices() .. " vertices blocketized")

print('setting constants for initial eip, ebp and esp')
local eip_0_constant = lqueso.constant(32, elf32:symbols()['main']['address'])
local esp_0_constant = lqueso.constant(32, 0xbe000000)
local ebp_0_constant = lqueso.constant(32, 0xbf000000)
quesoGraph:replace_operand(lqueso.variable(32, "eip", 0), eip_0_constant)
quesoGraph:replace_operand(lqueso.variable(32, "ebp", 0), ebp_0_constant)
quesoGraph:replace_operand(lqueso.variable(32, "esp", 0), esp_0_constant)


print('constant fold and propagate')
quesoGraph:constant_fold_propagate()

print('dead code elimination')
--quesoGraph:dead_code_elimination()

print('writing vIndex dot graph')
local fh = io.open('vIndex.dot', 'w')
fh:write(quesoGraph:dotGraphVIndex())
fh:close()

print('writing queso dot graph')
local fh = io.open('queso.dot', 'w')
fh:write(quesoGraph:dotGraph())
fh:close()

print("getting shadowGraph")
local shadowGraph = quesoGraph:shadowGraph2()

print("writing shadowGraph.dot")
local fh = io.open("shadowGraph.dot", "w")
fh:write(shadowGraph:dotGraph())
fh:close()

print('writing phiAssertions.smt2')
local fh = io.open('phiAssertions.smt2', 'w')
fh:write(phiAssertions(quesoGraph))
fh:close()

print('writing shadowDeclarations.smt2')
local fh = io.open('shadowDeclarations.smt2', 'w')
fh:write(shadowGraph:smtlib2Declarations())
fh:close()

print('writing shadow.smt2')
local fh = io.open('shadow.smt2', 'w')
fh:write(shadowGraph:smtlib2())
fh:close()

local smtlib2 = {}
table.insert(smtlib2, '(set-option :produce-models true)')
table.insert(smtlib2, '(set-logic QF_AUFBV)')
table.insert(smtlib2, '(set-info :smt-lib-version 2.0)')
table.insert(smtlib2, quesoGraph:smtlib2Declarations())
table.insert(smtlib2, shadowGraph:smtlib2Declarations())
table.insert(smtlib2, quesoGraph:smtlib2())
table.insert(smtlib2, phiAssertions(quesoGraph))
table.insert(smtlib2, shadowGraph:smtlib2())


table.insert(smtlib2, '(assert (= (select memory_0 #xbe000008) #x40))')
table.insert(smtlib2, '(assert (= (select memory_0 #xbe000009) #x40))')
table.insert(smtlib2, '(assert (= (select memory_0 #xbe00000a) #x40))')
table.insert(smtlib2, '(assert (= (select memory_0 #xbe00000b) #x40))')

table.insert(smtlib2, '(assert (= (select memory_0 #x40404044) #x4c))')
table.insert(smtlib2, '(assert (= (select memory_0 #x40404045) #x40))')
table.insert(smtlib2, '(assert (= (select memory_0 #x40404046) #x40))')
table.insert(smtlib2, '(assert (= (select memory_0 #x40404047) #x40))')

table.insert(smtlib2, '(assert (= v196_0 #b1))')

table.insert(smtlib2, '(check-sat)')
table.insert(smtlib2, '(get-model)')

print('writing test.smt2')
local fh = io.open('test.smt2', 'w')
fh:write(table.concat(smtlib2, '\n'))
fh:close()


local smtlib2 = {}
table.insert(smtlib2, '(set-option :produce-models true)')
table.insert(smtlib2, '(set-logic QF_AUFBV)')
table.insert(smtlib2, '(set-info :smt-lib-version 2.0)')
table.insert(smtlib2, shadowGraph:smtlib2Declarations())
table.insert(smtlib2, shadowGraph:smtlib2())
table.insert(smtlib2, '(check-sat)')
table.insert(smtlib2, '(get-model)')

print('writing shadowTest.smt2')
local fh = io.open('shadowTest.smt2', 'w')
fh:write(table.concat(smtlib2, '\n'))
fh:close()

print('solving shadowTest.smt2')

local p = os.execute('z3 shadowTest.smt2 > /tmp/z3out')

fh = io.open('/tmp/z3out')
local text = fh:read('*a')
fh:close()

if string.find(text, 'unsat') then 
    error('z3 said unsat')
end

print('patching vIndex dotGraph')
local dotGraph = quesoGraph:dotGraphVIndex()
for identifier,value in string.gmatch(text, 'define.fun v([%a%d_]*)_0.-#[xb](%x*)') do

    if value == '1' then
        dotGraph = string.gsub(dotGraph,
            'label="' .. identifier .. '"',
            'label="' .. identifier .. '", fillcolor=orange, style=filled')
    end
end

fh = io.open('shadowVindex.dot', 'w')
fh:write(dotGraph)
fh:close()