lqueso = require('lqueso')

function pcToVIndex (pc, quesoGraph)
    for k, instruction in pairs(quesoGraph:g_vertices()) do
        print(pc, instruction:g_pc())
        if pc == instruction:g_pc() then
            return instruction:g_vIndex()
        end
    end
end


function createAssertion (variableName, variableSsa, value)
    return "(assert (= "
           .. variableName
           .. "_"
           .. tostring(variableSsa)
           .. " "
           .. value
           .. "))"
end


function solver (quesoGraph, assertions, values)
    local smtlib2Header = "(set-option :produce-models true)\n"
    smtlib2Header = smtlib2Header .. "(set-logic QF_AUFBV)\n"
    smtlib2Header = smtlib2Header .. "(set-info :smt-lib-version 2.0)\n"

    local smtlib2 = quesoGraph:smtlib2Declarations() .. quesoGraph:smtlib2()

    local daFile = smtlib2Header .. smtlib2
    daFile = daFile .. table.concat(assertions, '\n') .. '\n'
    daFile = daFile .. "(check-sat)\n"
    daFile = daFile .. "(get-value (" .. table.concat(values, " ") .. "))"

    local fh = io.open('/tmp/smtlib2.smt2', 'w')
    fh:write(daFile)
    fh:close()
end


-- load test file
local test0 = lqueso.elf32('test0')

-- get the address of main function
local mainAddress = test0:symbols()['main']['address']

-- disassemble main function to a quesoGraph
local quesoGraph = lqueso.x86disassemble(mainAddress, test0:memoryModel())

-- get the index of the graph vertex for entry to main function
local vIndex = pcToVIndex(mainAddress, quesoGraph)

-- apply ssa to the graph
quesoGraph:ssa(vIndex)

-- create a dot of the graph
local fh = io.open('test0.dot', 'w')
fh:write(quesoGraph:dotGraph())
fh:close()

-- solve for eip_34 = 8048346 where eip_0 = 8048320
solver(quesoGraph,
       {
        createAssertion('eip', 33, '#x08048346'),
        createAssertion('eip', 0,  '#x08048320')
       },
       {'loaded_24', 'loaded_23', 'loaded_22'})