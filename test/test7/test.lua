local lbaptrace = require('lbapTrace')
local lqueso    = require('lqueso')

local crash_0 = lbaptrace.open('crash_0.bpt')

local quesoGraph = lqueso.quesoGraph()

--print('-------------------------------')
--print('- some bap trace instructions -')
--print('-------------------------------')

local i = 1
while crash_0:end_of_trace() == false do
    local frame = crash_0:get_frame()

    if frame.type == 'std_frame' then
        local instruction = lqueso.x86translate(frame.rawbytes, luint64.luint64(frame.address))

--        print(i, instruction:queso())

        quesoGraph:absorbInstruction(instruction, i)
        if i ~= 1 then
            quesoGraph:addEdge(i - 1, i)
        end

        i = i + 1
    end
end

function printQueso (instruction, depth)
    local spaces = ''
    for i=1,depth do
        spaces = spaces .. ' '
    end
    print(spaces .. instruction:queso())
    for k,depth_instruction in pairs(instruction:depth_instructions()) do
        printQueso(depth_instruction, depth + 2)
    end
end

quesoGraph:blockize()
quesoGraph:ssa()
--quesoGraph:constant_fold_propagate()
--quesoGraph:dead_code_elimination()

print()
print('---------------------------------')
print('- equivalent queso instructions -')
print('---------------------------------')

printQueso(quesoGraph:g_vertices()[1], 0)
