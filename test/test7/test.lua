local lbaptrace = require('lbapTrace')
local lqueso    = require('lqueso')

--print('-------------------------------')
--print('- some bap trace instructions -')
--print('-------------------------------')


local log_lines = {}
function log (line)
    print(line)
    table.insert(log_lines, line)
end


function write_log ()
    fh = io.open('log', 'w')
    fh:write(table.concat(log_lines, '\n'))
    fh:close()
end


function forZ3 (quesoGraph, declarations, assertions, values)--, declarations, assertions, values)
    local smtlib2Header = "(set-option :produce-models true)\n"
    smtlib2Header = smtlib2Header .. "(set-logic QF_AUFBV)\n"
    smtlib2Header = smtlib2Header .. "(set-info :smt-lib-version 2.0)\n"

    local smtlib2 = smtlib2Header .. 
                    quesoGraph:smtlib2Declarations() .. '\n' ..
                    quesoGraph:smtlib2() .. '\n' ..
                    table.concat(declarations, '\n') .. '\n' ..
                    table.concat(assertions, '\n') .. '\n' ..
                    '(check-sat)' .. '\n' ..
                    '(get-value ('.. table.concat(values, ' ') .. '))'
    return smtlib2
end


function z3Solve (smtlib2)
    local fh = io.open('/tmp/queso.smt2', 'w')
    fh:write(smtlib2)
    fh:close()

    local p = io.popen('z3 /tmp/queso.smt2')

    local text = p:read('*a')

    print(text)

    local result = {}
    for identifier,value in string.gmatch(text, '([%a%d_]*) #[xb](%x*)') do
        result[identifier] = tonumber(value, 16)
    end

    return result
end


function countInstructions (quesoGraph)
    local instruction_count = 0
    for k,instruction in pairs(quesoGraph:g_vertices()) do
        instruction_count = instruction_count + #instruction:flatten()
    end
    return instruction_count
end


function operand_needle (name)
    if     name == 'R_EAX' then return lqueso.variable(32, 'eax')
    elseif name == 'R_EAX_32' then return lqueso.variable(32, 'eax')
    elseif name == 'R_EBX' then return lqueso.variable(32, 'ebx')
    elseif name == 'R_EBX_32' then return lqueso.variable(32, 'ebx')
    elseif name == 'R_ECX' then return lqueso.variable(32, 'ecx')
    elseif name == 'R_ECX_32' then return lqueso.variable(32, 'ecx')
    elseif name == 'R_EDX' then return lqueso.variable(32, 'edx')
    elseif name == 'R_EDX_32' then return lqueso.variable(32, 'edx')
    elseif name == 'R_EDI' then return lqueso.variable(32, 'edi')
    elseif name == 'R_EDI_32' then return lqueso.variable(32, 'edi')
    elseif name == 'R_ESI' then return lqueso.variable(32, 'esi')
    elseif name == 'R_ESI_32' then return lqueso.variable(32, 'esi')
    elseif name == 'R_ESP' then return lqueso.variable(32, 'esp')
    elseif name == 'R_ESP_32' then return lqueso.variable(32, 'esp')
    elseif name == 'R_EBP' then return lqueso.variable(32, 'ebp')
    elseif name == 'R_EBP_32' then return lqueso.variable(32, 'ebp')
    elseif name == 'R_EIP' then return lqueso.variable(32, 'eip')
    else
        return nil
    end
end


function replaceOperand (instruction, needle, operand)
    local result = false
    for k,instruction in pairs(instruction:flatten()) do
        if instruction:replace_operand(needle, operand) then
            result = true
        end
    end
    return result
end


function printQueso (instruction, depth, child)
    local lines = {}
    local spaces = ''
    for i=1,depth do
        spaces = spaces .. ' '
    end
    table.insert(lines, (spaces .. instruction:queso()))
    for k,depth_instruction in pairs(instruction:depth_instructions()) do
        for k,line in pairs(printQueso(depth_instruction, depth + 2, true)) do
            table.insert(lines, line)
        end
    end

    if child == true then
        return lines
    else
        return table.concat(lines, '\n')
    end
end

function parseBapTrace (traceFileName)
    local crash_0 = lbaptrace.open(traceFileName)

    local quesoGraph = lqueso.quesoGraph()

    local fileTaints = {}

    local i = 1
    local vars_replaced = 0
    while crash_0:end_of_trace() == false do
        local frame = crash_0:get_frame()

        if frame.type == 'std_frame' then

            local instruction = lqueso.x86translate(frame.rawbytes, luint64.luint64(frame.address))

            instruction:ssa()

            log('')
            log(instruction:queso())
            log(printQueso(instruction, 4))

            -- these are instructions where we set traced memory values
            -- these will be prepended before the current instruction in the graph
            local memoryInstructions = nil

            --print(i, instruction:queso())

            -- need to ensure we replace only once. important for things like
            -- test eax, eax
            local replaced = {}

            log(' operand_pre_list size=' .. #frame.operand_pre_list)
            for k,operand in pairs(frame.operand_pre_list) do

                local value = ''
                if operand.value_int ~= nil then
                    value = ', value=' .. lqueso.constant(operand.size, operand.value_int):queso()
                end

                log(' operand_pre_list taint=' .. tostring(operand.taint) .. 
                    ', read=' .. tostring(operand.read) .. 
                    ', type=' .. operand.type ..
                    ', name=' .. tostring(operand.name) ..
                    ', size=' .. operand.size .. value)

                if operand.read and -- we read this operand
                   operand.type == 'reg' and -- it's a register
                   operand.taint == nil and -- it's tainted
                   operand.value_int ~= nil and -- we have a tainted value to substitute
                   operand.name ~= 'EFLAGS' and -- fuck EFLAGS
                   operand.name ~= 'R_EFLAGS' then -- fuck EFLAGS
                    --print('not tainted', operand.name, string.format('%08x', operand.value_int))
                    local needle = operand_needle(operand.name)
                    if needle == nil then
                        error('unhandled operand_name for ' .. operand.name)
                    end

                    if replaced[needle:queso()] == nil then
                        log('  replacing ' .. needle:queso() .. ' with ' .. lqueso.constant(32, operand.value_int):queso())

                        local result = instruction:replace_operand(needle, lqueso.constant(32, operand.value_int))
                        replaced[needle:queso()] = true

                        if not result then
                            print('needle=' .. needle:queso(), lqueso.constant(32, operand.value_int):queso())
                            printQueso(instruction, 2)
                            error('replace failed')
                        end

                        -- we need to 

                        vars_replaced = vars_replaced + 1

                    end

                elseif operand.read and -- we read this operand
                       operand.type == 'mem' and -- going for the big $ now!
                       operand.taint == nil and
                       operand.size == 8 then -- just a 1 byte load

                    local store = lqueso.store(lqueso.array(8, 'memory', 32),
                                               lqueso.constant(32, operand.address),
                                               lqueso.constant(8, operand.value_int))

                    -- add this store to the graph
                    quesoGraph:absorbInstruction(store, i)
                    -- add an edge from the previous instruction to this one
                    if i ~= 1 then
                        quesoGraph:addEdge(i - 1, i)
                    end
                    i = i + 1
                end
            end

            log(' operand_post_list size=' .. #frame.operand_post_list)
            for k,operand in pairs(frame.operand_post_list) do
                local value = ''
                if operand.value_int ~= nil then
                    value = ', value=' .. lqueso.constant(32, operand.value_int):queso()
                end

                log(' operand_post_list taint=' .. tostring(operand.taint) .. 
                    ', read=' .. tostring(operand.read) .. 
                    ', type=' .. operand.type ..
                    ', name=' .. tostring(operand.name) .. value)
            end

            
            --printQueso(instruction, 2)

            quesoGraph:absorbInstruction(instruction, i)
            if i ~= 1 then
                quesoGraph:addEdge(i - 1, i)
            end

            i = i + 1
        elseif frame.type == 'taint_intro_frame' then
            for k,taint in pairs(frame.taint_intro_list) do
                table.insert(fileTaints, taint)
                log('taint ' ..
                    string.format('%08x', taint.address) .. ' ' ..
                    taint.source_name .. '+' .. string.format('0x%x', taint.offset) .. ' ' ..
                    string.format('%02x', string.byte(taint.value)))
            end
        end
    end

    log('vars concretized: ' .. tostring(vars_replaced))

    return quesoGraph, fileTaints
end

quesoGraph, fileTaints = parseBapTrace('t.bpt')

print('blockize')
quesoGraph:blockize()
print(countInstructions(quesoGraph), ' instructions')
print('ssa')
quesoGraph:ssa()
print('constant fold and propagate')
quesoGraph:constant_fold_propagate()
print('eliminate dead code')
--quesoGraph:dead_code_elimination()
print(countInstructions(quesoGraph), ' instructions')

print('write smt2')

--printQueso(quesoGraph:g_vertices()[1], 0)

local declarations = {}
local values = {}
local assertions = {}
local i = 0
for k,t in pairs(fileTaints) do
    --table.insert(values, '(select memory_0 #x' .. string.format('%08x', t.address) .. ')')

    table.insert(declarations, '(declare-fun in_' .. tostring(i) .. ' () (_ BitVec 8))')
    table.insert(assertions, '(assert (= in_' .. tostring(i) .. ' ' ..
                             '(select memory_0 #x' .. string.format('%08x', t.address) .. ')))')
    table.insert(values, 'in_' .. tostring(i))
    i = i + 1
end

table.insert(values, 'ZF_1 ZF_2')

table.insert(assertions, '(assert (= ZF_1 #b1))')
table.insert(assertions, '(assert (= ZF_2 #b1))')

local results = z3Solve(forZ3(quesoGraph, declarations, assertions, values))

local i = 0
for key,value in pairs(results) do
    print(key,value)
    i = i + 1
    if i > 16 then break end
end

print('write log')

write_log()