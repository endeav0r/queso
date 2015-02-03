local lbaptrace = require('lbapTrace')
local lqueso    = require('lqueso')

-- number of times to perform concolic execution... ie this is
-- the path depth
LOOP_ITERATIONS = 16

-- set to maximum size for possible inputs
MAX_INPUT_SIZE = 256

-- set to name of input file
INPUT_FILENAME = 'input'

-- set this true to eliminate variables as memory addresses
-- all non-tainted memory addresses are given their runtime values
-- this will set tainted memory addresses to their runtime values
-- as well
-- NOT YET SUPPORTED
CONCRETIZE_MEMORY = true

-- by using the same seed, we introduce determinism which greatly
-- aids debuggin (when things are dependent upon random values, which
-- may not be the case in current code)
math.randomseed(1)

EFLAGS_CF = (1     )
EFLAGS_PF = (1 << 2)
EFLAGS_AF = (1 << 4)
EFLAGS_ZF = (1 << 6)
EFLAGS_SF = (1 << 7)
EFLAGS_DF = (1 << 10)
EFLAGS_OF = (1 << 11)


function map (f, t)
    local result = {}
    if type(t) == 'string' then
        for i=1,#t do
            result[i] = f(t:sub(i,i))
        end
    else
        for k,v in pairs(t) do
            result[k] = f(v)
        end
    end
    return result
end


function parse_eflags (eflags)
    local flags = {}
    flags.CF = (eflags & EFLAGS_CF) ~= 0
    flags.PF = (eflags & EFLAGS_PF) ~= 0
    flags.AF = (eflags & EFLAGS_AF) ~= 0
    flags.ZF = (eflags & EFLAGS_ZF) ~= 0
    flags.SF = (eflags & EFLAGS_SF) ~= 0
    flags.DF = (eflags & EFLAGS_DF) ~= 0
    flags.OF = (eflags & EFLAGS_OF) ~= 0
    return flags
end


local log_lines = {}
function log (line)
    --print(line)
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
                    quesoGraph:smtlib2() .. '\n'

    if declarations ~= nil then
        smtlib2 = smtlib2 .. table.concat(declarations, '\n') .. '\n'
    end

    if assertions ~= nil then
        smtlib2 = smtlib2 .. table.concat(assertions, '\n') .. '\n'
    end

    smtlib2 = smtlib2 .. '(check-sat)' .. '\n'

    if values ~= nil then
        smtlib2 = smtlib2 .. '(get-value ('.. table.concat(values, ' ') .. '))'
    end

    return smtlib2
end


function z3Solve (smtlib2)
    local fh = io.open('/tmp/queso.smt2', 'w')
    fh:write(smtlib2)
    fh:close()

    local p = os.execute('z3 /tmp/queso.smt2 > /tmp/z3out')

    fh = io.open('/tmp/z3out')
    local text = fh:read('*a')
    fh:close()

    if string.find(text, 'unsat') then return false end

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
    print('parseBapTrace')
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
            log(table.concat(map(function (x) return string.format('%02x', string.byte(x)) end, frame.rawbytes), ' '))
            log(instruction:queso())
            log(printQueso(instruction, 2))

            if CONCRETIZE_MEMORY then
                log('concretize memory')
                -- get all read/write tainted addresses from trace operands
                local reads = {}
                local writes = {}
                for k,operand in pairs(frame.operand_pre_list) do
                    if operand.type == 'mem' and operand.read then
                        --log('mem read, ' .. string.format('%08x', operand.address) .. ', ' .. tostring(operand.taint))
                        table.insert(reads, operand)
                    elseif operand.type == 'mem' then
                        --log('mem write, ' .. string.format('%08x', operand.address) .. ', ' .. tostring(operand.taint))
                        table.insert(writes, operand)
                    end
                end

                -- find the reads/writes, replace their address operands with
                -- constants
                -- as soon as we call replace_with_assign, subInstruction is invalid
                for k,subInstruction in pairs(instruction:flatten()) do
                    if subInstruction:opcode() == 'load' then
                        -- if this memory is not tainted, we assign its runtime value
                        local success = false
                        --log(subInstruction:queso() .. ' -- ' .. subInstruction:operand_written():queso())
                        if reads[1].taint == nil then
                            success = instruction:replace_with_assign(subInstruction:operand_written(), lqueso.constant(8, reads[1].value_int))
                        else
                            local memoryVariable = lqueso.variable(8, "memory_" .. string.format('%08x', reads[1].address))
                            success = instruction:replace_with_assign(subInstruction:operand_written(), memoryVariable)
                        end
                        --log('subInstruction:opcode() == load ' .. tostring(success))
                        table.remove(reads, 1)
                    elseif subInstruction:opcode() == 'store' then
                        -- if memory not tainted, assign runtime value
                        --if writes[1].taint == nil then
                        --    local memoryVariable = lqueso.variable(8, "memory_" .. string.format('%08x', writes[1].address))
                        --    local assign = lqueso.assign(memoryVariable, lqueso.constant(8, writes[1].value_int))
                        --    instruction:replace_with_instruction(subInstruction:operand_written(), assign)
                        --else
                        -- bap suchs, treat all writes as tainted, fuck
                            local memoryVariable = lqueso.variable(8, "memory_" .. string.format('%08x', writes[1].address))
                            local assign = lqueso.assign(memoryVariable, subInstruction:value())
                            instruction:replace_with_instruction(subInstruction:operand_written(), assign)
                        --end
                        table.remove(writes, 1)
                    end
                end
                --log(printQueso(instruction, 4))
            end

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
                       operand.taint == nil and -- not tainted
                       operand.size == 8 and -- just a 1 byte load
                       CONCRETIZE_MEMORY == false then -- we only do this if not concretizing memory

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

function traceInput (inputString)

    fh = io.open('input', 'wb')
    fh:write(inputString)
    fh:close()

    local p = os.execute('ssh user@192.168.1.53 rm /home/user/*trace.bpt')
    local p = os.execute('scp input user@192.168.1.53:~/')
    local trace_command = 'ssh user@192.168.1.53 ' ..
                          '/home/user/source/bap-0.8/pin/pin -t ' .. 
                          '/home/user/source/bap-0.8/pintraces/obj-ia32/gentrace.so ' ..
                          '-taint_indices -taint_files input -o trace.bpt ' ..
                          '-- /home/user/libpngfuzz input'
                          --'-- /home/user/android_libexif/fuzzlibexif input'
    print(trace_command)
    local p = os.execute(trace_command)

    local p = os.execute('ssh user@192.168.1.53 mv /home/user/*trace.bpt /home/user/trace.bpt')
    local p = os.execute('scp user@192.168.1.53:/home/user/trace.bpt .')
end


-- returns result, zfTree and path taken
function flipFlags ()
    quesoGraph, fileTaints = parseBapTrace('trace.bpt')

    quesoGraph:blockize()
    log(countInstructions(quesoGraph), ' instructions')
    quesoGraph:ssa()
    --quesoGraph:constant_fold_propagate()
    log(countInstructions(quesoGraph), ' instructions')

    local flags = {}
    -- collect ZF
    for k,instruction in pairs(quesoGraph:g_vertices()) do
        for k,instruction in pairs(instruction:flatten()) do
            for k,operand in pairs(instruction:operands_read()) do
                if operand:name() == 'ZF' then --or 
                   --operand:name() == 'SF' or
                   --operand:name() == 'CF' or
                   --operand:name() == 'OF' then
                    log('found flag ' .. operand:smtlib2())
                    table.insert(flags, {operand=operand})
                end
            end
        end
    end

    -- we are going to dedup flags
    local flags_dedup = {}
    local i = 1
    while i <= #flags do
        if flags_dedup[flags[i].operand:smtlib2()] == nil then
            flags_dedup[flags[i].operand:smtlib2()] = true
            i = i + 1
        else
            log('dedup flag ' .. flags[i].operand:smtlib2())
            table.remove(flags, i)
        end
    end

    log('flags found ' .. #flags)
    for k,v in pairs(flags) do
        log('flag=' .. v.operand:smtlib2())
    end

    -- we are going to run one time through SMTLIB2 with given inputs to solve
    -- for flag values
    local declarations = {}
    local assertions = {}
    local values = {}

    for k,taint in pairs(fileTaints) do
        table.insert(assertions, '(assert (= memory_' .. 
                                  string.format('%08x', taint.address) .. '_0 #x' ..
                                  string.format('%02x', string.byte(taint.value)) .. '))')
    end

    for k,flag in pairs(flags) do
        table.insert(values, flag.operand:smtlib2())
    end

    for k,v in pairs(assertions) do log(v) end
    for k,v in pairs(values) do log(v) end

    local result = z3Solve(forZ3(quesoGraph, {}, assertions, values))

    for k,v in pairs(result) do print(k,v) end

    -- set flags to their original value
    for k,flag in pairs(flags) do
        log(flag.operand:smtlib2() .. ' = ' .. result[flag.operand:smtlib2()])
        flags[k].value = result[flag.operand:smtlib2()]
    end

    local newInputs = {}

    local flippedFlags = {}

    for k,flag in pairs(flags) do
        local declarations = {}
        local values = {}
        local assertions = {}
        local i = 0

        local backSlice = quesoGraph:slice_backward_thin(flag.operand)
        backSlice:blockize()

        log('backSlice over ' .. flag.operand:smtlib2() .. ' ' ..
            #backSlice:g_vertices() .. ' instructions')
        for k, instruction in pairs(backSlice:g_vertices()) do
            log(printQueso(instruction, 1))
        end

        -- set up variables to solve for inputs
        for k,t in pairs(fileTaints) do
            table.insert(declarations, '(declare-fun in_' .. tostring(i) .. ' () (_ BitVec 8))')
            table.insert(assertions, '(assert (= in_' .. tostring(i) .. ' memory_' ..
                                     string.format('%08x', t.address) .. '_0))')
            table.insert(values, 'in_' .. tostring(i))
            i = i + 1
        end


        -- for every flag
        for k,f in pairs(flags) do
            -- if we have not yet flipped this flag, and this is the current
            -- flag in our loop
            -- we have to this because a flag may be encountered more than once,
            -- but we only want to flip it once
            if flippedFlags[f.operand:smtlib2()] == nil and
               (f.operand:smtlib2() == flag.operand:smtlib2()) then
                -- mark this flag as flipped
                flippedFlags[f.operand:smtlib2()] = true
                -- determine value as opposite of its runtime value
                local value = 0
                if f.value == 0 then value = 1 end
                log('solving for ' .. f.operand:smtlib2() .. ' == ' .. value)
                table.insert(assertions, '(assert (= ' .. f.operand:smtlib2() .. ' #b' .. value .. '))')
                table.insert(values, f.operand:smtlib2())
            -- if this is not the current flag, set to regular
            -- runtime value
            else
                table.insert(assertions, '(assert (= ' .. f.operand:smtlib2() .. ' #b' .. f.value .. '))')
                table.insert(values, f.operand:smtlib2())
            end
        end

        -- the direction flag will be execution dependent, but we'll set it to 0
        -- to begin. works with current target
        table.insert(assertions, '(assert (= DF_0 #b0))')

        table.insert(newInputs, z3Solve(forZ3(quesoGraph, declarations, assertions, values)))
    end

    return newInputs
end


fh = io.open(INPUT_FILENAME, 'rb')
local inputs = {fh:read()}
fh:close()
local inputs_dedup = {}
for k,input in pairs(inputs) do
    inputs_dedup[input] = true
end

local output_i = 0

local loopi = 0
while loopi < LOOP_ITERATIONS do
    local newInputs = {}
    -- loop through all of our pending inputs
    for k,input in pairs(inputs) do
        traceInput(input)
        for k,newInput in pairs(flipFlags()) do
            table.insert(newInputs, newInput)
        end
    end

    log('newInputs pre undup ' .. #newInputs)
    inputs = {}
    -- for each new input
    for k,newInput in pairs(newInputs) do
        -- skip unsat new inputs
        if newInput ~= false then
            -- nextInput will be a table of ints where each int is a byte of input
            local nextInput = {}
            for i=0,256 do
                if newInput['in_' .. i] == nil then break end
                table.insert(nextInput, newInput['in_' .. i])
            end
            --print(table.concat(map(function (x) return string.format('%02x', x) end, nextInput), ''))
            table.insert(inputs, table.concat(map(function (x) return string.char(x) end, nextInput)))
        end
    end

    table.sort(inputs)
    -- dedup input
    local i = 1
    while i < #inputs do
        if inputs_dedup[inputs[i] ] == true then
            table.remove(inputs, i)
        else
            inputs_dedup[inputs[i] ] = true
            i = i + 1
        end
    end

    log('inputs post-undup ' .. #inputs)

    -- write out all of the new outputs
    for k,input in pairs(inputs) do
        fh = io.open('outputs/out_' .. output_i, 'wb')
        fh:write(input)
        fh:close()
        output_i = output_i + 1
    end

    loopi = loopi + 1
end


--traceInput('AAAAAAAAAAAAAAAAAAAAAAAAAAAA')k
--local results = flipZF()

--for k,v in pairs(results) do
--    print(k,v)
--end

--[[

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

]]--

print('write log')

write_log()