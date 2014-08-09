require('lqueso')

tests = {
    {0x55},
    {0x31, 0xd2},
    {0x89, 0xe5},
    {0x8b, 0x45, 0x08},
    {0x56},
    {0x8b, 0x75, 0x0c},
    {0x53},
    {0x8d, 0x58, 0xff},
    {0x0f, 0xb6, 0x0c, 0x16},
    {0x88, 0x4c, 0x13, 0x01},
    {0x83, 0xc2, 0x01},
    {0x84, 0xc9},
    {0x75, 0xf1},
    {0x5b},
    {0x5e},
    {0x5d},
    {0xc3}
}

function map (f, t)
    result = {}
    for k,v in pairs(t) do
        result[k] = f(v)
    end
    return result
end

function printQueso (queso, depth)
    local padding = ''
    for d=0,depth do
        padding = padding .. ' '
    end
    
    print(padding .. queso:queso())

    local depth_instructions = queso:depth_instructions()
    if depth_instructions then
        map(function (i) printQueso(i, depth + 2) end, depth_instructions)
    end
end

for k,bytes in pairs(tests) do
    local bytes = table.concat(map(string.char, bytes))
    local instruction = lqueso.x86translate(bytes)
    printQueso(lqueso.x86translate(bytes), 0)
end