require('lqueso')

local test0 = lqueso.elf32('test0')

local symbols = test0:symbols()
for name, symbol in pairs(symbols) do
    print(name, symbol)
end

local memoryModel = test0:memoryModel()
local graph = lqueso.x86disassemble(symbols['main']['address'], memoryModel)
local dotGraph = graph:dotGraph()

local fh = io.open('test0.dot', 'w')
fh:write(dotGraph)
fh:close()