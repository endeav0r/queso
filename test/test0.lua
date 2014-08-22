require('lqueso')

local test0 = lqueso.elf32('test0')

local symbols = test0:symbols()

local memoryModel = test0:memoryModel()
local graph = lqueso.x86disassemble(test0:entry(), memoryModel)
local dotGraph = graph:dotGraph()
--print(dotGraph)