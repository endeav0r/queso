#!/usr/bin/python2

import subprocess
import sys
import thread
import os

COMPILER = 'g++'
INCLUDE = '-I./ -I/usr/local/include/SDL2 -I/usr/local/include/ -lSDL2main'
FLAGS = '-O2 -std=c++11 -DCYGWIN'
LIB = '-llua -ludis86 -L/usr/local/lib -lcygwin -lSDL2main -lSDL2 -lSDL2_ttf'

sourceFiles = []


def executeCommand (command) :
    return subprocess.Popen(command, shell=True).wait()

def addSourceFile (fileNameBase) :
    global sourceFiles

    sourceFiles.append({'source': fileNameBase + '.cc',
                        'obj': fileNameBase + '.o' })

def build (flags) :

    for sourceFile in sourceFiles :

        if os.path.exists(sourceFile['obj']) :
            print 'skip', sourceFile['source']
            continue

        cmd = ' '.join([COMPILER, \
                        '-c -o', \
                        sourceFile['obj'], \
                        sourceFile['source'], \
                        INCLUDE, \
                        FLAGS\
                       ])
        print cmd
        if (executeCommand(cmd)) :
            return

    cmd = ' '.join([COMPILER, \
                    '-o quesoGui', \
                    ' '.join(map(lambda x: x['obj'], sourceFiles)), \
                    LIB, \
                    ])
    print cmd
    executeCommand(cmd)

def clean () :
    for sourceFile in sourceFiles :
        print 'delete', sourceFile['obj']
        os.unlink(sourceFile['obj'])


addSourceFile('containers/memoryModel')
addSourceFile('disassembler/x86Disassembler')
addSourceFile('graph/graph')
addSourceFile('graph/quesoGraph')
addSourceFile('gui/gui')
addSourceFile('gui/guiButton')
addSourceFile('gui/widget')
addSourceFile('gui/quesoGui')
addSourceFile('loader/elf32')
addSourceFile('loader/loader')
addSourceFile('lua/lua')
addSourceFile('lua/luint64')
addSourceFile('machine/machine')
addSourceFile('queso/queso')
addSourceFile('queso/generic_instructions')
addSourceFile('translators/x86queso')

if len(sys.argv) == 1 :
    build([])
elif sys.argv[1] == 'clean' :
    clean()
elif sys.argv[1] == 'build' :
    build(argv[2:])