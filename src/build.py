#!/usr/bin/python

import subprocess
import sys
import thread
import os

COMPILER = 'g++'
#INCLUDE = '-I./ -I/usr/local/include/SDL2 -I/usr/local/include/ -I/usr/include/lua5.2'
INCLUDE = '-I./ -I/usr/local/include/ -I/usr/include/lua5.2'
FLAGS = '-O2 -std=c++11 -g -pg'
#LIB = '-ludis86 -L/usr/local/lib -lSDL2main -lSDL2 -lSDL2_ttf'
LIB = '-ludis86 -L/usr/local/lib'
CYGWIN = '-lcygwin -mwindows'
LINUX = '-llua -ljansson'

sourceFiles = []


def executeCommand (command) :
    return subprocess.Popen(command, shell=True).wait()

def addSourceFile (fileNameBase) :
    global sourceFiles

    sourceFiles.append({'source': fileNameBase + '.cc',
                        'obj': fileNameBase + '.o' })

def build (flags) :

    for sourceFile in sourceFiles :

        if os.path.exists(sourceFile['obj']) and \
           os.path.getmtime(sourceFile['source']) < os.path.getmtime(sourceFile['obj']) :
            print 'skip', sourceFile['source']
            continue

        cmd = ' '.join([COMPILER, \
                        '-c -fPIC -o', \
                        sourceFile['obj'], \
                        sourceFile['source'], \
                        INCLUDE, \
                        FLAGS\
                       ])
        print cmd
        if (executeCommand(cmd)) :
            return

    # build quesoGui
    '''
    cmd = ' '.join([COMPILER, \
                    '-o quesoGui', \
                    ' '.join(map(lambda x: x['obj'], sourceFiles)), \
                    LIB, \
                    ])
    if 'linux' not in flags :
        cmd += ' ' + CYGWIN
    else :
        cmd += ' ' + LINUX
    print cmd
    executeCommand(cmd)
    '''

    # build lqueso.so
    cmd = ' '.join([COMPILER, \
                    '-fPIC -shared -o lqueso.so', \
                    ' '.join(map(lambda x: x['obj'], sourceFiles)), \
                    LIB, \
                   ])
    if 'linux' in flags :
        cmd += ' ' + LINUX
    else :
        cmd += ' ' + CYGWIN
    print cmd
    executeCommand(cmd)

def clean () :
    unlinkFiles = map(lambda x: x['obj'], sourceFiles)
    unlinkFiles.append('lqueso.so')
    unlinkFiles.append('quesoGui')
    for unlinkFile in unlinkFiles :
        try :
            os.unlink(unlinkFile)
            print 'delete', unlinkFile
        except :
            pass
    
addSourceFile('containers/memoryModel')
addSourceFile('disassembler/x86Disassembler')
addSourceFile('graph/graph')
addSourceFile('graph/quesoGraph')
#addSourceFile('gui/gui')
#addSourceFile('gui/guiButton')
#addSourceFile('gui/widget')
#addSourceFile('gui/quesoGui')
#addSourceFile('gui/guiGraph')
addSourceFile('loader/elf32')
addSourceFile('loader/loader')
addSourceFile('lua/lua')
addSourceFile('lua/luint64')
addSourceFile('machine/machine')
addSourceFile('queso/generic_instructions')
addSourceFile('queso/queso')
addSourceFile('queso/spicyQueso')
addSourceFile('translators/x86queso')

if len(sys.argv) == 1 :
    build([])
elif sys.argv[1] == 'clean' :
    clean()
elif sys.argv[1] == 'build' :
    build(sys.argv[2:])
