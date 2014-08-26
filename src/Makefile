OBJS = queso/*.o translators/*.o machine/*.o \
       disassembler/*.o graph/*.o containers/*.o loader/*.o
LUA_OBJS = lua/*.o
GUI_OBJS = gui/*.o

CXXFLAGS = -g -Werror -Wall -std=c++11 -O2
LIBS = -ludis86 -llua -L/usr/local/lib

all :
	make -C containers
	make -C disassembler
	make -C graph
	make -C gui
	make -C loader
	make -C lua
	make -C machine
	make -C queso
	make -C translators
	#$(CXX) -shared -fPIC -o lqueso.so $(OBJS) $(LIBS) $(CXXFLAGS) -I./
	$(CXX) -o quesoGui $(OBJS) $(GUI_OBJS) $(LIBS) -lSDL2main -lSDL2 -lSDL2_ttf

%.o : %.cc %.h
	$(CXX) -fpic -c -o $@ $< $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f quesoGui
	rm -f lqueso.so
	make -C containers clean
	make -C disassembler clean
	make -C graph clean
	make -C gui clean
	make -C loader clean
	make -C lua clean
	make -C machine clean
	make -C queso clean
	make -C translators clean
