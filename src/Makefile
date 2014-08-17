OBJS = queso/*.o translators/*.o lua/*.o machine/*.o \
       disassembler/*.o graph/*.o containers/*.o

CXXFLAGS = -g -Werror -Wall -std=c++11 -O2
LIBS = -ludis86 -llua5.1

all :
	make -C containers
	make -C disassembler
	make -C graph
	make -C loader
	make -C lua
	make -C machine
	make -C queso
	make -C translators
	$(CXX) -shared -fPIC -o lqueso.so $(OBJS) $(LIBS) $(CXXFLAGS) -I./

%.o : %.cc %.h
	$(CXX) -fPIC -c -o $@ $< $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f lqueso.so
	make -C containers clean
	make -C disassembler clean
	make -C graph clean
	make -C loader clean
	make -C lua clean
	make -C machine clean
	make -C queso clean
	make -C translators clean