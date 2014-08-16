OBJS = queso/*.o translators/*.o lua/*.o machine/*.o

CXXFLAGS = -g -Werror -Wall -std=c++11 -O2
LIBS = -ludis86 -llua5.1

all :
	make -C cfg
	make -C containers
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
	make -C cfg clean
	make -C containers clean
	make -C loader clean
	make -C lua clean
	make -C machine clean
	make -C queso clean
	make -C translators clean