OBJS = queso/*.o translators/*.o lua/*.o machine/*.o

CXXFLAGS = -g -Werror -Wall -std=c++11 -O2
LIBS = -ludis86 -llua5.1

all :
	make -C queso
	make -C translators
	make -C lua
	make -C machine
	$(CXX) -shared -fPIC -o lqueso.so $(OBJS) $(LIBS) $(CXXFLAGS) -I./

%.o : %.cc %.h
	$(CXX) -fPIC -c -o $@ $< $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f lqueso.so
	make -C queso clean
	make -C translators clean
	make -C lua clean
	make -C machine clean