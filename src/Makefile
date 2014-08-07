OBJS = queso.o x86queso.o generic_instructions.o

CXXFLAGS = -g -Werror -Wall -std=c++11
INCLUDE = -ludis86 -llua5.1

all : lqueso

test_x86queso : $(OBJS) test_x86queso.cc
	$(CXX) -o test_x86queso test_x86queso.cc $(OBJS) $(CXXFLAGS) $(INCLUDE)

lqueso : $(OBJS)
	$(CXX) -shared -fPIC -o lqueso.so lua.cc $(OBJS) $(CXXFLAGS) $(INCLUDE)

%.o : %.cc %.h
	$(CXX) -fPIC -c -o $@ $< $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f test_x86queso
	rm -f lqueso.so