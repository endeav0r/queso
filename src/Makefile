OBJS = queso.o x86queso.o generic_instructions.o

CXXFLAGS = -g -Werror -Wall -std=c++11
INCLUDE = -ludis86

all : test_x86queso

test_x86queso : $(OBJS) test_x86queso.cc
	$(CXX) -o test_x86queso test_x86queso.cc $(OBJS) $(CXXFLAGS) $(INCLUDE)

%.o : %.cc %.h
	$(CXX) -c -o $@ $< $(CXXFLAGS)

clean :
	rm -f *.o
	rm test_x86queso