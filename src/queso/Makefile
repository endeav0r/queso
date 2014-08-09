OBJS = queso.o generic_instructions.o

CXXFLAGS = -g -Werror -Wall -std=c++11 -O2
INCLUDE =

all : $(OBJS)

%.o : %.cc %.h
	$(CXX) -fPIC -c -o $@ $< $(CXXFLAGS)

clean :
	rm -f *.o