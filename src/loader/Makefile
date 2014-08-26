OBJS = loader.o elf32.o

CXXFLAGS = -g -Wall -Werror -std=c++11 -O2
INCLUDE = -I../

all : $(OBJS)

%.o : %.cc %.h
	$(CXX) -c -o $@ $< $(CXXFLAGS) $(INCLUDE)

clean :
	rm -f *.o