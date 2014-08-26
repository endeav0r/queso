OBJS = graph.o quesoGraph.o

CXXFLAGS = -g -Werror -Wall -std=c++11 -O2
INCLUDE = -I../

all : $(OBJS)

%.o : %.cc %.h
	$(CXX) -c -o $@ $< $(CXXFLAGS) $(INCLUDE)

clean :
	rm -f *.o