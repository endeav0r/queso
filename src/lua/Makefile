OBJS = lua.o luint64.o

CXXFLAGS = -g -Wall -std=c++11 -O2
INCLUDE = -I../

all : $(OBJS)
	

%.o : %.cc %.h
	$(CXX) -c -o $@ $< $(CXXFLAGS) $(INCLUDE) -DCYGWIN

clean :
	rm -f *.o