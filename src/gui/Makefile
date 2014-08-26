OBJS = gui.o widget.o guiButton.o quesoGui.o

CXXFLAGS = -g -Wall -std=c++11 -O2
INCLUDE = -I../ -I/usr/local/include/SDL2

all : $(OBJS)
	

%.o : %.cc %.h
	$(CXX) -c -o $@ $< $(CXXFLAGS) $(INCLUDE)

%.o : %.cc
	$(CXX) -c -o $@ $< $(CXXFLAGS) $(INCLUDE)

clean :
	rm -f *.o