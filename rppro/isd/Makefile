#CXX := g++ -std=c++0x #11
CXX := /tools/local/gcc-4.7.2/bin/g++-4.7.2 -std=c++11

BLD_DIR := ../../build/isd

INCLUDES := -I../../../cgem/install/include

LDFLAGS := -L../../../cgem/install/lib

SRC := format.cpp instruction.cpp isd.cpp

all:
	$(CXX) $(INCLUDES) $(LDFLAGS) $(SRC) -lxgem -o $(BLD_DIR)/isd

.PHONY: all
