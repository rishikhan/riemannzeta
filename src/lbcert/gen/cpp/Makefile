# Builds libengine (ctypes) against the HiGHS installed under ./highs (or HIGHS=prefix).
HIGHS ?= $(CURDIR)/highs
CXX ?= c++
CXXFLAGS ?= -O2 -std=c++17 -fPIC
UNAME := $(shell uname)
ifeq ($(UNAME),Darwin)
  SO = libengine.dylib
  LDFLAGS = -dynamiclib -Wl,-rpath,$(HIGHS)/lib
else
  SO = libengine.so
  LDFLAGS = -shared -Wl,-rpath,$(HIGHS)/lib -pthread
endif

$(SO): engine.cpp
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include engine.cpp -o $(SO) $(LDFLAGS) -L$(HIGHS)/lib -lhighs

clean:
	rm -f $(SO)
