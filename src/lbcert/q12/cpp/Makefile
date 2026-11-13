# Builds libengine (ctypes) against HiGHS (HIGHS=prefix) and GMP (GMP=prefix, default system).
HIGHS ?= $(CURDIR)/highs
GMP ?= /usr
CXX ?= c++
CXXFLAGS ?= -O2 -std=c++17 -fPIC
UNAME := $(shell uname)
ifeq ($(UNAME),Darwin)
  SO = libengine.dylib
  LDFLAGS = -dynamiclib -Wl,-rpath,$(HIGHS)/lib -Wl,-rpath,$(GMP)/lib
else
  SO = libengine.so
  LDFLAGS = -shared -Wl,-rpath,$(HIGHS)/lib -pthread
endif

$(SO): engine.cpp builder.inc replay.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include engine.cpp -o $(SO) $(LDFLAGS) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp

clean:
	rm -f $(SO)
