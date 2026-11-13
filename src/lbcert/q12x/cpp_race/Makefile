# xgen: exact certified tree generator (HiGHS C++ API + GMP).  HIGHS=prefix, GMP=prefix.
HIGHS ?= $(CURDIR)/../../gen/cpp/highs
GMP ?= /opt/homebrew/opt/gmp
CXX ?= c++
CXXFLAGS ?= -O2 -std=c++17
UNAME := $(shell uname)
ifeq ($(UNAME),Darwin)
  RPATH = -Wl,-rpath,$(HIGHS)/lib
else
  RPATH = -Wl,-rpath,$(HIGHS)/lib -pthread
endif

xgen: xgen.cpp engine.cpp builder.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include xgen.cpp -o xgen $(RPATH) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp

# same sources under a second name, so a rebuild never replaces the binary of running jobs
xgen_ws: xgen.cpp engine.cpp builder.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include xgen.cpp -o xgen_ws $(RPATH) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp

# work stealing / deadline hand-off build (same sources; the new options are off by default)
xgen_st: xgen.cpp engine.cpp builder.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include xgen.cpp -o xgen_st $(RPATH) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp

clean:
	rm -f xgen xgen_ws xgen_st xgen_x xgen_fast

# extended-domain build (pyramid levels from the model, e.g. m12r_x with PLV = 21); same sources
xgen_x: xgen.cpp engine.cpp builder.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include xgen.cpp -o xgen_x $(RPATH) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp

# cpp_fast: bound-ordered and lookahead-partial scans (same trees as xgen_x; new name)
xgen_fast: xgen.cpp engine.cpp builder.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include xgen.cpp -o xgen_fast $(RPATH) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp

# per-box policy racing (--race-stall, --race-cap; XG_CACHE): fast sources plus patch_race.py
xgen_race: xgen.cpp engine.cpp builder.inc
	$(CXX) $(CXXFLAGS) -I$(HIGHS)/include/highs -I$(HIGHS)/include -I$(GMP)/include xgen.cpp -o xgen_race $(RPATH) -L$(HIGHS)/lib -L$(GMP)/lib -lhighs -lgmpxx -lgmp
