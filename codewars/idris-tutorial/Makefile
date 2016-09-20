IDRIS ?= idris

all : Primitives.bin

%.bin : %.idr
	$(IDRIS) $^ -o $@
