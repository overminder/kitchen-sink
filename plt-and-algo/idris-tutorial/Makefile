IDRIS ?= idris

all : Primitives.bin

%.bin : %.idr
	$(IDRIS) $^ -o $@

clean :
	rm -f *.ibc *.bin
