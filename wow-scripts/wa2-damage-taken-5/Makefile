CPP := cpp

ALL := shall-trigger.lua.gen

all : $(ALL)

clean :
	rm -f $(ALL)

%.lua.gen : %.lua queue.lua
	$(CPP) $< -P -o $@
