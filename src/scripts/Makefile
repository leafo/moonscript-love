
all: moonscript.lua.h boot.lua.h

%.lua.h: %.lua
	echo namespace love { > $@
	xxd -i $< >> $@
	echo } >> $@

