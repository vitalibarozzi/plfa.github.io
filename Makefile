agda := $(wildcard src/*.lagda)
agdai := $(wildcard src/*.agdai)
markdown := $(subst src/,out/,$(subst .lagda,.md,$(agda)))

default: $(markdown)

out/:
	mkdir out

out/%.md: src/%.lagda out/
	agda2html --link-to-agda-stdlib --link-local -i $< -o $@

.phony: clean

clean:
ifneq ($(strip $(agdai)),)
	rm $(agdai)
endif

.phony: clobber

clobber: clean
ifneq ($(strip $(markdown)),)
	rm $(markdown)
endif
	rmdir out/
