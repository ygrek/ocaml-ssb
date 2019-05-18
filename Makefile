.SUFFIXES:
.PHONY: build clean

build:
	dune build ssb.exe

clean:
	dune clean
