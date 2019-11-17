TARGETS=App.exe

GENERATE_DATA := python2 generate-data.py
CREATE_DEFAULT_ANSWERS := python2 create-default-answers.py

.PHONY: all build clean %.exe

all: build link

build:
	dune build app/App.exe

link: $(TARGETS)

%.exe:
	if [ ! -f $@ ]; then ln -s _build/default/app/$@ . ; fi

install:
	jbuilder install

clean:
	rm -rf _build *.install *.pdf $(TARGETS)

functionaltest: all

unittest:
	jbuilder runtest

test: unittest functionaltest

documentation:
	jbuilder build @docs

generate-data: all
	$(GENERATE_DATA) ./App.exe benchmarks

generate-outs: all
	$(CREATE_DEFAULT_ANSWERS) ./App.exe benchmarks
