.PHONY: test

all: frontend backend opt

backend:
	make -C back-end

frontend:
	make -C front-end

opt:
	make -C optim-pass
clean:
	rm -rf build/*

distclean: clean
	rm -rf bin/* lib/*

test:
	@forest ./test/crest/math/config.xml
	@forest ./test/crest/simple/config.xml
	@forest ./test/crest/uniform_test/config.xml
	@forest ./test/crest/function/config.xml
	@forest ./test/crest/concrete_return/config.xml
	@forest ./test/simple/array/config.xml
	@forest ./test/klee-examples/get_sign/config.xml
	@forest ./test/klee-examples/islower/config.xml
	@forest ./test/simple/forloop/config.xml
	@forest ./test/simple/float/config.xml
	@forest ./test/simple/floatint/config.xml
	@forest ./test/simple/struct/config.xml
	@forest ./test/simple/global/config.xml
	@forest ./test/simple/shift/config.xml
	@forest ./test/simple/wired_bool/config.xml
	@forest ./test/simple/array2d/config.xml
	@forest ./test/SNU-real-time/insertsort/config.xml
	@forest ./test/simple/array_struct/config.xml

