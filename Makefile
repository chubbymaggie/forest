.PHONY: test


backend:
	make -C back-end

frontend:
	make -C front-end

opt:
	sudo cp optim-pass/optimization_pass.cpp /llvm-2.9/lib/Transforms/Hello/Hello.cpp
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make;
	cd /llvm-2.9/lib/Transforms/Hello/; sudo make install;
	
clean:
	rm -rf build/*

distclean: clean
	rm -rf bin/*

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

