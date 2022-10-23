.DEFAULT_GOAL := generate
generate:
		rm -rf build/
		rm -rf libsmall.dylib
		clang -shared smallc.c -o libsmall.dylib -arch arm64
		idris2 -p linear Lib1.idr -o test
		./build/exec/test > temp
		echo >> temp
		echo >> temp
		cat temp