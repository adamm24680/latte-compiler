lib/runtime.o: lib/runtime.c
	gcc -m32 -c -o lib/runtime.o lib/runtime.s

grammar/AbsLatte.hs grammar/ErrM.hs grammar/LexLatte.x grammar/ParLatte.y grammar/PrintLatte.hs: grammar/Latte.cf
	bnfc --haskell Latte.cf


latc_x86: grammar/AbsLatte.hs grammar/ErrM.hs grammar/LexLatte.x grammar/ParLatte.y grammar/PrintLatte.hs src/* lib/runtime.o
	stack install
	mv ~/.local/bin/latc_x86 .

all: latc_x86
