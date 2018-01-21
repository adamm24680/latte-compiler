all: latc_x86

lib/runtime.o: lib/runtime.c
	gcc -m32 -c -o lib/runtime.o lib/runtime.c

grammar/AbsLatte.hs grammar/ErrM.hs grammar/LexLatte.x grammar/ParLatte.y grammar/PrintLatte.hs: grammar/Latte.cf
	cd grammar; bnfc --haskell --functor --ghc Latte.cf

grammar/ParLatte.hs: grammar/ParLatte.y
	happy -gca grammar/ParLatte.y

grammar/LexLatte.hs: grammar/LexLatte.x
	alex -g grammar/LexLatte.x

latc_x86: grammar/AbsLatte.hs grammar/ErrM.hs grammar/LexLatte.hs grammar/ParLatte.hs grammar/PrintLatte.hs src/* lib/runtime.o
	stack install
	mv ~/.local/bin/latc_x86 .
