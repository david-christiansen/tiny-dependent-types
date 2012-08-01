FSC=fsharpc
FSLEX=fslex
FSYACC=fsyacc
FLAGS=-r FSharp.PowerPack.dll --utf8output
LIBFLAGS=--target:library

Toplevel.exe: Toplevel.fs AST.dll Lexical.dll Grammar.dll Result.dll Typechecker.dll getline.dll
	$(FSC) $(FLAGS) -r Lexical.dll -r Grammar.dll -r AST.dll -r Result.dll -r Typechecker.dll -r getline.dll Toplevel.fs

getline.dll: getline.cs
	gmcs -target:library getline.cs

Nat.dll: Nat.fs
	$(FSC) $(LIBFLAGS) $(FLAGS) Nat.fs

AST.dll: AST.fs Nat.dll
	$(FSC) $(LIBFLAGS) $(FLAGS) -r Nat.dll AST.fs

Lexical.fs: Lexical.fsl Grammar.dll
	$(FSLEX) --unicode Lexical.fsl

Lexical.dll: Lexical.fs Grammar.dll
	$(FSC) $(LIBFLAGS) $(FLAGS) -r Grammar.dll Lexical.fs

Grammar.fs: Grammar.fsy
	$(FSYACC) --module Grammar Grammar.fsy

Grammar.dll: Grammar.fs AST.dll
	$(FSC) $(LIBFLAGS) $(FLAGS) -r AST.dll Grammar.fs

Result.dll: Result.fs
	$(FSC) $(LIBFLAGS) $(FLAGS) Result.fs

Typechecker.dll : Typechecker.fs AST.dll Result.dll
	$(FSC) $(LIBFLAGS) $(FLAGS) -r AST.dll -r Result.dll Typechecker.fs

clean:
	rm *.dll
	rm *.exe
	rm Grammar.fs
	rm Lexical.fs
