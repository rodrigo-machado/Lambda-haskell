all: Main.lhs
	ghc --make -x lhs Main.lhs && ./Main
	

doc: Main.lhs
	cp Main.lhs Main.tex
	xelatex Main.tex 
	xelatex Main.tex

	
clean: 
	rm Main.aux Main.hi Main.log Main.o Main.tex
