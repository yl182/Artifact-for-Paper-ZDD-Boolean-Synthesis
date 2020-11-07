main:
	g++  cudd0.cpp qdimacs-reader/QDimacsReader.cpp CNFtoZDDconverter.cpp qdimacs-reader/QCnfFormula.cpp qdimacs-reader/CnfFormula.cpp -I cudd-release -I cudd-release/cplusplus -I cudd-release/cudd -I cudd-release/st -I cudd-release/mtr -I cudd-release/epd -I qdimacs-reader  -lcudd -L cudd-release/cudd -L qdimacs-reader -o cudd0
	./cudd0
	dot ZDD.dot -Tpng -o ZDD.png

clean:
	rm -f *.dot
	rm -f *.png
	rm -f cudd0
	rm -f CNFtoZDDconverter
	
