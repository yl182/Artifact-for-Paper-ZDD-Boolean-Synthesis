main:

	g++ -std=c++11 -g -c CNFtoZDDconverter.cpp -I qdimacs-reader -I cudd-release/cudd -I cudd-release/cplusplus

	g++ -std=c++11 -g -c cudd0.cpp -I cudd-release/cudd -I cudd-release/cplusplus -I qdimacs-reader

	g++ -std=c++11 -g cudd0.o CNFtoZDDconverter.o qdimacs-reader/CnfFormula.o qdimacs-reader/QCnfFormula.o qdimacs-reader/QDimacsReader.o -I cudd-release -I cudd-release/cplusplus -I cudd-release/cudd -I cudd-release/util -I cudd-release/st -I cudd-release/mtr -I cudd-release/epd -I qdimacs-reader -I QMRes -I cudd-release/cplusplus -lobj -lcudd -L cudd-release/cplusplus/.libs -L cudd-release/cudd -o cudd0


	
sampleScriptForSeriesOfExecution:
	bash dot2png.sh
	

clean:
	rm -f *.dot
	rm -f *.png
	rm -f cudd0
	rm -f CNFtoZDDconverter
	rm -f *.o
	rm -f *.pdf

sampleExecutionScript:
	./cudd0 <argument> <Flag to enable outputting ZDDs as dot files> <Flag to enable writing out all details>
sampleToConvertZDDToFigureScript:
	dot <ZDD.dot> -Tpng -o <ZDD.png>
	dot <ZDD.dot> -Tpdf -o <ZDD.pdf>
