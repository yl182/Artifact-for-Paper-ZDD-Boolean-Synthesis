main:
	

	g++ -std=c++11 -g -c CNFtoZDDconverter.cpp -I qdimacs-reader -I cudd-release/cudd -I cudd-release/cplusplus

	g++ -std=c++11 -g -c cudd0.cpp -I cudd-release/cudd -I cudd-release/cplusplus -I qdimacs-reader

	g++ -std=c++11 -g cudd0.o CNFtoZDDconverter.o qdimacs-reader/CnfFormula.o qdimacs-reader/QCnfFormula.o qdimacs-reader/QDimacsReader.o -I cudd-release -I cudd-release/cplusplus -I cudd-release/cudd -I cudd-release/util -I cudd-release/st -I cudd-release/mtr -I cudd-release/epd -I qdimacs-reader -I QMRes -I cudd-release/cplusplus -lobj -lcudd -L cudd-release/cplusplus/.libs -L cudd-release/cudd -o cudd0


	
	#./cudd0 <argument>
	
	#bash dot2png.sh
	

clean:
	rm -f *.dot
	rm -f *.png
	rm -f cudd0
	rm -f CNFtoZDDconverter
	rm -f *.o
	rm -f *.pdf

saved:
	g++  -g cudd0.cpp qdimacs-reader/QDimacsReader.cpp CNFtoZDDconverter.cpp qdimacs-reader/QCnfFormula.cpp qdimacs-reader/CnfFormula.cpp QMRes/manip.c cudd-release/cplusplus/cuddObj.cc cudd-release/cudd/cuddZddGroup.c cudd-release/cudd/cuddAPI.c -I cudd-release -I cudd-release/cplusplus -I cudd-release/cudd -I cudd-release/util -I cudd-release/st -I cudd-release/mtr -I cudd-release/epd -I qdimacs-reader -I QMRes -I cudd-release/cplusplus -lcudd -L cudd-release/cudd -L qdimacs-reader -o cudd0

	gcc -g -c QMRes/manip.c -I cudd-release/cudd -I cudd-release/epd -I QMRes -I cudd-release/util -I cudd-release -I cudd-release/st -I cudd-release/mtr 
	./cudd0
	dot ZDD.dot -Tpng -o ZDD.png

	#dot try1ZDD.dot -Tpng -o try1ZDD.png
	#dot try2ZDD.dot -Tpng -o try2ZDD.png
	#dot try3ZDD.dot -Tpng -o try3ZDD.png

	
