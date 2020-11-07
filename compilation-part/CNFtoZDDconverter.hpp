#ifndef CNF_TO_ZDD_H
#define CNF_TO_ZDD_H

#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <string>
#include "cudd-release/cudd/cudd.h"
#include "cudd-release/cplusplus/cuddObj.hh"
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
#include "qdimacs-reader/QCnfFormula.hpp"
#include "qdimacs-reader/QDimacsReader.hpp"
#include "qdimacs-reader/CnfFormula.hpp"

//CNFtoZDDconverter class

class CNFtoZDDconverter {
	
public:
	//constructors
	CNFtoZDDconverter();

	//helper functions
	ZDD CLtoZDD(const CnfClause& cl, Cudd mgr, int maxvar); 
	int indexConverter(int g);
	int maxVarRange(const QCnfFormula& qcnf);	
	std::map<int, int> produce_indices_map(int maxvar);
	
	
	//main converter
	void convertCNFtoZDD(const std::string& path);
	
	//draw ZDD
	void ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames);
	
};


#endif // CNF_TO_ZDD_H








