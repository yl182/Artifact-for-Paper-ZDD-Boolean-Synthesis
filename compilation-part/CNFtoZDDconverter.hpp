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
#include <unordered_map>
#include <stdexcept>
#include "qdimacs-reader/QCnfFormula.hpp"
#include "qdimacs-reader/QDimacsReader.hpp"
#include "qdimacs-reader/CnfFormula.hpp"

//CNFtoZDDconverter class

class CNFtoZDDconverter {
	
public:
	//constructors
	CNFtoZDDconverter();

	//helper functions
	std::runtime_error EmptyFormulaException(const std::string& filepath) const;

	ZDD ClausetoZDD(const CnfClause& cl, Cudd& mgr, int maxvar); 
	int indexConverter(int g);
	int maxVarRange(const QCnfFormula& qcnf);	
	std::unordered_map<int, int> produceIndicesMap(int maxvar);
	
	
	//main converter
	std::vector<ZDD> convertCNFtoZDD(const std::string& path);
	
	//draw ZDD
	void ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames);
	
};


#endif // CNF_TO_ZDD_H








