#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <iostream>
#include <vector>
#include <fstream>   
#include <iterator>
#include <map>
#include <string>  
#include <algorithm>
#include "cudd.h"
#include "cuddObj.hh"
#include "qdimacs-reader/CnfFormula.hpp"
#include "qdimacs-reader/QCnfFormula.hpp"
#include "qdimacs-reader/QDimacsReader.hpp"  
#include "CNFtoZDDconverter.hpp"


// function to print clauses represented by a ZDD
void printZDD (ZDD z)
{
	return;

}

// ZDD with more vars---define zdd at the last step
int main (int argc, char *argv[])
{
 
	const std::string str1 = "test.txt";
	//const std::string& str = str1;
	CNFtoZDDconverter c;
	// ZDD.dot, realizability (full, partial), resolution
	c.convertCNFtoZDD(str1);
	

	return 0;
}