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



int main (int argc, char *argv[])
{
	if (argc < 2) {
		std::cout << "Usage: " << std::string(argv[0]) << " <filename>" << std::endl;
		return 0;
	}
	const std::string str1(argv[1]);
	
	CNFtoZDDconverter c(0,0);
	c.convertCNFtoZDD(str1);



	
	return 0;
}