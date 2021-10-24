#ifndef Q_CNF_FORMULA_H
#define Q_CNF_FORMULA_H

#include <vector>

#include "CnfFormula.hpp"

struct QCnfFormula {
	const std::vector<int> universal_vars;
	const std::vector<int> existential_vars;
	const CnfFormula formula;

	QCnfFormula(std::vector<int> uv, std::vector<int> ev, CnfFormula f);
};

#endif // Q_CNF_FORMULA_H
