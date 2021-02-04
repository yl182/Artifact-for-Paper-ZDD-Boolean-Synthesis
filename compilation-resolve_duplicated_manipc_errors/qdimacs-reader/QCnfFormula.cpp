#include "QCnfFormula.hpp"

QCnfFormula::QCnfFormula(std::vector<int> uv, std::vector<int> ev,
                         CnfFormula f)
	: universal_vars(std::move(uv))
	, existential_vars(std::move(ev))
	, formula(std::move(f)) {}
