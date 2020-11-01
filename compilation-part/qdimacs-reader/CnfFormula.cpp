#include "CnfFormula.hpp"

/** CnfClause **/

CnfClause::CnfClause() {}

CnfClause::CnfClause(int lit) {
	lits_ = { lit };
}

CnfClause::CnfClause(int l1, int l2) {
	lits_ = { l1, l2 };
}

CnfClause::CnfClause(int l1, int l2, int l3) {
	lits_ = { l1, l2, l3 };
}

void CnfClause::operator|=(int lit) {
	lits_.push_back(lit);
}

void CnfClause::operator|=(const CnfClause& other) {
	lits_.insert(lits_.end(), other.lits_.begin(), other.lits_.end());
}

CnfClause CnfClause::operator|(const CnfClause& other) const {
	CnfClause newClause(*this);

	newClause |= other;

	return newClause;
}

/** CnfFormula **/

CnfFormula::CnfFormula() {}

CnfFormula::CnfFormula(CnfClause c) {
	clauses_ = { c };
}

void CnfFormula::operator&=(CnfClause clause) {
	clauses_.push_back(clause);
}

void CnfFormula::operator&=(const CnfFormula& other) {
	clauses_.insert(clauses_.end(),
	                other.clauses_.begin(),
	                other.clauses_.end());
}

CnfFormula CnfFormula::operator&(const CnfFormula& other) const {
	CnfFormula cnf(*this);

	cnf &= other;

	return cnf;
}

const CnfClause& CnfFormula::operator[](size_t i) const {
	return clauses_[i];
}

