#ifndef CNF_CLAUSE_H
#define CNF_CLAUSE_H

#include <vector>

class CnfClause {
	std::vector<int> lits_;

public:

	CnfClause();
	CnfClause(int l);
	CnfClause(int l1, int l2);
	CnfClause(int l1, int l2, int l3);

	void operator|=(int lit);
	void operator|=(const CnfClause& other);
	CnfClause operator|(const CnfClause& other) const;

	int operator[](size_t i) const;

	size_t size() const;

	/** Iterators */

	using const_iterator = std::vector<int>::const_iterator;

	inline const_iterator begin() const noexcept { return lits_.cbegin(); }
	inline const_iterator end() const noexcept { return lits_.cend(); }
};

class CnfFormula {
	std::vector<CnfClause> clauses_;

public:

	CnfFormula();
	CnfFormula(CnfClause c);

	void operator&=(CnfClause clause);
	void operator&=(const CnfFormula& other);
	CnfFormula operator&(const CnfFormula& other) const;

	const CnfClause& operator[](size_t i) const;

	size_t size() const;

	/** Iterators */

	using const_iterator = std::vector<CnfClause>::const_iterator;

	inline const_iterator begin() const noexcept { return clauses_.cbegin(); }
	inline const_iterator end() const noexcept { return clauses_.cend(); }
};

#endif // CNF_CLAUSE_H
