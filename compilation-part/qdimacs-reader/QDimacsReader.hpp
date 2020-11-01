#ifndef Q_DIMACS_READER_H
#define Q_DIMACS_READER_H

#include <fstream>
#include <tuple>

#include "QCnfFormula.hpp"

class QDimacsReader {
	std::runtime_error EofException() const;

	std::runtime_error InputFormatException(const std::string& expected,
	                                        const std::string& got) const;

	std::runtime_error FileNotFoundException(const std::string& path) const;

	void SkipComments(std::ifstream& in) const;

	std::tuple<int, int> ReadHeader(std::ifstream& in) const;

	std::vector<int> ReadQuantifiedVars(std::ifstream& in,
	                                    const std::string& quantifier) const;

	CnfFormula ReadClauses(std::ifstream& in, int clause_count) const;

public:

	QCnfFormula Read(const std::string& path) const;
};

#endif // Q_DIMACS_READER_H
