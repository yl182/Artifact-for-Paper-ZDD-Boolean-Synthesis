#include "QDimacsReader.hpp"

std::runtime_error QDimacsReader::EofException() const {
	return std::runtime_error("Unexpected end of file while reading input file");
}

std::runtime_error QDimacsReader::InputFormatException(
    const std::string& expected, const std::string& got) const {
	return std::runtime_error("Incorrect format of input file: expected \"" +
	                          expected + "\", got \"" + got + "\"");
}

std::runtime_error QDimacsReader::FileNotFoundException(const std::string& path)
	  const {
	return std::runtime_error("Unable to open file " + path);
}

/**
 * Skip all comment lines.
 */
void QDimacsReader::SkipComments(std::ifstream& in) const {
	std::string line;

	while (in.peek() == 'c') {
		std::getline(in, line);
	}

	if (in.eof()) {
		throw EofException(); 
	}
}

/**
 * Reads header of DIMACS file in format (p cnf <var-count> <clause-count>).
 */
std::tuple<int, int> QDimacsReader::ReadHeader(std::ifstream& in) const {
	std::string p, cnf;
	in >> p >> cnf;

	if (p != "p" && cnf != "cnf")
		{
			throw InputFormatException("p cnf", p + " " + cnf); 
		}

	int var_count, clause_count;
	in >> var_count >> clause_count;

	return std::make_tuple(var_count, clause_count);
}

/**
 * Reads list of quantified variables from the input string.
 */
std::vector<int> QDimacsReader::ReadQuantifiedVars(
    std::ifstream& in, const std::string& quantifier) const {
	std::string q;
	in >> q;

	/* Check that the quantifier is the one we expected */
	if (q != quantifier) {
		throw InputFormatException(quantifier, q); 
	}

	std::vector<int> quantified_vars;
  
	int v;
	in >> v;

	/* Read variables until the 0 delimiter */
	while (!in.eof() && v != 0) {
		quantified_vars.emplace_back(v);
		in >> v;
	}

	/* Error if file ended before finding a 0 */
	if (in.eof()) {
		throw EofException();
	}

	return quantified_vars;
}

/**
 * Reads the given number of clauses from the input stream.
 */
CnfFormula QDimacsReader::ReadClauses(std::ifstream& in, int clause_count)
	  const {
	CnfFormula formula;

	for (size_t i = 0; i < clause_count; i++) {
		CnfClause clause;

		int lit;
		in >> lit;

		/* Read literals until the 0 delimiter */
		while (!in.eof() && lit != 0) {
			clause |= lit;

			in >> lit;
		}

		/* Error if file ended before finding a 0 */
		if (lit != 0) {
			throw EofException();
		}

		formula &= clause;
	}

	return formula;
}

/**
 * Reads a forall-exists QDIMACS file and parses it into a specification in CNF.
 * Assumes that all comments are located at the start of the file.
 */
QCnfFormula QDimacsReader::Read(const std::string& path) const {
	std::ifstream in(path);

	if (!in.is_open())
		throw FileNotFoundException(path); 

	SkipComments(in);

	/**< get only the number of clauses */
	int clause_count = std::get<1>(ReadHeader(in));

	/**< read list of universal variables */ 
	std::vector<int> universal_vars = ReadQuantifiedVars(in, "a");
	/**< read list of existential variables */
	std::vector<int> existential_vars = ReadQuantifiedVars(in, "e");

	CnfFormula formula = ReadClauses(in, clause_count);

	return QCnfFormula(std::move(universal_vars), std::move(existential_vars),
	                   std::move(formula));
}
