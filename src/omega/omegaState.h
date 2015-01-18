#ifndef omegaState_HEADER
#define omegaState_HEADER

#include <map>
#include <string>

namespace omega {

class Expr {};
class ExprConstant : public Expr {};
class ExprBinOp  : public Expr {};
class ExprAdd    : public ExprBinOp {};
class ExprSub    : public ExprBinOp {};
class ExprMul    : public ExprBinOp {};
class ExprUdiv   : public ExprBinOp {};
class ExprUmod   : public ExprBinOp {};
class ExprAnd    : public ExprBinOp {};
class ExprOr     : public ExprBinOp {};
class ExprXor    : public ExprBinOp {};
class ExprShl    : public ExprBinOp {};
class ExprShr    : public ExprBinOp {};
class ExprCmpE q : public ExprBinOp {};
class ExprCmpLtu : public ExprBinOp {};
class ExprCmpLeu : public ExprBinOp {};
class ExprCmpLts : public ExprBinOp {};
class ExprCmpLes : public ExprBinOp {};


class Variable {
	private :

};
class Array {

};


class OmegaState {
	private :
		std::map <std::string, OmegaVariable> variables;
		std::map <std::string, OmegaArray> arrays;
	public :

};

};

#endif