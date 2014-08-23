#ifndef symbolicExpression
#define symbolicExpression

class Expr {
    public :
        virtual ~Expr() {}
};

class ExprArith {
    private :
        Expr * lhs;
        Expr * rhs;
    public :
        ExprArith (Expr * lhs, Expr * rhs)
        virtual ~ExprArith () {}
};

class ExprAdd : ExprArith {
    public :
        ExprAdd (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprSub : ExprArith {
    public :
        ExprSub (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprMul : ExprArith {
    public :
        ExprMul (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprUdiv : ExprArith {
    public :
        ExprUdiv (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprUmod : ExprArith {
    public :
        ExprUmod (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprAnd : ExprArith {
    public :
        ExprAnd (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprOr : ExprArith {
    public :
        ExprOr (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprXor : ExprArith {
    public :
        ExprXor (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprShl : ExprArith {
    public :
        ExprShr (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprUdiv : ExprArith {
    public :
        ExprUdiv (Expr * lhs, Expr * rhs)
            : ExprArith (lhs, rhs) {}
};

class ExprCmp : public Expr {
    private :
        Expr * lhs;
        Expr * rhs;
    public :
        ExprCmp (Expr * lhs, Expr * rhs);
        virtual ~ExprCmp () {}
};

class ExprCmpEq : ExprArith {
    public :
        ExprCmpEq (Expr * lhs, Expr * rhs)
            : ExprCmp (lhs, rhs) {}
};

class ExprCmpLtu : ExprArith {
    public :
        ExprCmpLtu (Expr * lhs, Expr * rhs)
            : ExprCmp (lhs, rhs) {}
};

class ExprCmpLeu : ExprArith {
    public :
        ExprCmpLeu (Expr * lhs, Expr * rhs)
            : ExprCmp (lhs, rhs) {}
};

class ExprCmpLts : ExprArith {
    public :
        ExprCmpLts (Expr * lhs, Expr * rhs)
            : ExprCmp (lhs, rhs) {}
};

class ExprCmpLes : ExprArith {
    public :
        ExprCmpLes (Expr * lhs, Expr * rhs)
            : ExprCmp (lhs, rhs) {}
};

#endif