/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 *
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>
#include <algorithm>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

// Helper function to compute GCD (declared in expr.cpp)
extern int gcd(int a, int b);

// Helper function to add two values (integers or rationals)
Value addValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 + n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = n1 * r2->denominator + r2->numerator;
        int den = r2->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int num = r1->numerator + n2 * r1->denominator;
        int den = r1->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in addition");
}

// Helper function to subtract two values
Value subtractValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 - n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = n1 * r2->denominator - r2->numerator;
        int den = r2->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int num = r1->numerator - n2 * r1->denominator;
        int den = r1->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in subtraction");
}

// Helper function to multiply two values
Value multiplyValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 * n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = r1->numerator * r2->numerator;
        int den = r1->denominator * r2->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int num = n1 * r2->numerator;
        int den = r2->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int num = r1->numerator * n2;
        int den = r1->denominator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in multiplication");
}

// Helper function to divide two values
Value divideValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        int g = gcd(n1, n2);
        if (g != 0) {
            n1 /= g;
            n2 /= g;
        }
        if (n2 < 0) {
            n1 = -n1;
            n2 = -n2;
        }
        if (n2 == 1) return IntegerV(n1);
        return RationalV(n1, n2);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        int num = r1->numerator * r2->denominator;
        int den = r1->denominator * r2->numerator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        int num = n1 * r2->denominator;
        int den = r2->numerator;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    } else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        int num = r1->numerator;
        int den = r1->denominator * n2;
        int g = gcd(num, den);
        if (g != 0) {
            num /= g;
            den /= g;
        }
        if (den < 0) {
            num = -num;
            den = -den;
        }
        if (den == 1) return IntegerV(num);
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in division");
}

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (const auto &expr : rands) {
        args.push_back(expr->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            return ProcedureV({}, Expr(new Var(x)), e);
        }
        throw RuntimeError("Undefined variable: " + x);
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    return addValues(rand1, rand2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    return subtractValues(rand1, rand2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    return multiplyValues(rand1, rand2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    return divideValues(rand1, rand2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.size() == 0) return IntegerV(0);
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = addValues(result, args[i]);
    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.size() == 0) throw RuntimeError("Wrong number of arguments for -");
    if (args.size() == 1) {
        if (args[0]->v_type == V_INT) {
            return IntegerV(-dynamic_cast<Integer*>(args[0].get())->n);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            return RationalV(-r->numerator, r->denominator);
        }
        throw RuntimeError("Wrong typename");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = subtractValues(result, args[i]);
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.size() == 0) return IntegerV(1);
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = multiplyValues(result, args[i]);
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.size() == 0) throw RuntimeError("Wrong number of arguments for /");
    if (args.size() == 1) {
        return divideValues(IntegerV(1), args[0]);
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); ++i) {
        result = divideValues(result, args[i]);
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;

        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }

        long long result = 1;
        long long b = base;
        int exp = exponent;

        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }

        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; ++i) {
        if (compareNumericValues(args[i], args[i + 1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; ++i) {
        if (compareNumericValues(args[i], args[i + 1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; ++i) {
        if (compareNumericValues(args[i], args[i + 1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; ++i) {
        if (compareNumericValues(args[i], args[i + 1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; ++i) {
        if (compareNumericValues(args[i], args[i + 1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; --i) {
        result = PairV(args[i], result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    if (rand->v_type == V_NULL) return BooleanV(true);
    if (rand->v_type != V_PAIR) return BooleanV(false);

    Value curr = rand;
    while (curr->v_type == V_PAIR) {
        Pair* p = dynamic_cast<Pair*>(curr.get());
        curr = p->cdr;
    }
    return BooleanV(curr->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car: argument must be a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr: argument must be a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car!: first argument must be a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr!: first argument must be a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

// Helper function to convert Syntax to Value
Value syntaxToValue(const Syntax &s) {
    if (dynamic_cast<Number*>(s.get()) != nullptr) {
        Number* num = dynamic_cast<Number*>(s.get());
        return IntegerV(num->n);
    } else if (dynamic_cast<RationalSyntax*>(s.get()) != nullptr) {
        RationalSyntax* rat = dynamic_cast<RationalSyntax*>(s.get());
        return RationalV(rat->numerator, rat->denominator);
    } else if (dynamic_cast<TrueSyntax*>(s.get()) != nullptr) {
        return BooleanV(true);
    } else if (dynamic_cast<FalseSyntax*>(s.get()) != nullptr) {
        return BooleanV(false);
    } else if (dynamic_cast<SymbolSyntax*>(s.get()) != nullptr) {
        SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(s.get());
        return SymbolV(sym->s);
    } else if (dynamic_cast<StringSyntax*>(s.get()) != nullptr) {
        StringSyntax* str = dynamic_cast<StringSyntax*>(s.get());
        return StringV(str->s);
    } else if (dynamic_cast<List*>(s.get()) != nullptr) {
        List* lst = dynamic_cast<List*>(s.get());
        if (lst->stxs.empty()) {
            return NullV();
        }
        Value result = NullV();
        for (int i = lst->stxs.size() - 1; i >= 0; --i) {
            result = PairV(syntaxToValue(lst->stxs[i]), result);
        }
        return result;
    }
    throw RuntimeError("Unknown syntax type in quote");
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) return VoidV();
    Value result = VoidV();
    for (const auto &expr : es) {
        result = expr->eval(e);
    }
    return result;
}

Value Quote::eval(Assoc& e) {
    return syntaxToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) return BooleanV(true);
    Value result = BooleanV(true);
    for (const auto &expr : rands) {
        result = expr->eval(e);
        if (result->v_type == V_BOOL && !dynamic_cast<Boolean*>(result.get())->b) {
            return BooleanV(false);
        }
    }
    return result;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) return BooleanV(false);
    for (const auto &expr : rands) {
        Value result = expr->eval(e);
        if (result->v_type != V_BOOL || dynamic_cast<Boolean*>(result.get())->b) {
            return result;
        }
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b) {
        return BooleanV(true);
    }
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value cond_val = cond->eval(e);
    bool is_true = true;
    if (cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b) {
        is_true = false;
    }
    if (is_true) {
        return conseq->eval(e);
    } else {
        return alter->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (const auto &clause : clauses) {
        if (clause.empty()) continue;

        // Check for 'else' clause
        if (auto var_expr = dynamic_cast<Var*>(clause[0].get())) {
            if (var_expr->x == "else") {
                if (clause.size() == 1) return VoidV();
                Value result = VoidV();
                for (size_t i = 1; i < clause.size(); ++i) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }

        Value cond_val = clause[0]->eval(env);
        bool is_true = true;
        if (cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b) {
            is_true = false;
        }

        if (is_true) {
            if (clause.size() == 1) return cond_val;
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); ++i) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value rator_val = rator->eval(e);
    if (rator_val->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    Procedure* clos_ptr = dynamic_cast<Procedure*>(rator_val.get());

    std::vector<Value> args;
    for (const auto &expr : rand) {
        args.push_back(expr->eval(e));
    }

    // Check for variadic Begin node
    if (auto begin_node = dynamic_cast<Begin*>(clos_ptr->e.get())) {
        // Handle multi-expression body
    }

    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); ++i) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Check if variable name overlaps with primitives or reserved words
    if (primitives.count(var) || reserved_words.count(var)) {
        throw RuntimeError("Cannot redefine primitive or reserved word: " + var);
    }

    Value val = e->eval(env);

    // Try to modify existing binding
    Value existing = find(var, env);
    if (existing.get() != nullptr) {
        modify(var, val, env);
    } else {
        // Create new binding by extending environment
        env = extend(var, val, env);
    }

    return VoidV();
}

Value Let::eval(Assoc &env) {
    // Evaluate all binding expressions in current environment
    std::vector<Value> vals;
    for (const auto &binding : bind) {
        vals.push_back(binding.second->eval(env));
    }

    // Create new environment with all bindings
    Assoc new_env = env;
    for (size_t i = 0; i < bind.size(); ++i) {
        new_env = extend(bind[i].first, vals[i], new_env);
    }

    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // Create new environment with placeholder bindings
    Assoc new_env = env;
    for (const auto &binding : bind) {
        new_env = extend(binding.first, Value(nullptr), new_env);
    }

    // Evaluate all binding expressions in new environment
    for (const auto &binding : bind) {
        Value val = binding.second->eval(new_env);
        modify(binding.first, val, new_env);
    }

    return body->eval(new_env);
}

Value Set::eval(Assoc &env) {
    Value val = e->eval(env);
    Value existing = find(var, env);
    if (existing.get() == nullptr) {
        throw RuntimeError("Undefined variable in set!: " + var);
    }
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
