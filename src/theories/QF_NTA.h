#ifndef QF_NTA_H
#define QF_NTA_H

#include "../../SMTLIBParser/include/kind.h"
#include <set>

namespace SMTLIBGenerator {

// Quantifier-Free Non-linear Transcendental Arithmetic (QF_NTA) theory
std::set<SMTLIBParser::NODE_KIND> getNTAOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators;

    operators.insert(getNTABoolOperators().begin(), getNTABoolOperators().end());
    operators.insert(getNTACompOperators().begin(), getNTACompOperators().end());
    operators.insert(getNTATermOperators().begin(), getNTATermOperators().end());
    operators.insert(getNTAOtherOperators().begin(), getNTAOtherOperators().end());
    
    return operators;
}

std::set<SMTLIBParser::NODE_KIND> getNTABoolOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        SMTLIBParser::NODE_KIND::NT_AND,
        SMTLIBParser::NODE_KIND::NT_OR,
        SMTLIBParser::NODE_KIND::NT_NOT,
        SMTLIBParser::NODE_KIND::NT_XOR,
        SMTLIBParser::NODE_KIND::NT_IMPL
    };
    
    return operators;
}

std::set<SMTLIBParser::NODE_KIND> getNTACompOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        // 比较运算
        SMTLIBParser::NODE_KIND::NT_EQ,
        SMTLIBParser::NODE_KIND::NT_LE,
        SMTLIBParser::NODE_KIND::NT_LT,
        SMTLIBParser::NODE_KIND::NT_GE,
        SMTLIBParser::NODE_KIND::NT_GT
    };
    
    return operators;
}

std::set<SMTLIBParser::NODE_KIND> getNTATermOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        // 基本算术运算
        SMTLIBParser::NODE_KIND::NT_ADD,
        SMTLIBParser::NODE_KIND::NT_SUB,
        SMTLIBParser::NODE_KIND::NT_MUL,
        SMTLIBParser::NODE_KIND::NT_DIV_REAL,
        SMTLIBParser::NODE_KIND::NT_NEG,
        SMTLIBParser::NODE_KIND::NT_POW,
        SMTLIBParser::NODE_KIND::NT_POW2,
        SMTLIBParser::NODE_KIND::NT_ABS,
        SMTLIBParser::NODE_KIND::NT_SQRT,
        SMTLIBParser::NODE_KIND::NT_SAFE_SQRT,


        // 超越函数
        SMTLIBParser::NODE_KIND::NT_EXP,
        SMTLIBParser::NODE_KIND::NT_LOG,
        SMTLIBParser::NODE_KIND::NT_LG,
        SMTLIBParser::NODE_KIND::NT_LB,
        SMTLIBParser::NODE_KIND::NT_LN,
        SMTLIBParser::NODE_KIND::NT_LB,
        
        // 三角函数
        SMTLIBParser::NODE_KIND::NT_SIN,
        SMTLIBParser::NODE_KIND::NT_COS,
        SMTLIBParser::NODE_KIND::NT_TAN,
        SMTLIBParser::NODE_KIND::NT_COT,
        SMTLIBParser::NODE_KIND::NT_SEC,
        SMTLIBParser::NODE_KIND::NT_CSC,
        
        // 反三角函数
        SMTLIBParser::NODE_KIND::NT_ASIN,
        SMTLIBParser::NODE_KIND::NT_ACOS,
        SMTLIBParser::NODE_KIND::NT_ATAN,
        SMTLIBParser::NODE_KIND::NT_ACOT,
        SMTLIBParser::NODE_KIND::NT_ASEC,
        SMTLIBParser::NODE_KIND::NT_ACSC,

        
        // 双曲函数
        SMTLIBParser::NODE_KIND::NT_SINH,
        SMTLIBParser::NODE_KIND::NT_COSH,
        SMTLIBParser::NODE_KIND::NT_TANH,
        SMTLIBParser::NODE_KIND::NT_COTH,
        SMTLIBParser::NODE_KIND::NT_SECH,
        SMTLIBParser::NODE_KIND::NT_CSCH,
        
        // 反双曲函数
        SMTLIBParser::NODE_KIND::NT_ASINH,
        SMTLIBParser::NODE_KIND::NT_ACOSH,
        SMTLIBParser::NODE_KIND::NT_ATANH,
        SMTLIBParser::NODE_KIND::NT_ACOTH,
        SMTLIBParser::NODE_KIND::NT_ASECH,
        SMTLIBParser::NODE_KIND::NT_ACSCH
    };
    
    return operators;
}

std::set<SMTLIBParser::NODE_KIND> getNTAOtherOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        SMTLIBParser::NODE_KIND::NT_IS_INT,
        SMTLIBParser::NODE_KIND::NT_TO_INT,
        SMTLIBParser::NODE_KIND::NT_TO_REAL
    };
    
    return operators;
}

} // namespace SMTLIBGenerator

#endif // QF_NTA_H
