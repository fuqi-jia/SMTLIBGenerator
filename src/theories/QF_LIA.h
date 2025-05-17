#ifndef QF_LIA_H
#define QF_LIA_H

#include "../../SMTLIBParser/include/kind.h"
#include <set>

namespace SMTLIBGenerator {

// Quantifier-Free Linear Integer Arithmetic (QF_LIA) theory
std::set<SMTLIBParser::NODE_KIND> getLIAOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators;

    operators.insert(getLIABoolOperators().begin(), getLIABoolOperators().end());
    operators.insert(getLIACompOperators().begin(), getLIACompOperators().end());
    operators.insert(getLIATermOperators().begin(), getLIATermOperators().end());
    operators.insert(getLIAOtherOperators().begin(), getLIAOtherOperators().end());
    
    return operators;
}

std::set<SMTLIBParser::NODE_KIND> getLIABoolOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        SMTLIBParser::NODE_KIND::NT_AND,
        SMTLIBParser::NODE_KIND::NT_OR,
        SMTLIBParser::NODE_KIND::NT_NOT,
        SMTLIBParser::NODE_KIND::NT_XOR,
        SMTLIBParser::NODE_KIND::NT_IMPL
    };
}

std::set<SMTLIBParser::NODE_KIND> getLIACompOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        // 比较运算
        SMTLIBParser::NODE_KIND::NT_EQ,
        SMTLIBParser::NODE_KIND::NT_LE,
        SMTLIBParser::NODE_KIND::NT_LT,
        SMTLIBParser::NODE_KIND::NT_GE,
        SMTLIBParser::NODE_KIND::NT_GT,
    };
}

std::set<SMTLIBParser::NODE_KIND> getLIATermOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        // 基本算术运算
        SMTLIBParser::NODE_KIND::NT_ADD,
        SMTLIBParser::NODE_KIND::NT_SUB,
        SMTLIBParser::NODE_KIND::NT_MUL,  // 只用于线性表达式(一个变量乘以常数)
        SMTLIBParser::NODE_KIND::NT_NEG,
        
        // 整数特定运算
        SMTLIBParser::NODE_KIND::NT_DIV_INT,
        SMTLIBParser::NODE_KIND::NT_MOD,
    };
}

std::set<SMTLIBParser::NODE_KIND> getLIAOtherOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        SMTLIBParser::NODE_KIND::NT_IS_INT,
        SMTLIBParser::NODE_KIND::NT_IS_DIVISIBLE
    };
}

} // namespace SMTLIBGenerator

#endif // QF_LIA_H 