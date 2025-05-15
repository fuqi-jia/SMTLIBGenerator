#ifndef QF_LIA_H
#define QF_LIA_H

#include "../../SMTLIBParser/include/kind.h"
#include <set>

namespace SMTLIBGenerator {

// Quantifier-Free Linear Integer Arithmetic (QF_LIA) theory
std::set<SMTLIBParser::NODE_KIND> getQF_LIAOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        // 基本算术运算
        SMTLIBParser::NODE_KIND::NT_ADD,
        SMTLIBParser::NODE_KIND::NT_SUB,
        SMTLIBParser::NODE_KIND::NT_MUL,  // 只用于线性表达式(一个变量乘以常数)
        SMTLIBParser::NODE_KIND::NT_NEG,
        
        // 整数特定运算
        SMTLIBParser::NODE_KIND::NT_DIV_INT,
        SMTLIBParser::NODE_KIND::NT_MOD,
        
        // 比较运算
        SMTLIBParser::NODE_KIND::NT_EQ,
        SMTLIBParser::NODE_KIND::NT_LE,
        SMTLIBParser::NODE_KIND::NT_LT,
        SMTLIBParser::NODE_KIND::NT_GE,
        SMTLIBParser::NODE_KIND::NT_GT,
        
        // 布尔运算符
        SMTLIBParser::NODE_KIND::NT_AND,
        SMTLIBParser::NODE_KIND::NT_OR,
        SMTLIBParser::NODE_KIND::NT_NOT,
        
        // 整数特性检查
        SMTLIBParser::NODE_KIND::NT_IS_INT,
        SMTLIBParser::NODE_KIND::NT_IS_DIVISIBLE
    };
    
    return operators;
}

} // namespace SMTLIBGenerator

#endif // QF_LIA_H 