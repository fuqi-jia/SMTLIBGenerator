#ifndef NTA_H
#define NTA_H

#include "../../SMTLIBParser/include/kind.h"
#include <set>

namespace SMTLIBGenerator {

// Non-linear Transcendental Arithmetic (NTA) theory
std::set<SMTLIBParser::NODE_KIND> getNTAOperators() {
    std::set<SMTLIBParser::NODE_KIND> operators = {
        // 基本算术运算
        SMTLIBParser::NODE_KIND::NT_ADD,
        SMTLIBParser::NODE_KIND::NT_SUB,
        SMTLIBParser::NODE_KIND::NT_MUL,
        SMTLIBParser::NODE_KIND::NT_NEG,
        SMTLIBParser::NODE_KIND::NT_DIV_REAL,
        
        // 比较运算
        SMTLIBParser::NODE_KIND::NT_EQ,
        SMTLIBParser::NODE_KIND::NT_LE,
        SMTLIBParser::NODE_KIND::NT_LT,
        SMTLIBParser::NODE_KIND::NT_GE,
        SMTLIBParser::NODE_KIND::NT_GT,
        
        // 超越函数
        SMTLIBParser::NODE_KIND::NT_POW,
        SMTLIBParser::NODE_KIND::NT_SQRT,
        SMTLIBParser::NODE_KIND::NT_EXP,
        SMTLIBParser::NODE_KIND::NT_LOG,
        SMTLIBParser::NODE_KIND::NT_LN,
        SMTLIBParser::NODE_KIND::NT_SIN,
        SMTLIBParser::NODE_KIND::NT_COS,
        SMTLIBParser::NODE_KIND::NT_TAN,
        SMTLIBParser::NODE_KIND::NT_ASIN,
        SMTLIBParser::NODE_KIND::NT_ACOS,
        SMTLIBParser::NODE_KIND::NT_ATAN
    };
    
    return operators;
}

} // namespace SMTLIBGenerator

#endif // NTA_H
