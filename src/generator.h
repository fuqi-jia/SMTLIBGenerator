#ifndef GENERATOR_H
#define GENERATOR_H

#include "../SMTLIBParser/include/parser.h"
#include <random>
#include <string>
#include <vector>
#include <map>
#include <set>

namespace SMTLIBGenerator {

class Generator {
private:
    // 随机生成器
    std::mt19937 rng;
    // 衰减概率
    double decay_probability;
    // 支持的逻辑
    std::string logic;
    // SMTLIBParser
    std::shared_ptr<SMTLIBParser::Parser> parser;
    // 变量和值的映射，用于维护变量的赋值
    std::map<std::string, std::shared_ptr<SMTLIBParser::DAGNode>> variable_values;
    // 已创建的变量列表
    std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> variables;
    // 可用的理论操作符
    std::set<SMTLIBParser::NODE_KIND> available_operators;
    // 下一个变量ID
    int next_var_id = 0;

    // 随机生成一个变量或常量
    std::shared_ptr<SMTLIBParser::DAGNode> generateVariable(const std::shared_ptr<SMTLIBParser::Sort>& sort);
    
    // 随机生成一个表达式节点
    std::shared_ptr<SMTLIBParser::DAGNode> generateExpression(int depth, const std::shared_ptr<SMTLIBParser::Sort>& sort);
    
    // 随机生成一个约束
    std::shared_ptr<SMTLIBParser::DAGNode> generateConstraint(int depth);
    
    // 收集表达式中的所有变量并添加到变量列表
    void collectVariables(const std::shared_ptr<SMTLIBParser::DAGNode>& node);
    
    // 加载理论操作符
    void loadTheories();

public:
    // 构造函数
    Generator(unsigned int seed = std::random_device{}(), double decay_prob = 0.5);
    
    // 设置逻辑类型
    void setLogic(const std::string& logic);
    
    // 生成SMTLIB2文件
    void generateSMTLIB2File(const std::string& output_path, int num_vars, int num_constraints);
    
    // 加载特定理论
    void loadTheory(const std::string& theory_name);
};

} // namespace SMTLIBGenerator

#endif // GENERATOR_H
