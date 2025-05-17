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
    // 模型对象，用于存储变量值
    SMTLIBParser::Model model;
    // 变量和值的映射，用于维护变量的赋值
    std::map<std::string, std::shared_ptr<SMTLIBParser::DAGNode>> variable_values;
    // 已创建的变量列表
    std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> variables;
    // 下一个变量ID
    int next_var_id = 0;
    // 布尔变量生成概率
    double bool_var_probability = 0.2;

    // operators
    std::shared_ptr<SMTLIBParser::Sort> default_var_sort;
    std::set<SMTLIBParser::NODE_KIND> available_operators;
    std::set<SMTLIBParser::NODE_KIND> bool_operators;
    std::set<SMTLIBParser::NODE_KIND> comp_operators;
    std::set<SMTLIBParser::NODE_KIND> term_operators;
    std::set<SMTLIBParser::NODE_KIND> other_operators;
    
    // 整数变量取值范围
    int int_min_value = -100;
    int int_max_value = 100;
    // 实数变量取值范围
    double real_min_value = -100.0;
    double real_max_value = 100.0;
    // 约束生成深度
    int constraint_depth = 4;


    // 随机生成一个常量

    std::shared_ptr<SMTLIBParser::DAGNode> generateConstant(const std::shared_ptr<SMTLIBParser::Sort>& sort);
    std::shared_ptr<SMTLIBParser::DAGNode> generateConstant(const std::string& logic_name);

    // 随机选择一个变量
    std::shared_ptr<SMTLIBParser::DAGNode> selectVariable(const std::shared_ptr<SMTLIBParser::Sort>& sort);
    
    // 随机生成一个约束
    std::shared_ptr<SMTLIBParser::DAGNode> generateConstraint(int depth);
    
    // 生成布尔表达式约束
    std::shared_ptr<SMTLIBParser::DAGNode> generateBooleanConstraint(int depth);
    
    // 生成关系表达式约束
    std::shared_ptr<SMTLIBParser::DAGNode> generateRelationalConstraint(int depth);
    
    // 生成算术表达式
    std::shared_ptr<SMTLIBParser::DAGNode> generateArithmeticExpression(int depth, const std::shared_ptr<SMTLIBParser::Sort>& sort);
    
    // 生成模型文件
    void generateModelFile(const std::string& model_path);

public:
    // 构造函数
    Generator(unsigned int seed = std::random_device{}(), double decay_prob = 0.5);
    
    // 设置逻辑类型
    void setLogic(const std::string& logic);
    
    // 生成SMTLIB2文件
    void generateSMTLIB2File(const std::string& output_path, int num_vars, int num_constraints);
    
    // 加载特定理论
    void loadTheory(const std::string& theory_name);
    
    // 设置布尔变量生成概率 (0.0-1.0)
    void setBoolVarProbability(double probability);
    
    // 设置整数变量的取值范围
    void setIntRange(int min_value, int max_value);
    
    // 设置实数变量的取值范围
    void setRealRange(double min_value, double max_value);
    
    // 设置约束生成深度
    void setConstraintDepth(int depth);
};

} // namespace SMTLIBGenerator

#endif // GENERATOR_H
