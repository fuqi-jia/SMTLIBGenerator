#include "generator.h"
#include "theories/NTA.h"
#include "theories/QF_LIA.h"
#include <fstream>
#include <iostream>
#include <sstream>
#include <cmath>
#include <chrono>
#include <ctime>
#include <iomanip>
#include <filesystem>
#include <algorithm>

namespace SMTLIBGenerator {

// 构造函数
Generator::Generator(unsigned int seed, double decay_prob) 
    : rng(seed), decay_probability(decay_prob), logic("QF_LIA"), model() {
    // 初始化解析器
    parser = std::make_shared<SMTLIBParser::Parser>();
    
    // 默认加载QF_LIA理论
    loadTheory("QF_LIA");
}

// 设置布尔变量生成概率
void Generator::setBoolVarProbability(double probability) {
    // 确保概率值在有效范围内
    bool_var_probability = std::max(0.0, std::min(1.0, probability));
}

// 设置整数变量的取值范围
void Generator::setIntRange(int min_value, int max_value) {
    // 确保最小值不大于最大值
    if (min_value > max_value) {
        std::swap(min_value, max_value);
    }
    int_min_value = min_value;
    int_max_value = max_value;
}

// 设置实数变量的取值范围
void Generator::setRealRange(double min_value, double max_value) {
    // 确保最小值不大于最大值
    if (min_value > max_value) {
        std::swap(min_value, max_value);
    }
    real_min_value = min_value;
    real_max_value = max_value;
}

// 设置逻辑类型
void Generator::setLogic(const std::string& logic_name) {
    // 支持的逻辑类型
    if (logic_name == "QF_LIA" || logic_name == "NTA" || logic_name == "QF_NTA") {
        logic = logic_name;
    } else {
        std::cerr << "Warning: Unsupported logic: " << logic_name << ". Using QF_LIA instead." << std::endl;
        logic = "QF_LIA";
    }
    
    // 清空现有的操作符
    available_operators.clear();
    
    // 加载对应的理论
    if (logic == "QF_LIA") {
        loadTheory("QF_LIA");
    } else if (logic == "NTA" || logic == "QF_NTA") {
        loadTheory("NTA");
    } else {
        loadTheory("QF_LIA"); // 默认值
    }
}

// 加载特定理论
void Generator::loadTheory(const std::string& theory_name) {
    if (theory_name == "QF_LIA") {
        auto operators = getQF_LIAOperators();
        available_operators.insert(operators.begin(), operators.end());
    } else if (theory_name == "NTA") {
        auto operators = getNTAOperators();
        available_operators.insert(operators.begin(), operators.end());
    } else {
        std::cerr << "Warning: Unsupported theory: " << theory_name << std::endl;
    }
}

// 加载理论操作符
void Generator::loadTheories() {
    // 根据当前设置的逻辑类型加载对应的理论
    if (logic == "QF_LIA") {
        loadTheory("QF_LIA");
    } else if (logic == "NTA") {
        loadTheory("NTA");
    } else {
        // 如果没有匹配的逻辑类型，默认加载QF_LIA
        loadTheory("QF_LIA");
    }
}

// 随机生成一个变量或常量
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateVariable(const std::shared_ptr<SMTLIBParser::Sort>& sort) {
    std::shared_ptr<SMTLIBParser::DAGNode> result;
    
    // 有一定概率创建新变量，否则使用现有变量或创建常量
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    double random_val = dist(rng);
    
    // 如果是布尔类型，且随机值大于布尔变量生成概率，则尝试生成非布尔类型
    if (sort->isBool() && random_val > bool_var_probability) {
        // 如果不是强制要求布尔类型，则根据逻辑类型生成整数或实数变量
        std::shared_ptr<SMTLIBParser::Sort> non_bool_sort;
        if (logic == "QF_LIA") {
            non_bool_sort = SMTLIBParser::INT_SORT;
        } else if (logic == "NTA") {
            non_bool_sort = SMTLIBParser::REAL_SORT;
        } else {
            non_bool_sort = SMTLIBParser::INT_SORT;
        }
        
        // 生成一个比较表达式，结果是布尔类型
        auto left = generateVariable(non_bool_sort);
        auto right = generateVariable(non_bool_sort);
        
        // 随机选择一个比较操作符
        std::vector<SMTLIBParser::NODE_KIND> comparison_ops = {
            SMTLIBParser::NODE_KIND::NT_EQ,
            SMTLIBParser::NODE_KIND::NT_LE,
            SMTLIBParser::NODE_KIND::NT_LT,
            SMTLIBParser::NODE_KIND::NT_GE,
            SMTLIBParser::NODE_KIND::NT_GT
        };
        
        std::uniform_int_distribution<size_t> op_dist(0, comparison_ops.size() - 1);
        SMTLIBParser::NODE_KIND selected_op = comparison_ops[op_dist(rng)];
        
        // 创建比较表达式
        result = parser->mkOper(SMTLIBParser::BOOL_SORT, selected_op, left, right);
        
        // 计算表达式的值并保存
        if (left->isVar() && right->isVar() && 
            variable_values.count(left->getName()) && variable_values.count(right->getName())) {
            auto left_value = variable_values[left->getName()];
            auto right_value = variable_values[right->getName()];
            
            bool comparison_result = false;
            
            if (left_value->isConst() && right_value->isConst()) {
                if (selected_op == SMTLIBParser::NODE_KIND::NT_EQ) {
                    comparison_result = (left_value->getName() == right_value->getName());
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_LE &&
                           left_value->isCInt() && right_value->isCInt()) {
                    comparison_result = (parser->toInt(left_value) <= parser->toInt(right_value));
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_LT &&
                           left_value->isCInt() && right_value->isCInt()) {
                    comparison_result = (parser->toInt(left_value) < parser->toInt(right_value));
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_GE &&
                           left_value->isCInt() && right_value->isCInt()) {
                    comparison_result = (parser->toInt(left_value) >= parser->toInt(right_value));
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_GT &&
                           left_value->isCInt() && right_value->isCInt()) {
                    comparison_result = (parser->toInt(left_value) > parser->toInt(right_value));
                }
            }
            
            variable_values[result->getName()] = comparison_result ? parser->mkTrue() : parser->mkFalse();
        }
        
        return result;
    }
    
    if (random_val < 0.3 && !variables.empty()) {
        // 从现有变量中选择一个合适类型的变量
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> compatible_vars;
        for (const auto& var : variables) {
            if (var->getSort()->isEqTo(sort)) {
                compatible_vars.push_back(var);
            }
        }
        
        if (!compatible_vars.empty()) {
            std::uniform_int_distribution<size_t> var_dist(0, compatible_vars.size() - 1);
            result = compatible_vars[var_dist(rng)];
            return result;
        }
    }
    
    if (random_val < 0.7 || variables.empty()) {
        // 创建一个新变量
        std::string var_name = "x" + std::to_string(next_var_id++);
        
        // 根据排序类型创建不同的变量
        result = parser->mkVar(sort, var_name);
        
        // 生成一个随机值并保存
        if (sort->isInt()) {
            // 整数变量
            std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
            int value = int_dist(rng);
            auto value_node = parser->mkConstInt(value);
            
            // 保存变量和它的值
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var_name, value_node);
            variables.push_back(result);
        } else if (sort->isReal()) {
            // 实数变量
            std::uniform_real_distribution<double> real_dist(real_min_value, real_max_value);
            double value = real_dist(rng);
            
            // 将浮点数转换为分数形式
            auto value_node = parser->mkConstReal(value);
            
            // 保存变量和它的值
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var_name, value_node);
            variables.push_back(result);
        } else if (sort->isBool()) {
            // 布尔变量
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            
            auto value_node = value ? parser->mkTrue() : parser->mkFalse();
            
            // 保存变量和它的值
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var_name, value_node);
            variables.push_back(result);
        } else {
            // 对于不支持的类型，创建默认变量
            // 默认使用整数值
            std::uniform_int_distribution<int> int_dist(-100, 100);
            int value = int_dist(rng);
            auto value_node = parser->mkConstInt(value);
            
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var_name, value_node);
            variables.push_back(result);
        }
    } else {
        // 创建一个常量
        if (sort->isInt()) {
            // 整数常量
            std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
            int value = int_dist(rng);
            result = parser->mkConstInt(value);
        } else if (sort->isReal()) {
            // 实数常量
            std::uniform_real_distribution<double> real_dist(real_min_value, real_max_value);
            double value = real_dist(rng);
            
            // 将浮点数转换为分数形式
            result = parser->mkConstReal(value);
        } else if (sort->isBool()) {
            // 布尔常量
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            
            result = value ? parser->mkTrue() : parser->mkFalse();
        } else {
            // 对于不支持的类型，创建默认变量而不是常量
            std::string var_name = "x" + std::to_string(next_var_id++);
            result = parser->mkVar(sort, var_name);
            
            // 保存默认值
            std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
            int value = int_dist(rng);
            auto value_node = parser->mkConstInt(value);
            
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var_name, value_node);
            variables.push_back(result);
        }
    }
    
    return result;
}

// 随机生成一个表达式节点
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateExpression(int depth, const std::shared_ptr<SMTLIBParser::Sort>& sort) {
    // 如果深度到达限制或随机衰减，则使用已存在的变量或常量
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    if (depth <= 0 || dist(rng) < decay_probability) {
        // 如果有可用的变量，从中选择一个
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> compatible_vars;
        for (const auto& var : variables) {
            if (var->getSort()->isEqTo(sort)) {
                compatible_vars.push_back(var);
            }
        }
        
        if (!compatible_vars.empty()) {
            std::uniform_int_distribution<size_t> var_dist(0, compatible_vars.size() - 1);
            return compatible_vars[var_dist(rng)];
        }
        
        // 如果没有可用的变量，则创建一个常量
        if (sort->isInt()) {
            // 整数常量
            std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
            int value = int_dist(rng);
            return parser->mkConstInt(value);
        } else if (sort->isReal()) {
            // 实数常量
            std::uniform_real_distribution<double> real_dist(real_min_value, real_max_value);
            double value = real_dist(rng);
            return parser->mkConstReal(value);
        } else if (sort->isBool()) {
            // 布尔常量
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            return value ? parser->mkTrue() : parser->mkFalse();
        }
        
        // 未知类型，返回一个整数常量
        std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
        int value = int_dist(rng);
        return parser->mkConstInt(value);
    }
    
    // 以下代码用于生成复杂表达式，需要确保只使用已存在的变量
    // 如果没有足够的变量，则直接返回一个常量或变量
    if (variables.size() < 2) {
        return generateExpression(0, sort);
    }
    
    // 根据排序类型选择可用的操作符
    std::vector<SMTLIBParser::NODE_KIND> compatible_operators;
    
    if (sort->isInt()) {
        // 整数操作符
        for (const auto& op : available_operators) {
            if (op == SMTLIBParser::NODE_KIND::NT_ADD ||
                op == SMTLIBParser::NODE_KIND::NT_SUB ||
                op == SMTLIBParser::NODE_KIND::NT_MUL ||
                op == SMTLIBParser::NODE_KIND::NT_DIV_INT ||
                op == SMTLIBParser::NODE_KIND::NT_MOD ||
                op == SMTLIBParser::NODE_KIND::NT_NEG) {
                compatible_operators.push_back(op);
            }
        }
    } else if (sort->isReal()) {
        // 实数操作符
        for (const auto& op : available_operators) {
            if (op == SMTLIBParser::NODE_KIND::NT_ADD ||
                op == SMTLIBParser::NODE_KIND::NT_SUB ||
                op == SMTLIBParser::NODE_KIND::NT_MUL ||
                op == SMTLIBParser::NODE_KIND::NT_DIV_REAL ||
                op == SMTLIBParser::NODE_KIND::NT_NEG ||
                op == SMTLIBParser::NODE_KIND::NT_POW ||
                op == SMTLIBParser::NODE_KIND::NT_SQRT ||
                op == SMTLIBParser::NODE_KIND::NT_EXP ||
                op == SMTLIBParser::NODE_KIND::NT_LOG ||
                op == SMTLIBParser::NODE_KIND::NT_LN ||
                op == SMTLIBParser::NODE_KIND::NT_SIN ||
                op == SMTLIBParser::NODE_KIND::NT_COS ||
                op == SMTLIBParser::NODE_KIND::NT_TAN ||
                op == SMTLIBParser::NODE_KIND::NT_ASIN ||
                op == SMTLIBParser::NODE_KIND::NT_ACOS ||
                op == SMTLIBParser::NODE_KIND::NT_ATAN) {
                compatible_operators.push_back(op);
            }
        }
    } else if (sort->isBool()) {
        // 布尔操作符
        for (const auto& op : available_operators) {
            if (op == SMTLIBParser::NODE_KIND::NT_AND ||
                op == SMTLIBParser::NODE_KIND::NT_OR ||
                op == SMTLIBParser::NODE_KIND::NT_NOT) {
                compatible_operators.push_back(op);
            }
        }
    }
    
    // 从可用操作符中随机选择
    std::vector<SMTLIBParser::NODE_KIND> available_ops;
    for (const auto& op : compatible_operators) {
        // 只有在操作符可用的情况下才添加
        if (available_operators.find(op) != available_operators.end()) {
            available_ops.push_back(op);
        }
    }
    
    // 如果没有可用的操作符，返回变量或常量
    if (available_ops.empty()) {
        std::cout << "Warning: No available operators for the selected sort. Defaulting to variable or constant." << std::endl;
        return generateArithmeticExpression(0, sort);
    }
    
    // 随机选择一个操作符
    std::uniform_int_distribution<size_t> op_dist(0, available_ops.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = available_ops[op_dist(rng)];
    
    // 根据选择的操作符创建表达式
    std::shared_ptr<SMTLIBParser::DAGNode> result;
    
    switch (selected_op) {
        // 一元操作符
        case SMTLIBParser::NODE_KIND::NT_NEG:
        case SMTLIBParser::NODE_KIND::NT_NOT:
        case SMTLIBParser::NODE_KIND::NT_SQRT:
        case SMTLIBParser::NODE_KIND::NT_EXP:
        case SMTLIBParser::NODE_KIND::NT_LOG:
        case SMTLIBParser::NODE_KIND::NT_LN:
        case SMTLIBParser::NODE_KIND::NT_SIN:
        case SMTLIBParser::NODE_KIND::NT_COS:
        case SMTLIBParser::NODE_KIND::NT_TAN:
        case SMTLIBParser::NODE_KIND::NT_ASIN:
        case SMTLIBParser::NODE_KIND::NT_ACOS:
        case SMTLIBParser::NODE_KIND::NT_ATAN: {
            // 为一元操作符创建子表达式
            auto child = generateExpression(depth - 1, sort);
            result = parser->mkOper(sort, selected_op, child);
            
            // 计算操作结果并存储
            if (child->isVar() && variable_values.find(child->getName()) != variable_values.end()) {
                auto child_value = variable_values[child->getName()];
                
                // TODO: 根据操作符计算结果
                // 此处简化处理，仅针对部分操作符计算结果
                // 在实际实现中应根据不同的操作符进行更详细的计算
                
                // 例如，对于布尔操作NOT
                if (selected_op == SMTLIBParser::NODE_KIND::NT_NOT && child_value->isCBool()) {
                    bool value = !child_value->isTrue();
                    variable_values[result->getName()] = value ? parser->mkTrue() : parser->mkFalse();
                }
            }
            break;
        }
        
        // 二元操作符
        case SMTLIBParser::NODE_KIND::NT_ADD:
        case SMTLIBParser::NODE_KIND::NT_SUB:
        case SMTLIBParser::NODE_KIND::NT_MUL:
        case SMTLIBParser::NODE_KIND::NT_DIV_INT:
        case SMTLIBParser::NODE_KIND::NT_DIV_REAL:
        case SMTLIBParser::NODE_KIND::NT_MOD:
        case SMTLIBParser::NODE_KIND::NT_POW:
        case SMTLIBParser::NODE_KIND::NT_AND:
        case SMTLIBParser::NODE_KIND::NT_OR: {
            // 为二元操作符创建子表达式
            auto left = generateExpression(depth - 1, sort);
            auto right = generateExpression(depth - 1, sort);
            result = parser->mkOper(sort, selected_op, left, right);
            
            // 计算操作结果并存储
            bool left_has_value = left->isVar() && variable_values.find(left->getName()) != variable_values.end();
            bool right_has_value = right->isVar() && variable_values.find(right->getName()) != variable_values.end();
            
            if (left_has_value && right_has_value) {
                auto left_value = variable_values[left->getName()];
                auto right_value = variable_values[right->getName()];
                
                // TODO: 根据操作符计算结果
                // 此处简化处理，仅针对部分操作符计算结果
                
                // 例如，对于布尔操作AND
                if (selected_op == SMTLIBParser::NODE_KIND::NT_AND && 
                    left_value->isCBool() && right_value->isCBool()) {
                    bool value = left_value->isTrue() && right_value->isTrue();
                    variable_values[result->getName()] = value ? parser->mkTrue() : parser->mkFalse();
                }
            }
            break;
        }
        
        default:
            // 对于不支持的操作符，创建变量或常量
            result = generateVariable(sort);
            break;
    }
    
    return result;
}

// 随机生成一个约束
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateConstraint(int depth) {
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    double random_val = dist(rng);
    
    // 确保至少有一些变量可用
    if (variables.empty()) {
        // 如果没有变量，创建一个简单约束（应该不会发生，因为在generateSMTLIB2File中已经预先创建了变量）
        return parser->mkTrue();
    }
    
    // 选择约束类型：布尔表达式或关系表达式
    if (random_val < 0.3) {
        // 生成复合布尔表达式作为约束
        return generateBooleanConstraint(depth);
    } else {
        // 生成关系表达式作为约束
        return generateRelationalConstraint(depth);
    }
}

// 生成关系表达式约束
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateRelationalConstraint(int depth) {
    // 收集所有可用的比较运算符
    std::vector<SMTLIBParser::NODE_KIND> comparison_ops;
    for (const auto& op : available_operators) {
        if (op == SMTLIBParser::NODE_KIND::NT_EQ ||
            op == SMTLIBParser::NODE_KIND::NT_LE ||
            op == SMTLIBParser::NODE_KIND::NT_LT ||
            op == SMTLIBParser::NODE_KIND::NT_GE ||
            op == SMTLIBParser::NODE_KIND::NT_GT) {
            comparison_ops.push_back(op);
        }
    }
    
    // 如果没有比较运算符，则使用等号
    if (comparison_ops.empty()) {
        comparison_ops.push_back(SMTLIBParser::NODE_KIND::NT_EQ);
    }
    
    // 随机选择一个比较运算符
    std::uniform_int_distribution<size_t> op_dist(0, comparison_ops.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = comparison_ops[op_dist(rng)];
    
    // 确定操作数的类型
    std::shared_ptr<SMTLIBParser::Sort> operand_sort;
    if (logic == "QF_LIA") {
        operand_sort = SMTLIBParser::INT_SORT;
    } else if (logic == "NTA") {
        operand_sort = SMTLIBParser::REAL_SORT;
    } else {
        // 默认使用整数类型
        operand_sort = SMTLIBParser::INT_SORT;
    }
    
    // 随机决定是使用简单变量还是生成复杂表达式
    std::uniform_real_distribution<double> expr_dist(0.0, 1.0);
    double expr_choice = expr_dist(rng);
    
    std::shared_ptr<SMTLIBParser::DAGNode> left, right;
    if (expr_choice < 0.6 && depth > 1) {
        // 生成复杂表达式
        left = generateArithmeticExpression(depth - 1, operand_sort);
        right = generateArithmeticExpression(depth - 1, operand_sort);
    } else {
        // 选择变量
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> compatible_vars;
        for (const auto& var : variables) {
            if (var->getSort()->isEqTo(operand_sort)) {
                compatible_vars.push_back(var);
            }
        }
        
        if (compatible_vars.empty()) {
            // 如果没有找到兼容的变量，生成常量
            std::uniform_int_distribution<int> val_dist(int_min_value, int_max_value);
            left = parser->mkConstInt(val_dist(rng));
            right = parser->mkConstInt(val_dist(rng));
        } else {
            // 从兼容变量中随机选择
            std::uniform_int_distribution<size_t> var_dist(0, compatible_vars.size() - 1);
            left = compatible_vars[var_dist(rng)];
            
            // 50%的概率，右边是变量或常量
            if (expr_dist(rng) < 0.5) {
                right = compatible_vars[var_dist(rng)];
            } else {
                // 生成一个随机常量
                std::uniform_int_distribution<int> val_dist(int_min_value, int_max_value);
                right = parser->mkConstInt(val_dist(rng));
            }
        }
    }
    
    // 创建比较表达式
    auto result = parser->mkOper(SMTLIBParser::BOOL_SORT, selected_op, left, right);
    
    return result;
}

// 生成布尔表达式约束
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateBooleanConstraint(int depth) {
    if (depth <= 0) {
        // 如果深度为0，返回一个变量或常量
        if (!variables.empty()) {
            std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> bool_vars;
            for (const auto& var : variables) {
                if (var->getSort()->isBool()) {
                    bool_vars.push_back(var);
                }
            }
            
            if (!bool_vars.empty()) {
                std::uniform_int_distribution<size_t> var_dist(0, bool_vars.size() - 1);
                return bool_vars[var_dist(rng)];
            }
        }
        
        // 50%概率返回true或false
        std::uniform_int_distribution<int> bool_dist(0, 1);
        return bool_dist(rng) == 1 ? parser->mkTrue() : parser->mkFalse();
    }
    
    // 选择布尔操作符
    std::vector<int> operator_types = {0, 1, 2}; // 0: NOT, 1: AND, 2: OR
    std::uniform_int_distribution<size_t> op_dist(0, operator_types.size() - 1);
    int op_type = operator_types[op_dist(rng)];
    
    if (op_type == 0) {
        // NOT 操作符
        auto child = generateBooleanConstraint(depth - 1);
        return parser->mkNot(child);
    } else if (op_type == 1) {
        // AND 操作符
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        int num_children = std::uniform_int_distribution<int>(2, 3)(rng);
        for (int i = 0; i < num_children; ++i) {
            children.push_back(generateBooleanConstraint(depth - 1));
        }
        return parser->mkAnd(children);
    } else {
        // OR 操作符
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        int num_children = std::uniform_int_distribution<int>(2, 3)(rng);
        for (int i = 0; i < num_children; ++i) {
            children.push_back(generateBooleanConstraint(depth - 1));
        }
        return parser->mkOr(children);
    }
}

// 生成算术表达式
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateArithmeticExpression(int depth, const std::shared_ptr<SMTLIBParser::Sort>& sort) {
    if (depth <= 0) {
        // 如果深度为0，返回一个变量或常量
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> compatible_vars;
        for (const auto& var : variables) {
            if (var->getSort()->isEqTo(sort)) {
                compatible_vars.push_back(var);
            }
        }
        
        if (!compatible_vars.empty()) {
            std::uniform_int_distribution<size_t> var_dist(0, compatible_vars.size() - 1);
            return compatible_vars[var_dist(rng)];
        }
        
        // 如果没有兼容的变量，生成一个常量
        if (sort->isInt()) {
            std::uniform_int_distribution<int> val_dist(int_min_value, int_max_value);
            return parser->mkConstInt(val_dist(rng));
        } else if (sort->isReal()) {
            std::uniform_real_distribution<double> val_dist(real_min_value, real_max_value);
            return parser->mkConstReal(val_dist(rng));
        } else {
            // 默认返回整数
            std::uniform_int_distribution<int> val_dist(int_min_value, int_max_value);
            return parser->mkConstInt(val_dist(rng));
        }
    }
    
    // 选择算术操作符
    std::vector<SMTLIBParser::NODE_KIND> compatible_operators;
    
    // 检查是否支持NTA (非线性超越函数算术)
    bool supports_nta = (logic == "NTA" || logic == "QF_NTA");
    
    if (sort->isInt()) {
        // 整数操作符
        compatible_operators = {
            SMTLIBParser::NODE_KIND::NT_ADD,
            SMTLIBParser::NODE_KIND::NT_SUB,
            SMTLIBParser::NODE_KIND::NT_MUL,
            SMTLIBParser::NODE_KIND::NT_DIV_INT,
            SMTLIBParser::NODE_KIND::NT_MOD
        };
    } else if (sort->isReal()) {
        // 实数基本操作符
        compatible_operators = {
            SMTLIBParser::NODE_KIND::NT_ADD,
            SMTLIBParser::NODE_KIND::NT_SUB,
            SMTLIBParser::NODE_KIND::NT_MUL,
            SMTLIBParser::NODE_KIND::NT_DIV_REAL
        };
        
        // 如果支持NTA，添加超越函数操作符
        if (supports_nta) {
            std::vector<SMTLIBParser::NODE_KIND> transcendental_ops = {
                SMTLIBParser::NODE_KIND::NT_SQRT,
                SMTLIBParser::NODE_KIND::NT_EXP,
                SMTLIBParser::NODE_KIND::NT_LOG,
                SMTLIBParser::NODE_KIND::NT_LN,
                SMTLIBParser::NODE_KIND::NT_SIN,
                SMTLIBParser::NODE_KIND::NT_COS,
                SMTLIBParser::NODE_KIND::NT_TAN,
                SMTLIBParser::NODE_KIND::NT_POW,
                SMTLIBParser::NODE_KIND::NT_ASIN,
                SMTLIBParser::NODE_KIND::NT_ACOS,
                SMTLIBParser::NODE_KIND::NT_ATAN
            };
            
            compatible_operators.insert(compatible_operators.end(), 
                                       transcendental_ops.begin(), 
                                       transcendental_ops.end());
        }
    } else {
        // 默认操作符
        compatible_operators = {
            SMTLIBParser::NODE_KIND::NT_ADD,
            SMTLIBParser::NODE_KIND::NT_SUB
        };
    }
    
    // 从可用操作符中随机选择
    std::vector<SMTLIBParser::NODE_KIND> available_ops;
    for (const auto& op : compatible_operators) {
        // 只有在操作符可用的情况下才添加
        if (available_operators.find(op) != available_operators.end()) {
            available_ops.push_back(op);
        }
    }
    
    // 如果没有可用的操作符，返回变量或常量
    if (available_ops.empty()) {
        std::cout << "Warning: No available operators for the selected sort. Defaulting to variable or constant." << std::endl;
        return generateArithmeticExpression(0, sort);
    }
    
    // 随机选择一个操作符
    std::uniform_int_distribution<size_t> op_dist(0, available_ops.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = available_ops[op_dist(rng)];
    
    // 创建表达式
    std::shared_ptr<SMTLIBParser::DAGNode> result;
    
    // 检查操作符需要的参数数量
    size_t param_count = 0;
    bool is_unary = false;
    bool is_binary = false;
    
    // 单目操作符
    if (selected_op == SMTLIBParser::NODE_KIND::NT_NEG ||
        selected_op == SMTLIBParser::NODE_KIND::NT_SQRT ||
        selected_op == SMTLIBParser::NODE_KIND::NT_EXP ||
        selected_op == SMTLIBParser::NODE_KIND::NT_LOG ||
        selected_op == SMTLIBParser::NODE_KIND::NT_LN ||
        selected_op == SMTLIBParser::NODE_KIND::NT_SIN ||
        selected_op == SMTLIBParser::NODE_KIND::NT_COS ||
        selected_op == SMTLIBParser::NODE_KIND::NT_TAN ||
        selected_op == SMTLIBParser::NODE_KIND::NT_ASIN ||
        selected_op == SMTLIBParser::NODE_KIND::NT_ACOS ||
        selected_op == SMTLIBParser::NODE_KIND::NT_ATAN) {
        is_unary = true;
        param_count = 1;
    }
    // 二目操作符
    else if (selected_op == SMTLIBParser::NODE_KIND::NT_DIV_INT ||
             selected_op == SMTLIBParser::NODE_KIND::NT_DIV_REAL ||
             selected_op == SMTLIBParser::NODE_KIND::NT_MOD ||
             selected_op == SMTLIBParser::NODE_KIND::NT_POW) {
        is_binary = true;
        param_count = 2;
    }
    // 可变参数操作符
    else if (selected_op == SMTLIBParser::NODE_KIND::NT_ADD ||
             selected_op == SMTLIBParser::NODE_KIND::NT_MUL) {
        param_count = std::uniform_int_distribution<size_t>(2, 3)(rng);
    }
    // SUB默认为二目操作符
    else if (selected_op == SMTLIBParser::NODE_KIND::NT_SUB) {
        param_count = 2;
    }
    // 默认参数数量
    else {
        param_count = 2;
    }
    
    // 根据参数数量生成子表达式
    if (is_unary) {
        auto child = generateArithmeticExpression(depth - 1, sort);
        
        // 针对一些特殊函数检查参数约束
        if ((selected_op == SMTLIBParser::NODE_KIND::NT_SQRT ||
             selected_op == SMTLIBParser::NODE_KIND::NT_LOG ||
             selected_op == SMTLIBParser::NODE_KIND::NT_LN ||
             selected_op == SMTLIBParser::NODE_KIND::NT_ASIN ||
             selected_op == SMTLIBParser::NODE_KIND::NT_ACOS) && 
            depth > 1) {
            // 对于需要非负数/在特定范围内的参数的函数，可以添加加法防止负数
            if (child->isConst() && child->getName()[0] == '-') {
                // 如果是负常量，转换为正数
                if (sort->isInt()) {
                    std::uniform_int_distribution<int> val_dist(1, 10);
                    child = parser->mkConstInt(val_dist(rng));
                } else {
                    std::uniform_real_distribution<double> val_dist(0.1, 10.0);
                    child = parser->mkConstReal(val_dist(rng));
                }
            }
        }
        
        result = parser->mkOper(sort, selected_op, child);
    } else if (is_binary) {
        auto left = generateArithmeticExpression(depth - 1, sort);
        auto right = generateArithmeticExpression(depth - 1, sort);
        
        // 处理除法和取模操作符，确保除数不为0
        if ((selected_op == SMTLIBParser::NODE_KIND::NT_DIV_INT ||
             selected_op == SMTLIBParser::NODE_KIND::NT_DIV_REAL ||
             selected_op == SMTLIBParser::NODE_KIND::NT_MOD) && 
            right->isConst() && right->getName() == "0") {
            // 如果除数是0，替换为非0值
            if (sort->isInt()) {
                std::uniform_int_distribution<int> val_dist(1, 10);
                right = parser->mkConstInt(val_dist(rng));
            } else {
                std::uniform_real_distribution<double> val_dist(0.1, 10.0);
                right = parser->mkConstReal(val_dist(rng));
            }
        }
        
        result = parser->mkOper(sort, selected_op, left, right);
    } else {
        // 处理可变参数操作符
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        for (size_t i = 0; i < param_count; ++i) {
            children.push_back(generateArithmeticExpression(depth - 1, sort));
        }
        
        if (selected_op == SMTLIBParser::NODE_KIND::NT_ADD) {
            result = parser->mkAdd(children);
        } else if (selected_op == SMTLIBParser::NODE_KIND::NT_MUL) {
            result = parser->mkMul(children);
        } else if (selected_op == SMTLIBParser::NODE_KIND::NT_SUB) {
            result = parser->mkSub(children);
        } else {
            // 默认情况下使用通用操作符构造函数
            result = parser->mkOper(sort, selected_op, children);
        }
    }
    
    return result;
}

// 收集表达式中的所有变量并添加到variables列表中
void Generator::collectVariables(const std::shared_ptr<SMTLIBParser::DAGNode>& node) {
    if (!node) return;
    
    // 如果变量列表已经满了，直接返回
    if (variables.size() >= static_cast<size_t>(next_var_id)) {
        return;
    }
    
    // 如果是变量节点
    if (node->isVar()) {
        // 检查变量是否已在变量列表中
        bool found = false;
        for (const auto& var : variables) {
            if (var->getName() == node->getName()) {
                found = true;
                break;
            }
        }
        
        // 如果没找到，则添加到变量列表
        if (!found) {
            variables.push_back(node);
            
            // 如果变量没有对应的值，生成一个随机值
            if (variable_values.find(node->getName()) == variable_values.end()) {
                if (node->getSort()->isInt()) {
                    std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
                    int value = int_dist(rng);
                    auto value_node = parser->mkConstInt(value);
                    variable_values[node->getName()] = value_node;
                    // 添加到模型中
                    model.add(node->getName(), value_node);
                } else if (node->getSort()->isReal()) {
                    std::uniform_real_distribution<double> real_dist(real_min_value, real_max_value);
                    double value = real_dist(rng);
                    auto value_node = parser->mkConstReal(value);
                    variable_values[node->getName()] = value_node;
                    // 添加到模型中
                    model.add(node->getName(), value_node);
                } else if (node->getSort()->isBool()) {
                    std::uniform_int_distribution<int> bool_dist(0, 1);
                    bool value = bool_dist(rng) == 1;
                    auto value_node = value ? parser->mkTrue() : parser->mkFalse();
                    variable_values[node->getName()] = value_node;
                    // 添加到模型中
                    model.add(node->getName(), value_node);
                }
            }
        }
    }
    
    // 递归处理子节点
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        collectVariables(node->getChild(i));
    }
}

// 生成模型文件
void Generator::generateModelFile(const std::string& model_path) {
    // 创建模型文件目录（如果需要）
    std::filesystem::path model_file_path(model_path);
    auto parent_path = model_file_path.parent_path();
    if (!parent_path.empty() && !std::filesystem::exists(parent_path)) {
        try {
            std::filesystem::create_directories(parent_path);
        } catch (const std::exception& e) {
            std::cerr << "Error: Failed to create model file directory: " << parent_path << std::endl;
            std::cerr << "  " << e.what() << std::endl;
            return;
        }
    }
    
    std::ofstream outfile(model_path);
    if (!outfile.is_open()) {
        std::cerr << "Error: Unable to open model file: " << model_path << std::endl;
        return;
    }
    
    // 直接将模型输出到文件
    try {
        outfile << model.toString();
        outfile.close();
        std::cout << "Model file generated: " << model_path << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Error: Failed to generate model file: " << e.what() << std::endl;
    }
}

// 生成SMTLIB2文件
void Generator::generateSMTLIB2File(const std::string& output_path, int num_vars, int num_constraints) {
    // 清空现有数据
    variables.clear();
    variable_values.clear();
    next_var_id = 0;
    // 清空模型
    model = SMTLIBParser::Model();
    
    // 创建输出文件
    std::ofstream outfile(output_path);
    if (!outfile.is_open()) {
        std::cerr << "Error: Unable to open output file: " << output_path << std::endl;
        return;
    }
    
    // 写入头部
    outfile << "; This file was automatically generated by SMTLIBGenerator\n";
    
    // 将系统时间转换为字符串并输出
    auto now = std::chrono::system_clock::now();
    auto time_t_now = std::chrono::system_clock::to_time_t(now);
    outfile << "; Generation time: " << std::put_time(std::localtime(&time_t_now), "%Y-%m-%d %H:%M:%S") << "\n\n";
    
    // 设置逻辑
    outfile << "(set-logic " << logic << ")\n\n";
    
    // 预先创建指定数量的变量
    std::shared_ptr<SMTLIBParser::Sort> var_sort;
    if (logic == "QF_LIA") {
        var_sort = SMTLIBParser::INT_SORT;
    } else if (logic == "QF_NTA") {
        var_sort = SMTLIBParser::REAL_SORT;
    } else {
        // 默认使用整数类型
        var_sort = SMTLIBParser::INT_SORT;
    }
    
    // 确保生成的变量数量不超过指定的数量
    for (int i = 0; i < num_vars; ++i) {
        // 强制创建新变量，而不是复用已有变量或创建常量
        std::string var_name = "x" + std::to_string(next_var_id++);
        auto var = parser->mkVar(var_sort, var_name);
        
        // 生成随机值
        if (var_sort->isInt()) {
            std::uniform_int_distribution<int> int_dist(int_min_value, int_max_value);
            int value = int_dist(rng);
            auto value_node = parser->mkConstInt(value);
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var, value_node);
        } else if (var_sort->isReal()) {
            std::uniform_real_distribution<double> real_dist(real_min_value, real_max_value);
            double value = real_dist(rng);
            auto value_node = parser->mkConstReal(value);
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var, value_node);
        } else if (var_sort->isBool()) {
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            auto value_node = value ? parser->mkTrue() : parser->mkFalse();
            variable_values[var_name] = value_node;
            // 添加到模型中
            model.add(var, value_node);
        }
        
        variables.push_back(var);
    }
    
    // 生成约束
    std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> constraints;
    for (int i = 0; i < num_constraints; ++i) {
        try {
            // 使用更高的深度生成更复杂的约束
            auto constraint = generateConstraint(4); // 增加深度到4
            
            // 确保不是简单的true/false约束
            if (constraint->isTrue() || constraint->isFalse()) {
                // 如果是简单常量，重新生成
                i--; // 重试这个约束
                continue;
            }
            
            constraints.push_back(constraint);
            
            std::cout << "constraint " << i << " generated" << std::endl;
            std::cout << SMTLIBParser::dumpSMTLIB2(constraint) << std::endl;
        } catch (const std::exception& e) {
            std::cerr << "Warning: Failed to generate constraint " << i << ": " << e.what() << std::endl;
            // 生成一个简单的满足约束替代
            if (i == 0) {
                // 确保至少有一个可满足的约束
                auto var = variables[0]; // 使用第一个变量
                if (var->getSort()->isInt()) {
                    // 创建一个总是成立的约束，如 x >= x
                    auto constraint = parser->mkGe(var, var);
                    constraints.push_back(constraint);
                    std::cout << "constraint " << i << " generated (fallback)" << std::endl;
                    std::cout << SMTLIBParser::dumpSMTLIB2(constraint) << std::endl;
                } else if (var->getSort()->isBool()) {
                    // 创建 x OR (NOT x)
                    auto not_var = parser->mkNot(var);
                    std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children = {var, not_var};
                    auto constraint = parser->mkOr(children);
                    constraints.push_back(constraint);
                    std::cout << "constraint " << i << " generated (fallback)" << std::endl;
                    std::cout << SMTLIBParser::dumpSMTLIB2(constraint) << std::endl;
                } else {
                    // 默认创建true
                    auto constraint = parser->mkTrue();
                    constraints.push_back(constraint);
                    std::cout << "constraint " << i << " generated (fallback)" << std::endl;
                    std::cout << SMTLIBParser::dumpSMTLIB2(constraint) << std::endl;
                }
            } else {
                // 非第一个约束可以是true
                auto constraint = parser->mkTrue();
                constraints.push_back(constraint);
                std::cout << "constraint " << i << " generated (fallback)" << std::endl;
                std::cout << SMTLIBParser::dumpSMTLIB2(constraint) << std::endl;
            }
        }
    }
    
    // 声明变量
    outfile << "; Variable declarations\n";
    for (const auto& var : variables) {
        outfile << "(declare-const " << var->getName() << " ";
        
        // 根据变量类型输出类型名称
        if (var->getSort()->isInt()) {
            outfile << "Int";
        } else if (var->getSort()->isReal()) {
            outfile << "Real";
        } else if (var->getSort()->isBool()) {
            outfile << "Bool";
        } else {
            // 未知类型默认为Int
            outfile << "Int";
        }
        
        outfile << ")\n";
    }
    outfile << "\n";
    
    // 输出约束
    outfile << "; Constraints\n";
    for (int i = 0; i < static_cast<int>(constraints.size()); ++i) {
        auto constraint = constraints[i];
        
        // 输出约束
        outfile << "(assert ";
        outfile << SMTLIBParser::dumpSMTLIB2(constraint);
        outfile << ")\n";
    }
    
    // 添加查询命令
    outfile << "\n; Check satisfiability\n";
    outfile << "(check-sat)\n";
    outfile << "(exit)\n";
    
    outfile.close();
    std::cout << "Successfully generated SMTLIB2 file: " << output_path << std::endl;
    
    // 生成模型文件
    std::filesystem::path output_file_path(output_path);
    std::string model_path;
    
    if (output_file_path.parent_path().empty()) {
        // 如果输出文件在当前目录，则模型文件也生成在当前目录
        model_path = output_file_path.stem().string() + ".model";
    } else {
        // 否则生成在与输出文件相同的目录
        model_path = output_file_path.parent_path().string() + "/" +
                     output_file_path.stem().string() + ".model";
    }
    
    try {
        generateModelFile(model_path);
        std::cout << "Model file generated as: " << model_path << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Warning: Failed to generate model file: " << e.what() << std::endl;
    }
}

} // namespace SMTLIBGenerator
