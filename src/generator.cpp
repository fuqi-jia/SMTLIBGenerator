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

namespace SMTLIBGenerator {

// 构造函数
Generator::Generator(unsigned int seed, double decay_prob) 
    : rng(seed), decay_probability(decay_prob), logic("QF_LIA") {
    // 初始化解析器
    parser = std::make_shared<SMTLIBParser::Parser>();
    
    // 默认加载QF_LIA理论
    loadTheory("QF_LIA");
}

// 设置逻辑类型
void Generator::setLogic(const std::string& logic_name) {
    logic = logic_name;
    // 清空现有的操作符
    available_operators.clear();
    // 加载对应的理论
    loadTheory(logic);
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
        result = std::make_shared<SMTLIBParser::DAGNode>(sort, SMTLIBParser::NODE_KIND::NT_VAR, var_name);
        
        // 生成一个随机值并保存
        if (sort->isInt()) {
            // 整数变量
            std::uniform_int_distribution<int> int_dist(-100, 100);
            int value = int_dist(rng);
            auto value_node = std::make_shared<SMTLIBParser::DAGNode>(std::to_string(value));
            
            // 保存变量和它的值
            variable_values[var_name] = value_node;
            variables.push_back(result);
        } else if (sort->isReal()) {
            // 实数变量
            std::uniform_real_distribution<double> real_dist(-100.0, 100.0);
            double value = real_dist(rng);
            
            // 将浮点数转换为分数形式
            std::stringstream ss;
            ss << value;
            auto value_node = std::make_shared<SMTLIBParser::DAGNode>(ss.str());
            
            // 保存变量和它的值
            variable_values[var_name] = value_node;
            variables.push_back(result);
        } else if (sort->isBool()) {
            // 布尔变量
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            
            auto value_node = value ? parser->mkTrue() : parser->mkFalse();
            
            // 保存变量和它的值
            variable_values[var_name] = value_node;
            variables.push_back(result);
        } else {
            // 对于不支持的类型，创建默认变量
            // 默认使用整数值
            std::uniform_int_distribution<int> int_dist(-100, 100);
            int value = int_dist(rng);
            auto value_node = std::make_shared<SMTLIBParser::DAGNode>(std::to_string(value));
            
            variable_values[var_name] = value_node;
            variables.push_back(result);
        }
    } else {
        // 创建一个常量
        if (sort->isInt()) {
            // 整数常量
            std::uniform_int_distribution<int> int_dist(-100, 100);
            int value = int_dist(rng);
            result = std::make_shared<SMTLIBParser::DAGNode>(std::to_string(value));
        } else if (sort->isReal()) {
            // 实数常量
            std::uniform_real_distribution<double> real_dist(-100.0, 100.0);
            double value = real_dist(rng);
            
            // 将浮点数转换为分数形式
            std::stringstream ss;
            ss << value;
            result = std::make_shared<SMTLIBParser::DAGNode>(ss.str());
        } else if (sort->isBool()) {
            // 布尔常量
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            
            result = value ? parser->mkTrue() : parser->mkFalse();
        } else {
            // 对于不支持的类型，创建默认变量而不是常量
            std::string var_name = "x" + std::to_string(next_var_id++);
            result = std::make_shared<SMTLIBParser::DAGNode>(sort, SMTLIBParser::NODE_KIND::NT_VAR, var_name);
            
            // 保存默认值
            std::uniform_int_distribution<int> int_dist(-100, 100);
            int value = int_dist(rng);
            auto value_node = std::make_shared<SMTLIBParser::DAGNode>(std::to_string(value));
            
            variable_values[var_name] = value_node;
            variables.push_back(result);
        }
    }
    
    return result;
}

// 随机生成一个表达式节点
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateExpression(int depth, const std::shared_ptr<SMTLIBParser::Sort>& sort) {
    // 如果深度到达限制或随机衰减，则创建变量或常量
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    if (depth <= 0 || dist(rng) < decay_probability) {
        return generateVariable(sort);
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
    
    // 如果没有兼容的操作符，则创建变量或常量
    if (compatible_operators.empty()) {
        return generateVariable(sort);
    }
    
    // 随机选择一个操作符
    std::uniform_int_distribution<size_t> op_dist(0, compatible_operators.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = compatible_operators[op_dist(rng)];
    
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
    
    // 选择约束类型：布尔表达式或关系表达式
    if (random_val < 0.3 && !variables.empty()) {
        // 生成一个布尔表达式作为约束
        return generateExpression(depth, SMTLIBParser::BOOL_SORT);
    } else {
        // 生成一个关系表达式作为约束
        std::vector<SMTLIBParser::NODE_KIND> comparison_ops;
        
        // 收集所有可用的比较运算符
        for (const auto& op : available_operators) {
            if (op == SMTLIBParser::NODE_KIND::NT_EQ ||
                op == SMTLIBParser::NODE_KIND::NT_LE ||
                op == SMTLIBParser::NODE_KIND::NT_LT ||
                op == SMTLIBParser::NODE_KIND::NT_GE ||
                op == SMTLIBParser::NODE_KIND::NT_GT) {
                comparison_ops.push_back(op);
            }
        }
        
        // 如果没有比较运算符，则直接生成布尔表达式
        if (comparison_ops.empty()) {
            return generateExpression(depth, SMTLIBParser::BOOL_SORT);
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
        
        // 生成左右操作数
        auto left = generateExpression(depth - 1, operand_sort);
        auto right = generateExpression(depth - 1, operand_sort);
        
        // 创建比较表达式
        auto result = parser->mkOper(SMTLIBParser::BOOL_SORT, selected_op, left, right);
        
        // 计算比较结果并存储
        bool left_has_value = left->isVar() && variable_values.find(left->getName()) != variable_values.end();
        bool right_has_value = right->isVar() && variable_values.find(right->getName()) != variable_values.end();
        
        if (left_has_value && right_has_value) {
            auto left_value = variable_values[left->getName()];
            auto right_value = variable_values[right->getName()];
            
            // 根据比较运算符计算结果
            bool comparison_result = false;
            
            // 此处简化处理，实际应对不同类型的值进行更详细的计算
            if (left_value->isConst() && right_value->isConst()) {
                if (selected_op == SMTLIBParser::NODE_KIND::NT_EQ) {
                    // 相等比较
                    comparison_result = (left_value->getName() == right_value->getName());
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_LE) {
                    // 小于等于比较
                    if (left_value->isCInt() && right_value->isCInt()) {
                        comparison_result = (left_value->toInt() <= right_value->toInt());
                    } else if (left_value->isCReal() && right_value->isCReal()) {
                        comparison_result = (left_value->toReal() <= right_value->toReal());
                    }
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_LT) {
                    // 小于比较
                    if (left_value->isCInt() && right_value->isCInt()) {
                        comparison_result = (left_value->toInt() < right_value->toInt());
                    } else if (left_value->isCReal() && right_value->isCReal()) {
                        comparison_result = (left_value->toReal() < right_value->toReal());
                    }
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_GE) {
                    // 大于等于比较
                    if (left_value->isCInt() && right_value->isCInt()) {
                        comparison_result = (left_value->toInt() >= right_value->toInt());
                    } else if (left_value->isCReal() && right_value->isCReal()) {
                        comparison_result = (left_value->toReal() >= right_value->toReal());
                    }
                } else if (selected_op == SMTLIBParser::NODE_KIND::NT_GT) {
                    // 大于比较
                    if (left_value->isCInt() && right_value->isCInt()) {
                        comparison_result = (left_value->toInt() > right_value->toInt());
                    } else if (left_value->isCReal() && right_value->isCReal()) {
                        comparison_result = (left_value->toReal() > right_value->toReal());
                    }
                }
            }
            
            variable_values[result->getName()] = comparison_result ? parser->mkTrue() : parser->mkFalse();
        }
        
        return result;
    }
}

// 收集表达式中的所有变量并添加到variables列表中
void Generator::collectVariables(const std::shared_ptr<SMTLIBParser::DAGNode>& node) {
    if (!node) return;
    
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
        
        // 如果没找到，添加到变量列表
        if (!found) {
            variables.push_back(node);
            
            // 如果变量没有对应的值，生成一个随机值
            if (variable_values.find(node->getName()) == variable_values.end()) {
                if (node->getSort()->isInt()) {
                    std::uniform_int_distribution<int> int_dist(-100, 100);
                    int value = int_dist(rng);
                    auto value_node = std::make_shared<SMTLIBParser::DAGNode>(std::to_string(value));
                    variable_values[node->getName()] = value_node;
                } else if (node->getSort()->isReal()) {
                    std::uniform_real_distribution<double> real_dist(-100.0, 100.0);
                    double value = real_dist(rng);
                    std::stringstream ss;
                    ss << value;
                    auto value_node = std::make_shared<SMTLIBParser::DAGNode>(ss.str());
                    variable_values[node->getName()] = value_node;
                } else if (node->getSort()->isBool()) {
                    std::uniform_int_distribution<int> bool_dist(0, 1);
                    bool value = bool_dist(rng) == 1;
                    auto value_node = value ? parser->mkTrue() : parser->mkFalse();
                    variable_values[node->getName()] = value_node;
                }
            }
        }
    }
    
    // 递归处理子节点
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        collectVariables(node->getChild(i));
    }
}

// 生成SMTLIB2文件
void Generator::generateSMTLIB2File(const std::string& output_path, int num_vars, int num_constraints) {
    // 清空现有数据
    variables.clear();
    variable_values.clear();
    next_var_id = 0;
    
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
    } else if (logic == "NTA") {
        var_sort = SMTLIBParser::REAL_SORT;
    } else {
        // 默认使用整数类型
        var_sort = SMTLIBParser::INT_SORT;
    }
    
    for (int i = 0; i < num_vars; ++i) {
        generateVariable(var_sort);
    }
    
    // 生成约束
    std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> constraints;
    for (int i = 0; i < num_constraints; ++i) {
        auto constraint = generateConstraint(3); // 深度限制为3
        constraints.push_back(constraint);
        
        // 收集约束中的所有变量
        collectVariables(constraint);
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
    for (int i = 0; i < num_constraints; ++i) {
        auto constraint = constraints[i];
        
        // 输出约束
        outfile << "(assert ";
        outfile << SMTLIBParser::dumpSMTLIB2(constraint);
        outfile << ")\n";
        
        std::cout << "constraint " << i << " generated" << std::endl;
        std::cout << SMTLIBParser::dumpSMTLIB2(constraint) << std::endl;
    }
    
    // 添加查询命令
    outfile << "\n; Check satisfiability\n";
    outfile << "(check-sat)\n";
    outfile << "(exit)\n";
    
    outfile.close();
}

} // namespace SMTLIBGenerator
