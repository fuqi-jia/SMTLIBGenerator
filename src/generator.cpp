#include "generator.h"
#include "theories/QF_NTA.h"
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
    : rng(seed), decay_probability(decay_prob), logic("QF_LIA"), model(std::make_shared<SMTLIBParser::Model>()) {
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

// 设置约束生成深度
void Generator::setConstraintDepth(int depth) {
    // 确保深度至少为1
    constraint_depth = std::max(1, depth);
}

// 设置逻辑类型
void Generator::setLogic(const std::string& logic_name) {
    logic = logic_name;
    // 清空现有的操作符
    available_operators.clear();
    bool_operators.clear();
    comp_operators.clear();
    term_operators.clear();
    other_operators.clear();
    
    // 加载对应的理论
    if (logic == "QF_LIA") {
        loadTheory("QF_LIA");
    } else if (logic == "QF_NTA") {
        loadTheory("QF_NTA");
    } else {
        std::cerr << "Warning: Unsupported logic: " << logic_name << ". Using QF_LIA instead." << std::endl;
        loadTheory("QF_LIA"); // A默认值
    }
}

// 加载特定理论
void Generator::loadTheory(const std::string& theory_name) {
    if (theory_name == "QF_LIA") {
        bool_operators = getLIABoolOperators();
        comp_operators = getLIACompOperators();
        term_operators = getLIATermOperators();
        other_operators = getLIAOtherOperators();
    } else if (theory_name == "QF_NTA") {
        bool_operators = getNTABoolOperators();
        comp_operators = getNTACompOperators();
        term_operators = getNTATermOperators();
        other_operators = getNTAOtherOperators();
    } else {
        std::cerr << "Warning: Unsupported theory: " << theory_name << std::endl;
    }
    available_operators.insert(bool_operators.begin(), bool_operators.end());
    available_operators.insert(comp_operators.begin(), comp_operators.end());
    available_operators.insert(term_operators.begin(), term_operators.end());
    available_operators.insert(other_operators.begin(), other_operators.end());
}

// 随机生成一个常量
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateConstant(const std::string& logic_name) {
    if (logic_name == "QF_LIA") {
        return generateConstant(SMTLIBParser::INT_SORT);
    } else if (logic_name == "QF_NTA") {
        return generateConstant(SMTLIBParser::REAL_SORT);
    }
    return nullptr;
}

std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateConstant(const std::shared_ptr<SMTLIBParser::Sort>& sort) {
    if (sort->isInt()) {
        std::uniform_int_distribution<int> val_dist(int_min_value, int_max_value);
        return parser->mkConstInt(val_dist(rng));
    } else if (sort->isReal()) {
        std::uniform_real_distribution<double> val_dist(real_min_value, real_max_value);
        return parser->mkConstReal(val_dist(rng));
    } else if (sort->isBool()) {
        std::uniform_int_distribution<int> bool_dist(0, 1);
        return bool_dist(rng) == 1 ? parser->mkTrue() : parser->mkFalse();
    }
    return nullptr;
}

// 随机生成一个变量或常量
std::shared_ptr<SMTLIBParser::DAGNode> Generator::selectVariable(const std::shared_ptr<SMTLIBParser::Sort>& sort) {
    assert(!variables.empty());
    std::shared_ptr<SMTLIBParser::DAGNode> result;
    
    // 从现有变量中选择一个合适类型的变量
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
    
    return result;
}

// 随机生成一个约束
std::shared_ptr<SMTLIBParser::DAGNode> Generator::generateConstraint(int depth) {
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    double random_val = dist(rng);
    assert(!variables.empty());
    
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
    assert(!comp_operators.empty());
    std::vector<SMTLIBParser::NODE_KIND> comparison_ops(comp_operators.begin(), comp_operators.end());
    
    // 随机选择一个比较运算符
    std::uniform_int_distribution<size_t> op_dist(0, comparison_ops.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = comparison_ops[op_dist(rng)];
    
    // 确定操作数的类型
    std::shared_ptr<SMTLIBParser::Sort> operand_sort;
    operand_sort = default_var_sort;
    
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
        // TODO: how about BV/FP variables?
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> compatible_vars;
        for (const auto& var : variables) {
            if (var->getSort()->isEqTo(operand_sort)) {
                compatible_vars.push_back(var);
            }
        }
        
        if (compatible_vars.empty()) {
            // 如果没有找到兼容的变量，生成常量
            left = generateConstant(logic);
            right = generateConstant(logic);
        } else {
            // 从兼容变量中随机选择
            std::uniform_int_distribution<size_t> var_dist(0, compatible_vars.size() - 1);
            left = compatible_vars[var_dist(rng)];
            
            // 50%的概率，右边是变量或常量
            if (expr_dist(rng) < 0.5) {
                right = compatible_vars[var_dist(rng)];
            } else {
                // 生成一个随机常量
                right = generateConstant(logic);
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
    std::vector<SMTLIBParser::NODE_KIND> bool_ops(bool_operators.begin(), bool_operators.end());
    std::uniform_int_distribution<size_t> op_dist(0, bool_ops.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = bool_ops[op_dist(rng)];

    std::shared_ptr<SMTLIBParser::DAGNode> result;
    std::shared_ptr<SMTLIBParser::DAGNode> result_value;
    
    if (selected_op == SMTLIBParser::NODE_KIND::NT_NOT) {
        // NOT 操作符
        auto child = generateConstraint(depth - 1);
        result = parser->mkNot(child);
    } else if (selected_op == SMTLIBParser::NODE_KIND::NT_AND) {
        // AND 操作符
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        int num_children = std::uniform_int_distribution<int>(2, 5)(rng);
        for (int i = 0; i < num_children; ++i) {
            children.push_back(generateConstraint(depth - 1));
        }
        result = parser->mkAnd(children);
    } else if (selected_op == SMTLIBParser::NODE_KIND::NT_OR) {
        // OR 操作符
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        int num_children = std::uniform_int_distribution<int>(2, 3)(rng);
        for (int i = 0; i < num_children; ++i) {
            children.push_back(generateConstraint(depth - 1));
        }
        result = parser->mkOr(children);
    } else if (selected_op == SMTLIBParser::NODE_KIND::NT_XOR) {
        // XOR 操作符
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        int num_children = std::uniform_int_distribution<int>(2, 3)(rng);
        for (int i = 0; i < num_children; ++i) {
            children.push_back(generateConstraint(depth - 1));
        }
        result = parser->mkXor(children);
    } else if (selected_op == SMTLIBParser::NODE_KIND::NT_IMPLIES) {
        // IMPL 操作符
        auto left = generateBooleanConstraint(depth - 1);
        auto right = generateBooleanConstraint(depth - 1);
        result = parser->mkImplies(left, right);
    }
    return result;
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
        return generateConstant(sort);
    }
    
    // 选择算术操作符
    std::vector<SMTLIBParser::NODE_KIND> term_ops;
    term_ops.insert(term_ops.end(), term_operators.begin(), term_operators.end());
    
    // 如果没有可用的操作符，返回变量或常量
    if (term_ops.empty()) {
        std::cout << "Warning: No available operators for the selected sort. Defaulting to variable or constant." << std::endl;
        return generateArithmeticExpression(0, sort);
    }
    
    // 随机选择一个操作符
    std::uniform_int_distribution<size_t> op_dist(0, term_ops.size() - 1);
    SMTLIBParser::NODE_KIND selected_op = term_ops[op_dist(rng)];
    
    // 创建表达式
    std::shared_ptr<SMTLIBParser::DAGNode> result;
    
    // 检查操作符需要的参数数量
    size_t param_count = parser->getArity(selected_op);
    
    // 根据参数数量生成子表达式
    if (param_count == 1) {
        auto child = generateArithmeticExpression(depth - 1, sort);
        
        // 针对一些特殊函数检查参数约束
        if (selected_op == SMTLIBParser::NODE_KIND::NT_SQRT ||
             selected_op == SMTLIBParser::NODE_KIND::NT_LOG ||
             selected_op == SMTLIBParser::NODE_KIND::NT_LN) {
            // 对于需要非负数/在特定范围内的参数的函数，可以添加加法防止负数
            auto child_value = parser->toReal(parser->evaluate(child, model));
            if (child_value < 0) {
                // 如果是负数，转化为正数
                child = parser->mkNeg(child);
            }
        }
        else if(selected_op == SMTLIBParser::NODE_KIND::NT_ASIN ||
                selected_op == SMTLIBParser::NODE_KIND::NT_ACOS ||
                selected_op == SMTLIBParser::NODE_KIND::NT_ATAN ||
                selected_op == SMTLIBParser::NODE_KIND::NT_ACOT) {
            // 对于需要非负数/在特定范围内的参数的函数，可以添加加法防止负数
            auto child_value = parser->toReal(parser->evaluate(child, model));
            if(child_value == 0){
                // 如果参数为0，添加加法防止0
                child = parser->mkAdd(child, parser->mkConstReal(1));
            }
            else if (child_value < -1 || child_value > 1) {
                // 如果参数不在范围内，添加加法防止超出范围
                child = parser->mkDivReal(parser->mkConstReal(1), child);
            }
        }
        
        result = parser->mkOper(sort, selected_op, child);
    } else if (param_count == 2) {
        auto left = generateArithmeticExpression(depth - 1, sort);
        auto right = generateArithmeticExpression(depth - 1, sort);

        auto right_value = parser->evaluate(right, model);
        
        // 处理除法和取模操作符，确保除数不为0
        if ((selected_op == SMTLIBParser::NODE_KIND::NT_DIV_INT ||
             selected_op == SMTLIBParser::NODE_KIND::NT_DIV_REAL ||
             selected_op == SMTLIBParser::NODE_KIND::NT_MOD) && 
             parser->isZero(right_value)) {
            // 如果除数是0，替换为非0值
            right = parser->mkAdd(right, sort->isReal() ? parser->mkConstReal(1) : parser->mkConstInt(1));
        }
        
        result = parser->mkOper(sort, selected_op, left, right);
    } else if (param_count == 3) {
        auto left = generateArithmeticExpression(depth - 1, sort);
        auto right = generateArithmeticExpression(depth - 1, sort);
        auto third = generateArithmeticExpression(depth - 1, sort);
        result = parser->mkOper(sort, selected_op, left, right, third);
    } else {
        // param_count == -1 means variable-arity operator
        std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> children;
        int num_children = std::uniform_int_distribution<int>(2, 5)(rng);
        for (int i = 0; i < num_children; ++i) {
            children.push_back(generateArithmeticExpression(depth - 1, sort));
        }
        result = parser->mkOper(sort, selected_op, children);
    }
    
    return result;
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
        outfile << model->toString();
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
    model = SMTLIBParser::newModel();
    
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
    if (logic == "QF_LIA") {
        default_var_sort = SMTLIBParser::INT_SORT;
    } else if (logic == "QF_NTA") {
        default_var_sort = SMTLIBParser::REAL_SORT;
    } else {
        // 默认使用整数类型
        default_var_sort = SMTLIBParser::INT_SORT;
    }
    
    // 确保生成的变量数量不超过指定的数量
    for (int i = 0; i < num_vars; ++i) {
        // 决定变量类型
        std::shared_ptr<SMTLIBParser::Sort> var_sort;
        std::uniform_real_distribution<double> type_dist(0.0, 1.0);
        double random_val = type_dist(rng);
        
        // 根据布尔变量生成概率决定是否生成布尔变量
        if (random_val < bool_var_probability) {
            var_sort = SMTLIBParser::BOOL_SORT;
        } else {
            var_sort = default_var_sort;
        }
        
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
            model->add(var, value_node);
        } else if (var_sort->isReal()) {
            std::uniform_real_distribution<double> real_dist(real_min_value, real_max_value);
            double value = real_dist(rng);
            auto value_node = parser->mkConstReal(value);
            variable_values[var_name] = value_node;
            // 添加到模型中
            model->add(var, value_node);
        } else if (var_sort->isBool()) {
            std::uniform_int_distribution<int> bool_dist(0, 1);
            bool value = bool_dist(rng) == 1;
            auto value_node = value ? parser->mkTrue() : parser->mkFalse();
            variable_values[var_name] = value_node;
            // 添加到模型中
            model->add(var, value_node);
        }
        
        variables.push_back(var);
    }
    
    // 生成约束
    std::vector<std::shared_ptr<SMTLIBParser::DAGNode>> constraints;
    for (int i = 0; i < num_constraints; ++i) {
        try {
            // 使用更高的深度生成更复杂的约束
            auto constraint = generateConstraint(constraint_depth);
            
            // 确保不是简单的true/false约束
            if (constraint->isTrue() || constraint->isFalse()) {
                // 如果是简单常量，重新生成
                i--; // 重试这个约束
                continue;
            }

            if(parser->evaluate(constraint, model)->isFalse()) {
                constraint = parser->mkNot(constraint);
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
