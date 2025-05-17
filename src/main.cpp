#include "generator.h"
#include <iostream>
#include <string>
#include <random>
#include <ctime>
#include <cstdlib>
#include <filesystem>
#include <map>

void printUsage() {
    std::cout << "Usage: SMTLIBGenerator <logic> <num_vars> <num_constraints> <output_path> [options]" << std::endl;
    std::cout << "  logic           : Logic to use (QF_LIA or QF_NTA)" << std::endl;
    std::cout << "  num_vars        : Number of variables to generate" << std::endl;
    std::cout << "  num_constraints : Number of constraints to generate" << std::endl;
    std::cout << "  output_path     : Path to output SMT-LIB2 file" << std::endl;
    std::cout << "Options:" << std::endl;
    std::cout << "  --bool-prob <value>  : Probability of generating boolean variables (0.0-1.0, default: 0.2)" << std::endl;
    std::cout << "  --seed <value>       : Random seed (default: current time)" << std::endl;
    std::cout << "  --int-min <value>    : Minimum value for integer variables (default: -100)" << std::endl;
    std::cout << "  --int-max <value>    : Maximum value for integer variables (default: 100)" << std::endl;
    std::cout << "  --real-min <value>   : Minimum value for real variables (default: -100.0)" << std::endl;
    std::cout << "  --real-max <value>   : Maximum value for real variables (default: 100.0)" << std::endl;
    std::cout << "  --depth <value>      : Depth of constraint generation (default: 4)" << std::endl;
}

// 解析命令行参数
bool parseOption(int argc, char* argv[], const std::string& option, std::string& value) {
    for (int i = 5; i < argc; i += 2) {
        if (i + 1 < argc && std::string(argv[i]) == option) {
            value = argv[i + 1];
            return true;
        }
    }
    return false;
}

int main(int argc, char* argv[]) {
    // 检查参数数量
    if (argc < 5) {
        std::cerr << "Error: Not enough arguments" << std::endl;
        printUsage();
        return 1;
    }
    
    // 解析必选参数
    std::string logic = argv[1];
    int num_vars, num_constraints;
    
    try {
        num_vars = std::stoi(argv[2]);
        num_constraints = std::stoi(argv[3]);
    } catch (const std::exception& e) {
        std::cerr << "Error: Invalid number format" << std::endl;
        printUsage();
        return 1;
    }
    
    std::string output_path = argv[4];
    
    // 检查变量和约束数量的有效性
    if (num_vars <= 0 || num_constraints <= 0) {
        std::cerr << "Error: Number of variables and constraints must be positive" << std::endl;
        return 1;
    }
    
    // 解析可选参数
    std::string option_value;
    
    // 布尔变量生成概率
    double bool_prob = 0.2; // 默认值
    if (parseOption(argc, argv, "--bool-prob", option_value)) {
        try {
            bool_prob = std::stod(option_value);
            if (bool_prob < 0.0 || bool_prob > 1.0) {
                std::cerr << "Warning: Bool probability should be between 0.0 and 1.0. Using default value." << std::endl;
                bool_prob = 0.2;
            }
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid bool probability format. Using default value." << std::endl;
        }
    }
    
    // 确定随机种子
    unsigned int seed;
    if (parseOption(argc, argv, "--seed", option_value)) {
        try {
            seed = std::stoi(option_value);
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid seed format. Using current time." << std::endl;
            seed = static_cast<unsigned int>(std::time(nullptr));
        }
    } else {
        // 如果没有提供种子，使用当前时间
        seed = static_cast<unsigned int>(std::time(nullptr));
    }
    
    // 设置整数变量范围
    int int_min = -100; // 默认值
    if (parseOption(argc, argv, "--int-min", option_value)) {
        try {
            int_min = std::stoi(option_value);
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid int-min format. Using default value." << std::endl;
        }
    }
    
    int int_max = 100;  // 默认值
    if (parseOption(argc, argv, "--int-max", option_value)) {
        try {
            int_max = std::stoi(option_value);
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid int-max format. Using default value." << std::endl;
        }
    }
    
    // 设置实数变量范围
    double real_min = -100.0; // 默认值
    if (parseOption(argc, argv, "--real-min", option_value)) {
        try {
            real_min = std::stod(option_value);
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid real-min format. Using default value." << std::endl;
        }
    }
    
    double real_max = 100.0;  // 默认值
    if (parseOption(argc, argv, "--real-max", option_value)) {
        try {
            real_max = std::stod(option_value);
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid real-max format. Using default value." << std::endl;
        }
    }
    
    // 设置约束生成深度
    int constraint_depth = 4;  // 默认值
    if (parseOption(argc, argv, "--depth", option_value)) {
        try {
            constraint_depth = std::stoi(option_value);
            if (constraint_depth <= 0) {
                std::cerr << "Warning: Constraint depth must be positive. Using default value." << std::endl;
                constraint_depth = 4;
            }
        } catch (const std::exception& e) {
            std::cerr << "Warning: Invalid depth format. Using default value." << std::endl;
        }
    }
    
    // 检查并创建输出目录
    std::filesystem::path output_file_path(output_path);
    auto parent_path = output_file_path.parent_path();
    if (!parent_path.empty() && !std::filesystem::exists(parent_path)) {
        try {
            std::filesystem::create_directories(parent_path);
        } catch (const std::exception& e) {
            std::cerr << "Error: Failed to create output directory: " << parent_path << std::endl;
            std::cerr << "  " << e.what() << std::endl;
            return 1;
        }
    }
    
    // 创建生成器
    std::cout << "Initializing generator with seed: " << seed << std::endl;
    SMTLIBGenerator::Generator generator(seed);
    
    // 设置布尔变量生成概率
    std::cout << "Setting boolean variable probability to: " << bool_prob << std::endl;
    generator.setBoolVarProbability(bool_prob);
    
    // 设置变量取值范围
    std::cout << "Setting integer variable range to: [" << int_min << ", " << int_max << "]" << std::endl;
    generator.setIntRange(int_min, int_max);
    
    std::cout << "Setting real variable range to: [" << real_min << ", " << real_max << "]" << std::endl;
    generator.setRealRange(real_min, real_max);
    
    // 设置约束生成深度
    std::cout << "Setting constraint generation depth to: " << constraint_depth << std::endl;
    generator.setConstraintDepth(constraint_depth);
    
    // 设置逻辑
    if (logic != "QF_LIA" && logic != "QF_NTA") {
        std::cerr << "Warning: Unsupported logic: " << logic << ". Using QF_LIA instead." << std::endl;
        logic = "QF_LIA";
    }
    generator.setLogic(logic);
    
    // 生成SMTLIB2文件
    std::cout << "Generating SMTLIB2 file with " << num_vars << " variables and " 
              << num_constraints << " constraints..." << std::endl;
    
    generator.generateSMTLIB2File(output_path, num_vars, num_constraints);
    
    std::cout << "Successfully generated SMTLIB2 file: " << output_path << std::endl;
    
    return 0;
}
