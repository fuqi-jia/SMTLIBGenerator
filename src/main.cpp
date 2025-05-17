#include "generator.h"
#include <iostream>
#include <string>
#include <random>
#include <ctime>
#include <cstdlib>
#include <filesystem>

void printUsage() {
    std::cout << "Usage: SMTLIBGenerator <logic> <num_vars> <num_constraints> <output_path> [bool_prob] [seed]" << std::endl;
    std::cout << "  logic           : Logic to use (QF_LIA or NTA)" << std::endl;
    std::cout << "  num_vars        : Number of variables to generate" << std::endl;
    std::cout << "  num_constraints : Number of constraints to generate" << std::endl;
    std::cout << "  output_path     : Path to output SMT-LIB2 file" << std::endl;
    std::cout << "  bool_prob (optional) : Probability of generating boolean variables (0.0-1.0, default: 0.2)" << std::endl;
    std::cout << "  seed (optional) : Random seed (default: current time)" << std::endl;
}

int main(int argc, char* argv[]) {
    // 检查参数数量
    if (argc < 5) {
        std::cerr << "Error: Not enough arguments" << std::endl;
        printUsage();
        return 1;
    }
    
    // 解析参数
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
    
    // 布尔变量生成概率
    double bool_prob = 0.2; // 默认值
    if (argc > 5) {
        try {
            bool_prob = std::stod(argv[5]);
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
    if (argc > 6) {
        try {
            seed = std::stoi(argv[6]);
        } catch (const std::exception& e) {
            std::cerr << "Error: Invalid seed format" << std::endl;
            printUsage();
            return 1;
        }
    } else {
        // 如果没有提供种子，使用当前时间
        seed = static_cast<unsigned int>(std::time(nullptr));
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
    
    // 设置逻辑
    if (logic != "QF_LIA" && logic != "NTA") {
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
