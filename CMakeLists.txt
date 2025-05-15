cmake_minimum_required(VERSION 3.10)
project(SMTLIBGenerator VERSION 1.0)

# C++17标准支持filesystem
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 设置构建类型
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

# 添加编译选项
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -g")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3")

# 设置GMP路径（如果需要）
# set(GMP_INCLUDE_DIR "/path/to/gmp/include")
# set(GMP_LIBRARY "/path/to/gmp/lib/libgmp.so")

# 添加SMTLIBParser子项目
add_subdirectory(SMTLIBParser)

# 查找GMP（大整数库，如果SMTLIBParser需要）
find_library(GMP_LIBRARY gmp)
find_library(GMPXX_LIBRARY gmpxx)

# 包含头文件目录
include_directories(
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/SMTLIBParser/include
  # ${GMP_INCLUDE_DIR} # 如果需要指定GMP目录
)

# 添加源文件
set(SOURCES
  src/generator.cpp
  src/main.cpp
)

# 创建可执行文件
add_executable(SMTLIBGenerator ${SOURCES})

# 链接库
target_link_libraries(SMTLIBGenerator
  smtlibparser_static
  ${GMP_LIBRARY}
  ${GMPXX_LIBRARY}
  stdc++fs  # 用于早期C++17的filesystem支持
)

# 安装目标
install(TARGETS SMTLIBGenerator DESTINATION bin) 