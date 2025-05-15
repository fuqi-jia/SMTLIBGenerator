# SMTLIBGenerator

A tool for generating random satisfiable SMT-LIB2 formulas based on SMTLIBParser.

## Overview

SMTLIBGenerator creates random satisfiable SMT formulas in SMT-LIB2 format. It works by:
1. Randomly creating variables and assigning values to them
2. Generating expressions using available operators from the chosen theory
3. Tracking variable values during expression generation
4. Creating constraints (comparison expressions) that are guaranteed to be satisfiable
5. Outputting everything in SMT-LIB2 format

## Supported Theories

- QF_LIA: Quantifier-Free Linear Integer Arithmetic
- NTA: Non-linear Transcendental Arithmetic

## Requirements

- C++17 or newer
- GMP (GNU Multiple Precision Arithmetic Library)
- CMake 3.10 or newer

## Building

```bash
# Clone the repository with submodules
git clone --recursive https://github.com/fuqi-jia/SMTLIBGenerator.git
cd SMTLIBGenerator

# Create build directory
mkdir build
cd build

# Configure and build
cmake ..
make

# Optionally install
make install
```

## Usage

```
SMTLIBGenerator <logic> <num_vars> <num_constraints> <output_path> [seed]
```

Parameters:
- `logic`: The logic to use (QF_LIA or NTA)
- `num_vars`: Number of variables to generate
- `num_constraints`: Number of constraints to generate
- `output_path`: Path to output SMT-LIB2 file
- `seed` (optional): Random seed (default: current time)

Example:
```bash
./SMTLIBGenerator QF_LIA 10 5 examples/example1.smt2
```

This will generate a satisfiable QF_LIA formula with 10 variables and 5 constraints, and save it to `examples/example1.smt2`.

## License

This project is licensed under the MIT License - see the LICENSE file for details.
