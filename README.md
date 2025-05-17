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
- QF_NTA: Quantifier-Free Non-linear Transcendental Arithmetic

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
SMTLIBGenerator <logic> <num_vars> <num_constraints> <output_path> [options]
```

### Required Parameters:
- `logic`: The logic to use (QF_LIA or QF_NTA)
- `num_vars`: Number of variables to generate
- `num_constraints`: Number of constraints to generate
- `output_path`: Path to output SMT-LIB2 file

### Options:
- `--bool-prob <value>` : Probability of generating boolean variables (0.0-1.0, default: 0.2)
- `--seed <value>` : Random seed (default: current time)
- `--int-min <value>` : Minimum value for integer variables (default: -100)
- `--int-max <value>` : Maximum value for integer variables (default: 100)
- `--real-min <value>` : Minimum value for real variables (default: -100.0)
- `--real-max <value>` : Maximum value for real variables (default: 100.0)
- `--depth <value>` : Depth of constraint generation (affects complexity, default: 4)

### Examples:

Basic usage:
```bash
./SMTLIBGenerator QF_LIA 10 5 examples/example1.smt2
```

Setting a specific seed for reproducibility:
```bash
./SMTLIBGenerator QF_LIA 10 5 examples/example2.smt2 --seed 12345
```

Setting variable ranges:
```bash
./SMTLIBGenerator QF_LIA 10 5 examples/example3.smt2 --int-min 1 --int-max 100
```

Generating QF_NTA formulas with custom ranges:
```bash
./SMTLIBGenerator QF_NTA 8 4 examples/example4.smt2 --real-min -10.0 --real-max 10.0
```

Multiple options can be combined in any order:
```bash
./SMTLIBGenerator QF_LIA 15 6 examples/example5.smt2 --bool-prob 0.1 --seed 54321 --int-min 0 --int-max 50
```

Generating more complex constraints by increasing depth:
```bash
./SMTLIBGenerator QF_LIA 10 5 examples/complex.smt2 --depth 6
```

## License

This project is licensed under the MIT License - see the LICENSE file for details.
