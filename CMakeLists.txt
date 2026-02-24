cmake_minimum_required(VERSION 3.24)
project(kaleidoscope CXX)

set(CMAKE_CXX_COMPILER "clang++")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Find LLVM
find_package(LLVM REQUIRED CONFIG)

include_directories(${LLVM_INCLUDE_DIRS})

# Add LLVM's compile definitions (e.g., for release/debug builds)
add_definitions(${LLVM_DEFINITIONS})

add_executable(${PROJECT_NAME})

target_sources(${PROJECT_NAME}
    PRIVATE src/toy.cpp
)

target_link_libraries(${PROJECT_NAME}
    PRIVATE
        LLVMCore
        # LLVMIRReader
        # For example:
        # LLVMAsmParser
        # LLVMCodeGen
        # LLVMTarget
        # LLVMAnalysis
        # LLVMTransformUtils
        # LLVMMCJIT # If you want to use the MCJIT for execution
        # LLVMExecutionEngine
        # LLVMRuntimeDyld
)
