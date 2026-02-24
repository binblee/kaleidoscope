cmake_minimum_required(VERSION 3.24)
project(kaleidoscope CXX)

if (APPLE)
    set(CMAKE_CXX_COMPILER "clang++")
elseif(UNIX)
    find_program(CLANGPP_EXECUTABLE NAMES clang++ HINTS /usr/bin /usr/local/bin)
    if (CLANGPP_EXECUTABLE)
        set(CMAKE_CXX_COMPILER "${CLANGPP_EXECUTABLE}")
    else()
        message(WARNING "clang++ not found. Using default C++ compiler, which might cause issues with LLVM.")
    endif()
endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_program(LLVM_CONFIG NAMES llvm-config REQUIRED)

execute_process(COMMAND ${LLVM_CONFIG} --cppflags OUTPUT_VARIABLE LLVM_CPPFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG} --includedir OUTPUT_VARIABLE LLVM_INCLUDEDIR OUTPUT_STRIP_TRAILING_WHITESPACE)

include_directories(${LLVM_INCLUDEDIR})

set(LLVM_COMMON_LIBS
    Core
    Analysis
    ExecutionEngine
    InstCombine
    Object
    OrcJIT
    RuntimeDyld
    ScalarOpts
    Support
    Target
    CodeGen
    AsmPrinter
    MC
    MCJIT
    MCDisassembler
    BitWriter
    LTO
)

if ("${CMAKE_SYSTEM_PROCESSOR}" MATCHES "x86_64")
    message(STATUS "Detected x86_64 processor, adding X86 LLVM components.")
    list(APPEND LLVM_COMMON_LIBS
        X86CodeGen
        X86AsmParser
    )
elseif ("${CMAKE_SYSTEM_PROCESSOR}" MATCHES "aarch64|arm64")
    message(STATUS "Detected AArch64/ARM64 processor, adding AArch64 LLVM components.")
    list(APPEND LLVM_COMMON_LIBS
        AArch64CodeGen
        AArch64AsmParser
    )
else()
    message(WARNING "Unknown processor type '${CMAKE_SYSTEM_PROCESSOR}'. Linking only common LLVM components. JIT might fail.")
endif()

execute_process(COMMAND ${LLVM_CONFIG} --libs ${LLVM_COMMON_LIBS} --link-static
                OUTPUT_VARIABLE LLVM_SPECIFIC_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)

# Now get the system libraries separately from llvm-config (might include zlib, but we'll be explicit)
execute_process(COMMAND ${LLVM_CONFIG} --system-libs
                OUTPUT_VARIABLE LLVM_SYSTEM_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)

add_executable(${PROJECT_NAME})
target_sources(${PROJECT_NAME} PRIVATE src/toy.cpp)

target_compile_options(${PROJECT_NAME} PRIVATE ${LLVM_CPPFLAGS})

target_link_libraries(${PROJECT_NAME}
    PRIVATE
    ${LLVM_SPECIFIC_LIBS}
    ${LLVM_SYSTEM_LIBS}
)

# --- Explicitly find and link Zlib ---
# The zlib library is typically named 'z' on most Unix-like systems.
find_library(ZLIB_LIBRARY NAMES z HINTS /opt/homebrew/lib /usr/local/lib /usr/lib)
if (ZLIB_LIBRARY)
    message(STATUS "Found Zlib library: ${ZLIB_LIBRARY}")
    target_link_libraries(${PROJECT_NAME} PRIVATE ${ZLIB_LIBRARY})
else()
    message(FATAL_ERROR "Could not find Zlib library. Please ensure zlib is installed.")
endif()

# Explicitly find and link Zstd
find_library(ZSTD_LIBRARY NAMES zstd HINTS /opt/homebrew/lib /usr/local/lib /usr/lib)
if (ZSTD_LIBRARY)
    message(STATUS "Found Zstd library: ${ZSTD_LIBRARY}")
    target_link_libraries(${PROJECT_NAME} PRIVATE ${ZSTD_LIBRARY})
else()
    message(FATAL_ERROR "Could not find Zstd library. Please ensure zstd is installed.")
endif()
