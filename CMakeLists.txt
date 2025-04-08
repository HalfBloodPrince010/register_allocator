cmake_minimum_required(VERSION 3.20)

project(RegisterAllocatorMinimal)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# LLVM
# Load LLVMConfig.cmake. If this fails, consider setting `LLVM_DIR` to point
# to your LLVM installation's `lib/cmake/llvm` directory.
# LLVM_DIR=/usr/local/opt/llvm@18/lib/cmake/llvm/
set(LLVM_DIR "/usr/local/opt/llvm@18/lib/cmake/llvm")
find_package(LLVM REQUIRED CONFIG)

# Include the part of LLVM's CMake libraries that defines
# `add_llvm_pass_plugin`.
include(AddLLVM)

# Use LLVM's preprocessor definitions, include directories, and library search
# paths.
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

# Fetch monolithic LLVM compile/link flags explicitly
execute_process(COMMAND llvm-config --cxxflags
                OUTPUT_VARIABLE LLVM_CXXFLAGS
                OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND llvm-config --ldflags
                OUTPUT_VARIABLE LLVM_LDFLAGS
                OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND llvm-config --libs
                OUTPUT_VARIABLE LLVM_LIBS
                OUTPUT_STRIP_TRAILING_WHITESPACE)

# Prepare these flags for use in subdirectories
separate_arguments(LLVM_CXXFLAGS_LIST UNIX_COMMAND "${LLVM_CXXFLAGS}")
separate_arguments(LLVM_LDFLAGS_LIST UNIX_COMMAND "${LLVM_LDFLAGS}")
separate_arguments(LLVM_LIBS_LIST UNIX_COMMAND "${LLVM_LIBS}")

# Pass LLVM flags to subdirectories
set(LLVM_CXXFLAGS_LIST ${LLVM_CXXFLAGS_LIST} CACHE INTERNAL "")
set(LLVM_LDFLAGS_LIST ${LLVM_LDFLAGS_LIST} CACHE INTERNAL "")
set(LLVM_LIBS_LIST ${LLVM_LIBS_LIST} CACHE INTERNAL "")

add_subdirectory(pass)
add_subdirectory(lib)
