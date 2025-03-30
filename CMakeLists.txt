cmake_minimum_required(VERSION 3.20)

project(RegisterAllocatorMinimal)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# LLVM
execute_process(COMMAND llvm-config --cxxflags
                OUTPUT_VARIABLE LLVM_CXXFLAGS
                OUTPUT_STRIP_TRAILING_WHITESPACE)

execute_process(COMMAND llvm-config --ldflags
                OUTPUT_VARIABLE LLVM_LDFLAGS
                OUTPUT_STRIP_TRAILING_WHITESPACE)

execute_process(COMMAND llvm-config --libs all
                OUTPUT_VARIABLE LLVM_LIBS
                OUTPUT_STRIP_TRAILING_WHITESPACE)
    
execute_process(COMMAND llvm-config --system-libs
                OUTPUT_VARIABLE LLVM_SYSTEM_LIBS
                OUTPUT_STRIP_TRAILING_WHITESPACE)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_CXXFLAGS} -Wall -Werror")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LLVM_LDFLAGS}")
add_compile_options(-Wno-unused-private-field)

include_directories(${LLVM_INCLUDE_DIRS})

add_subdirectory(lib)

add_executable(${PROJECT_NAME} lib/RegisterAllocatorMinimal.cpp)

target_link_libraries(${PROJECT_NAME} PRIVATE ${LLVM_LIBS} ${LLVM_SYSTEM_LIBS})