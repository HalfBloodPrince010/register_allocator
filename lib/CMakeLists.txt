add_library(RegAlloc SHARED RegisterAllocator.cpp)

# Apply LLVM compile and link flags explicitly
target_compile_options(RegAlloc PRIVATE ${LLVM_CXXFLAGS_LIST})
target_link_options(RegAlloc PRIVATE ${LLVM_LDFLAGS_LIST})
target_link_libraries(RegAlloc PRIVATE ${LLVM_LIBS_LIST})