cmake_minimum_required(VERSION 3.8)
project(xeq CXX C)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_subdirectory(lib)

#add_compile_options(-g -O3)
add_compile_options(-O3 -DNDEBUG)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

file(GLOB FILENAMES ${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp)
add_executable(xeq ${FILENAMES})
target_link_libraries(xeq glucose libabc cadical kissat)
target_include_directories(xeq PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/lib/glucose)

add_executable(ceverify ${CMAKE_CURRENT_SOURCE_DIR}/misc/ceverify.cpp ${CMAKE_CURRENT_SOURCE_DIR}/src/node.cpp)
