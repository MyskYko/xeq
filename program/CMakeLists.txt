project(xeq CXX)
cmake_minimum_required(VERSION 3.8)
#set(CMAKE_CXX_STANDARD 17)
#set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_compile_options(-g -O3)	

#add_subdirectory(lib)

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

add_executable(xeq ${CMAKE_CURRENT_SOURCE_DIR}/src/main.cpp ${CMAKE_CURRENT_SOURCE_DIR}/src/node.cpp)
