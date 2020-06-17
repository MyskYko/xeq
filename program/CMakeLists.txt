cmake_minimum_required(VERSION 3.8)
project(xeq CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_compile_options(-g -O3)	

add_subdirectory(lib)

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

file(GLOB FILENAMES ${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp)
add_executable(xeq ${FILENAMES})
target_link_libraries(xeq bdd atbdd glucose)
target_include_directories(xeq PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/lib/glucose)

list(REMOVE_ITEM FILENAMES ${CMAKE_CURRENT_SOURCE_DIR}/src/main.cpp)
add_executable(ceverify ${CMAKE_CURRENT_SOURCE_DIR}/misc/ceverify.cpp ${FILENAMES})
target_link_libraries(ceverify bdd atbdd glucose)
target_include_directories(ceverify PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/lib/glucose)
