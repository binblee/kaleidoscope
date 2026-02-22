cmake_minimum_required(VERSION 3.24)
project(kaleidoscope)

add_executable(${PROJECT_NAME})

target_sources(${PROJECT_NAME}
    PRIVATE src/toy.cpp
)
