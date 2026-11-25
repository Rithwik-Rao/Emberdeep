cmake_minimum_required(VERSION 3.20)

project(OpenGLBasics LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(glfw3 CONFIG REQUIRED)
find_package(glad CONFIG REQUIRED)
find_package(glm CONFIG REQUIRED)

add_executable(OpenGLBasics createwindow.cpp)

target_link_libraries(OpenGLBasics PRIVATE
    glfw
    glad::glad
    glm::glm
)