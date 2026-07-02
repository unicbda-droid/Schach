cmake_minimum_required(VERSION 3.16)
project(Aufbauspiel LANGUAGES CXX)
set(CMAKE_CXX_STANDARD 17)

set(VCPKG_DIR "C:/Users/ionco/vcpkg/installed/x64-windows")
set(glfw3_DIR "${VCPKG_DIR}/share/glfw3")
find_package(glfw3 REQUIRED)
set(GLEW_INCLUDE_DIR "${VCPKG_DIR}/include")
set(GLEW_LIBRARY "${VCPKG_DIR}/lib/glew32.lib")

add_executable(Aufbauspiel main.cpp)

target_include_directories(Aufbauspiel PRIVATE ${GLEW_INCLUDE_DIR})
target_link_libraries(Aufbauspiel PRIVATE glfw ${GLEW_LIBRARY} opengl32 winmm)
