project(Ldd)
cmake_minimum_required(VERSION 2.8.11)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

include ("cmake/PackageOptions.cmake")

include_directories(
  ${CMAKE_CURRENT_BINARY_DIR}/include
  )

add_subdirectory(cudd-2.4.2)
#add_subdirectory(src)