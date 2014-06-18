find_package (Gmp REQUIRED)
include_directories (${GMP_INCLUDE_DIR})

configure_file(ldd/ldd.h ${Ldd_BINARY_DIR}/include/ldd.h COPYONLY)
configure_file(ldd/lddInt.h ${Ldd_BINARY_DIR}/include/lddInt.h COPYONLY)
configure_file(tvpi/tvpi.h ${Ldd_BINARY_DIR}/include/tvpi.h COPYONLY)

add_subdirectory (tvpi)
add_subdirectory (ldd)
add_subdirectory (test)