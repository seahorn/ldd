
# setup all header files
configure_file(cudd/cudd.h ${Ldd_BINARY_DIR}/include/cudd.h COPYONLY)
configure_file(cudd/cuddInt.h ${Ldd_BINARY_DIR}/include/cuddInt.h COPYONLY)
configure_file(epd/epd.h ${Ldd_BINARY_DIR}/include/epd.h COPYONLY)
configure_file(dddmp/dddmp.h ${Ldd_BINARY_DIR}/include/dddmp.h COPYONLY)
configure_file(mtr/mtr.h ${Ldd_BINARY_DIR}/include/mtr.h COPYONLY)
configure_file(obj/cuddObj.hh ${Ldd_BINARY_DIR}/include/cuddObj.hh COPYONLY)
configure_file(st/st.h ${Ldd_BINARY_DIR}/include/st.h COPYONLY)
configure_file(util/util.h ${Ldd_BINARY_DIR}/include/util.h COPYONLY)
configure_file(mnemosyne/mnemosyne.h  ${Ldd_BINARY_DIR}/include/mnemosyne.h COPYONLY)

add_subdirectory(util)
add_subdirectory(mtr)
add_subdirectory(epd)
add_subdirectory(st)
add_subdirectory(cudd)