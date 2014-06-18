set(PSRC mtrBasic.c mtrGroup.c)
add_library (Cudd_Mtr ${PSRC})
set_target_properties (Cudd_Mtr PROPERTIES OUTPUT_NAME "mtr")
set_target_properties (Cudd_Mtr PROPERTIES COMPILE_DEFINITIONS_DEBUG 
  "${COMPILE_DEFINITIONS_DEBUG};MTR_STATS;MTR_VERBOSE;MTR_DEBUG")
install (FILES mtr.h DESTINATION include/ldd)
install (TARGETS Cudd_Mtr ARCHIVE DESTINATION lib)


add_executable(Cudd_testmtr testmtr.c)
target_link_libraries(Cudd_testmtr Cudd_Mtr Cudd_Util)
set_target_properties (Cudd_testmtr PROPERTIES OUTPUT_NAME "testmtr")
set_target_properties (Cudd_testmtr PROPERTIES COMPILE_DEFINITIONS_DEBUG 
  "${COMPILE_DEFINITIONS_DEBUG};MTR_STATS;MTR_VERBOSE;MTR_DEBUG")
