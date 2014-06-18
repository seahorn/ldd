add_library (Cudd_St st.c)
set_target_properties (Cudd_St PROPERTIES OUTPUT_NAME "st")
install (FILES st.h DESTINATION include/cudd)
install (TARGETS Cudd_St ARCHIVE DESTINATION lib)
