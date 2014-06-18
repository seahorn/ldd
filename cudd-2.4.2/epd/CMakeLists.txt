add_library (Cudd_Epd epd.c)
set_target_properties (Cudd_Epd PROPERTIES OUTPUT_NAME "epd")
install (FILES epd.h DESTINATION include/ldd)
install (TARGETS Cudd_Epd ARCHIVE DESTINATION lib)
