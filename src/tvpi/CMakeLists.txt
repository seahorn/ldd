add_library(Ldd_Tvpi tvpi.c)
set_target_properties(Ldd_Tvpi PROPERTIES OUTPUT_NAME "tvpi")
install (FILES tvpi.h DESTINATION include/ldd)
install (TARGETS Ldd_Tvpi ARCHIVE DESTINATION lib)