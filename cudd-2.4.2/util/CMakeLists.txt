add_definitions ("-DUNIX")
set (PSRC cpu_time.c cpu_stats.c getopt.c safe_mem.c strsav.c texpand.c 
	  ptime.c prtime.c pipefork.c pathsearch.c stub.c tmpfile.c datalimit.c)
add_library (Cudd_Util ${PSRC})
set_target_properties (Cudd_Util PROPERTIES OUTPUT_NAME "util")

install (FILES util.h DESTINATION include/cudd)
install (TARGETS Cudd_Util ARCHIVE DESTINATION lib)