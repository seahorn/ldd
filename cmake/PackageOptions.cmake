#set(LDD_LIBRARY XXX)
#set(LDD_INCLUDE_DIR XXX)
#add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)

include (CheckTypeSize)
check_type_size (long CMAKE_SIZEOF_LONG)
check_type_size (void* CMAKE_SIZEOF_VOID_P)
mark_as_advanced (CMAKE_SIZEOF_LONG CMAKE_SIZEOF_VOID_P)

add_definitions (-DSIZEOF_VOID_P=${CMAKE_SIZEOF_VOID_P} 
  -DSIZEOF_LONG=${CMAKE_SIZEOF_LONG})

add_definitions(-DHAVE_IEEE_754 -DBSD)