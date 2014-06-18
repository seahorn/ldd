add_library(Ldd_Ldd lddInit.c lddIte.c lddVars.c lddDebug.c
  lddNodeset.c lddExport.c lddPrint.c lddCof.c lddQelimFM.c
  lddQelimPAT.c lddQelim.c lddQelimInf.c lddQelimBdd.c lddAPI.c
  lddSatReduce.c lddBoxes.c)
set_target_properties (Ldd_Ldd PROPERTIES OUTPUT_NAME "ldd")

install (FILES ldd.h lddInt.h DESTINATION include/ldd)
install (TARGETS Ldd_Ldd ARCHIVE DESTINATION lib)