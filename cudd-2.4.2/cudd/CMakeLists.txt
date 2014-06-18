set(PSRC cuddAPI.c cuddAddAbs.c cuddAddApply.c cuddAddFind.c cuddAddIte.c 
  cuddAddInv.c cuddAddNeg.c cuddAddWalsh.c cuddAndAbs.c 
  cuddAnneal.c cuddApa.c cuddApprox.c cuddBddAbs.c cuddBddCorr.c 
  cuddBddIte.c cuddBridge.c cuddCache.c cuddCheck.c cuddClip.c 
  cuddCof.c cuddCompose.c cuddDecomp.c cuddEssent.c 
  cuddExact.c cuddExport.c cuddGenCof.c cuddGenetic.c 
  cuddGroup.c cuddHarwell.c cuddInit.c cuddInteract.c 
  cuddLCache.c cuddLevelQ.c 
  cuddLinear.c cuddLiteral.c cuddMatMult.c cuddPriority.c 
  cuddRead.c cuddRef.c cuddReorder.c cuddSat.c cuddSign.c 
  cuddSolve.c cuddSplit.c cuddSubsetHB.c cuddSubsetSP.c cuddSymmetry.c 
  cuddTable.c cuddUtil.c cuddWindow.c cuddZddCount.c cuddZddFuncs.c 
  cuddZddGroup.c cuddZddIsop.c cuddZddLin.c cuddZddMisc.c 
  cuddZddPort.c cuddZddReord.c cuddZddSetop.c cuddZddSymm.c 
  cuddZddUtil.c)

add_library (Cudd_Cudd ${PSRC})
set_target_properties (Cudd_Cudd PROPERTIES OUTPUT_NAME "cudd")
set_target_properties (Cudd_Cudd PROPERTIES COMPILE_DEFINITIONS_DEBUG 
  "${COMPILE_DEFINITIONS_DEBUG};DD_DEBUG;DD_CACHE_PROFILE;DD_VERBOSE;DD_UNIQUE_PROFILE")
install (FILES cudd.h cuddInt.h DESTINATION include/cudd)
install (TARGETS Cudd_Cudd ARCHIVE DESTINATION lib)


add_executable(Cudd_testcudd testcudd.c)
target_link_libraries(Cudd_testcudd Cudd_Cudd Cudd_Mtr Cudd_St Cudd_Epd Cudd_Util m)
set_target_properties (Cudd_testcudd PROPERTIES OUTPUT_NAME "testcudd")
set_target_properties (Cudd_testcudd PROPERTIES COMPILE_DEFINITIONS_DEBUG 
  "${COMPILE_DEFINITIONS_DEBUG};DD_DEBUG;DD_CACHE_PROFILE;DD_VERBOSE;DD_UNIQUE_PROFILE")