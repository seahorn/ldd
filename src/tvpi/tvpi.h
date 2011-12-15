/** 
 * TVPI Theory. Constraints of the form   x<=k and -x<= k
 */

#ifndef __TVPI__H_
#define __TVPI__H_
#include "ldd.h"
#include "gmp.h"

typedef mpq_t* tvpi_cst_t;

#ifdef __cplusplus
extern "C" {
#endif

  theory_t *tvpi_create_theory (size_t vn);
  theory_t *tvpi_create_utvpiz_theory (size_t vn);
  theory_t *tvpi_create_tvpiz_theory (size_t vn);
  void tvpi_destroy_theory (theory_t*);
  
  tvpi_cst_t tvpi_create_cst(mpq_t k);
  void tvpi_cst_set_mpq (mpq_t res, tvpi_cst_t k);

#ifdef __cplusplus
}
#endif
#endif
