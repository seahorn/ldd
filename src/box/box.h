/** 
 * BOX Theory. Constraints of the form   x<=k and -x<= k
 */

#ifndef __BOX__H_
#define __BOX__H_
#include "tdd.h"

#ifdef __cplusplus
extern "C" {
#endif

  theory_t *box_create_theory (size_t vn);
  void box_destroy_theory (tdd_manager*, theory_t*);

#ifdef __cplusplus
}
#endif
#endif
