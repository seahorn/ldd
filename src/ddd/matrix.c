#include "util.h"
#include "dddCuddInt.h"

/**
 * Creates a matrix with m rows and n columns
 */
pmatrix matrix_create (int m, int n)
{
  pmatrix mat;
  
  mat = (pmatrix)malloc (sizeof(matrix));
  if (mat == NULL) return NULL;

  mat->m = m;
  mat->n = n;
  mat->data = (int*) malloc (sizeof (int) * m * n);
  
  if (mat->data == NULL)
    {
      free (mat);
      return NULL;
    }

  return mat;
}

/**
 * Creates a square matrix with m rows and m columns
 */
pmatrix matrix_create_square (int m)
{
  return matrix_create (m, m);
}

/**
 * Frees memory allocated by a matrix
 */
void matrix_destroy (pmatrix m)
{
  if (m->data != NULL) free (m->data);
  free (m);
}

/**
 * Fills all entries of a matrix m with value v
 */
void matrix_fill (pmatrix m, int v)
{
  memset (m->data, v, sizeof(int) * m->m * m->n);
}

/**
 * Creates a copy of a matrix
 */
pmatrix matrix_dup (pmatrix m)
{
  pmatrix res;
  res = matrix_create (m->m, m->n);
  memcpy (res->data, m->data, sizeof(int) * m->m * m->n);
  return res;
}

/**
 * Applies Floyd-Warshall shortest path algorithm.
 * Assume: m is a square matrix (m->m == m->n)
 * Side-effect:  m is modified
 */
void matrix_floyd_warshall (pmatrix m)
{
  /* assume matrix is square */
  int k, i, j;
  
  assert (m->m == m->n);
  
  for (k = 0; k < m->m; k++)
    for (i = 0; i < m->m; i++)
      for (j = 0; j < m->m; j++)
	if (M_GET(m,i,j) > M_GET(m,i,k) + M_GET(m,k,j))
	  M_SET(m,i,j,M_GET(m,i,k) + M_GET(m,k,j));
}

/**
 * Returns 1 if the difference constraints represented by m are
 * satisfiable.
 * 
 * Assume: m is a square matrix
 * Side-effect: m is modified
 */
int ddd_is_sat (pmatrix m)
{
  int i;
  
  matrix_floyd_warshall (m);  
  for (i = 0; i < m->m; i++)
    if (M_GET(m,i,i) < 0) return 0;

  return 1;
}
