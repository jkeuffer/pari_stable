/* $Id$ */

/* DO NOT REORDER THESE
 * actual values can be changed, but don't forget to adapt
 *  - lontyp/lontyp2 in gen2.c
 *  - the assembly file mp.s...
 */
#define t_SMALL    0
#define t_INT      1
#define t_REAL     2
#define t_INTMOD   3
#define t_FRAC     4
#define t_FRACN    5
#define t_COMPLEX  6
#define t_PADIC    7
#define t_QUAD     8
#define t_POLMOD   9
#define t_POL      10
#define t_SER      11
#define t_RFRAC    13
#define t_RFRACN   14
#define t_QFR      15
#define t_QFI      16
#define t_VEC      17
#define t_COL      18
#define t_MAT      19
#define t_LIST     20
#define t_STR      21
#define t_VECSMALL 22

#define is_recursive_t(t) (lontyp[t])

/* #define is_intreal_t(t) ( (t) == t_REAL || (t) == t_INT ) */
#define is_intreal_t(t) ( (t) <= t_REAL )

#define is_frac_t(t) ( (t) == t_FRAC || (t) == t_FRACN )
#define is_rfrac_t(t) ( (t) == t_RFRAC || (t) == t_RFRACN )
#define is_polser_t(t) ( (t) == t_SER || (t) == t_POL )
#define is_vec_t(t) ( (t) == t_VEC || (t) == t_COL )
#define is_matvec_t(t) ( (t) >= t_VEC && (t) <= t_MAT )
#define is_scalar_t(tx) ((tx) < t_POL)
#define is_extscalar_t(tx) ((tx) <= t_POL)
#define is_const_t(tx) ((tx) < t_POLMOD)
/* pas terrible celui-la: pour deriv */

#define is_qf_t(t) ( (t) == t_QFR || (t) == t_QFI )
#define is_mod_t(t) ( (t) == t_POLMOD || (t) == t_INTMOD )
#define has_lgef_t(t) ((t) == t_INT || (t) == t_POL)

/* #define is_graphicvec_t(t) ( is_matvec_t(t) || is_qf_t(t) ) */
#define is_graphicvec_t(t) ( (t) >= t_QFR && (t) <= t_MAT )

#define needsnewline(tx) (is_matvec(tx))
#define isscalar(x) (is_scalar_t(typ(x)) || (typ(x)==t_POL && lgef(x)<=3))
#define isnonscalar(x) (typ(x) == t_POL && lgef(x) > 3)
