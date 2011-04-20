/* tuned on laurent5.polytechnique.fr (Athlon 2200+) */
#define __MULII_KARATSUBA_LIMIT  32
#define __SQRI_KARATSUBA_LIMIT  62
#define __MULRR_MULII_LIMIT 294
#define __MULII_FFT_LIMIT       1800
#define __SQRI_FFT_LIMIT       2000
#define __Fp_POW_REDC_LIMIT      70
#define __Fp_POW_BARRETT_LIMIT  139
#define __DIVRR_GMP_LIMIT       -1 /* unused */
#define __EXPNEWTON_LIMIT       87
#define __INVNEWTON_LIMIT      402
#define __LOGAGM_LIMIT          24
#define __LOGAGMCX_LIMIT        90
#define __AGM_ATAN_LIMIT       130
#define __INVMOD_GMP_LIMIT      -1 /* unused */
#define __Flx_MUL_KARATSUBA_LIMIT  100
#define __Flx_SQR_KARATSUBA_LIMIT  200
#define __Flx_MUL_HALFMULII_LIMIT  10
#define __Flx_SQR_HALFSQRI_LIMIT   10
#define __Flx_MUL_MULII_LIMIT      8
#define __Flx_SQR_SQRI_LIMIT       5
#define __Flx_INVMONTGOMERY_LIMIT  6000
#define __Flx_REM_MONTGOMERY_LIMIT 3500
#define __Flx_POW_MONTGOMERY_LIMIT 1000
#define __Flx_HALFGCD_LIMIT        52
#define __Flx_GCD_LIMIT            527
#define __Flx_EXTGCD_LIMIT         118
#define __FpX_INVMONTGOMERY_LIMIT  100
#define __FpX_REM_MONTGOMERY_LIMIT 657
#define __FpX_POW_MONTGOMERY_LIMIT 200
#define __FpX_HALFGCD_LIMIT        70
#define __FpX_GCD_LIMIT            820
#define __FpX_EXTGCD_LIMIT         90
#define __RgX_MUL_LIMIT         10
#define __RgX_SQR_LIMIT          6
