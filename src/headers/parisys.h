/******************************************************************/
/* This files contains macros depending on system and compiler    */
/* $Id$ */

#ifndef LITTLE_ENDIAN_64
#  define   LITTLE_ENDIAN_64 12345678
#endif
#ifndef BIG_ENDIAN_64
#  define   BIG_ENDIAN_64    87654321
#endif
#ifndef LITTLE_ENDIAN
#  define   LITTLE_ENDIAN 1234
#endif
#ifndef BIG_ENDIAN
#  define   BIG_ENDIAN    4321
#endif
#ifndef PDP_ENDIAN
#  define   PDP_ENDIAN    3412
#endif

#ifdef __cplusplus
#  define ANYARG ...
#  define BEGINEXTERN extern "C" {
#  define ENDEXTERN }
#  define INLINE inline
#  ifdef __GNUC__
#    define ASMINLINE
#    define VOLATILE volatile
#  else
#    define VOLATILE
#  endif
#else
#  define ANYARG
#  define BEGINEXTERN
#  define ENDEXTERN
#  ifdef __GNUC__
#    define ASMINLINE
#    define VOLATILE __volatile__
#    ifdef GCC_INLINE
#      ifndef __OPTIMIZE__
#        error "no inlining without -O. Put back -O or remove -DGCC_INLINE"
#      else
#        define INLINE __inline__ static
#      endif
#    endif
#    ifdef __STRICT_ANSI__
#      define ULONG_NOT_DEFINED
#    endif
#  else
#    define VOLATILE

#  endif
#endif
#ifdef _WIN32
/* ANSI C does not allow to longjmp() out of a signal handler, in particular,
 * the SIGINT handler. On Win32, the handler is executed in another thread, and
 * longjmp'ing into another thread's stack will utterly confuse the system.
 * Instead, we check whether win32ctrlc is set in new_chunk().
 */
  extern int win32ctrlc;
  void dowin32ctrlc();
#endif
