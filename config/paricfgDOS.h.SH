file="$objdir/../Odos/paricfg.h"; echo Extracting $file
rm -f $file
cat > $file << EOT
/* This file extracted by Configure. */
#ifndef __CONFIG_H__
#define __CONFIG_H__

#ifdef _MSC_VER /* Bill Daly: avoid spurious Warnings from MSVC */
#  pragma warning(disable: 4013 4018 4146 4244 4761)
#endif

#define GPDATADIR "/pari/data"
#define GPMISCDIR "/pari/"
#define SHELL_Q '"'
#define DL_DFLT_NAME "libpari.dll"

#define PARIVERSION "GP/PARI CALCULATOR Version ${version}.${patch} (${status})"
#ifdef __cplusplus
#  define PARIINFO_PRE "C++"
#else
#  define PARIINFO_PRE ""
#endif
#if defined(__EMX__)
#  define PARIINFO_POST "ix86 running EMX (ix86 kernel) 32-bit version"
#endif
#if defined(WINCE)
#  define PARIINFO_POST "Windows CE 32-bit version"
#endif
#if !defined(PARIINFO_POST)
#  define PARIINFO_POST "ix86 running Windows 3.2 (ix86 kernel) 32-bit version"
#endif
#define PARIINFO PARIINFO_PRE/**/PARIINFO_POST

#define PARI_BYTE_ORDER    1234
#ifdef _MSC_VER /* MSVC inline directive */
#  define INLINE __inline
#endif

/*  Location of GNU gzip program, enables reading of .Z and .gz files. */
#ifndef WINCE
#  define GNUZCAT
#  define ZCAT "gzip -d -c"
#endif

#ifdef __EMX__
#  define READLINE
#  define READLINE_LIBRARY
#  define HAS_RL_MESSAGE
#  define CPPFunction_defined
/* in readline 1, no arguments for rl_refresh_line() */
#  define RL_REFRESH_LINE_OLDPROTO
#endif
#ifdef __MINGW32__
#  define READLINE "4.0"
#  define HAS_COMPLETION_APPEND_CHAR
#  define HAS_RL_SAVE_PROMPT
#  define HAS_RL_MESSAGE
#  define CPPFunction_defined
#endif

/* No exp2, log2 in libc */
#define NOEXP2

/* Headers are clean - ulong not defined */
#define ULONG_NOT_DEFINED

#ifndef WINCE
/* Timings: Don't use times because of the HZ / CLK_TCK confusion. */
#  define USE_FTIME 1
#  define HAS_STRFTIME
 /* comment this one if not on NT ??? */
#  define HAS_OPENDIR
#endif

#endif
EOT
