file="$objdir/paricfg.h"

echo Extracting $file
rm -f $file

case "$optimization" in
  full) ;;
  *) debuginfo=" -- $optimization";;
esac

case "$osname" in
  os2) gphelp="perl -S gphelp -detex" ;;
  *) gphelp="$bindir/gphelp" ;;
esac

cat > $file << EOT
/*  This file was created by Configure. Any change made to it will be lost
 *  next time Configure is run.
 */
#ifndef __CONFIG_H__
#define __CONFIG_H__
EOT

# case "$osname" in
#   cygwin*) echo '#ifdef __CYGWIN32__' >> $file ;
# 	     echo '#include "libpari_dll.h"' >> $file ;
# 	     echo '#endif' >> $file ;;
# esac

cat >> $file << EOT
#define UNIX
#define GPHELP "$gphelp"
#define GPDATADIR "$datadir"
#define SHELL_Q '\\$shell_q'

#define PARIVERSION "GP/PARI CALCULATOR Version ${version}.${patch} (${status})"
#ifdef __cplusplus
# define PARIINFO "C++ ${pretty}${debuginfo}"
#else
# define PARIINFO "${pretty}${debuginfo}"
#endif

#define PARI_BYTE_ORDER    ${endian}
EOT

case $asmarch in
  none) echo '#define __HAS_NO_ASM__' >> $file;;
  hppa) echo '#define __HPPA__' >> $file;;
  m68k) echo '#define __M68K__' >> $file;;
esac

if test -n "$gzip"; then
  cat >> $file << EOT

/*  Location of GNU gzip program (enables reading of .Z and .gz files). */
#define GNUZCAT
#define ZCAT "$gzip -dc"

EOT
else if test -n "$zcat"; then
  cat >> $file << EOT

/*  Location of zcat program (enables reading of .Z files). */
#define ZCAT "$zcat"

EOT
  fi
fi

if test -n "$readline"; then
  cat >> $file <<EOT
/*  Use GNU readline library
 *  This is incompatible with SUN commandtools (not with shelltools).
 */
#define READLINE "$readline"
EOT
  if test -n "$rl_appendchar"; then
    echo '#define HAS_COMPLETION_APPEND_CHAR' >> $file
  fi
  if test -n "$rl_save_prompt"; then
    echo '#define HAS_RL_SAVE_PROMPT' >> $file
  else
    if test -n "$_rl_save_prompt"; then
      echo '#define HAS_UNDERSCORE_RL_SAVE_PROMPT' >> $file
    fi
  fi 
  if test -n "$rl_message"; then
    echo '#define HAS_RL_MESSAGE' >> $file
  fi
  echo >> $file
fi

case "$CPPF_defined" in
yes) echo '#define CPPFunction_defined' >> $file;;
esac

case "$sizeof_long" in
8) echo '#define LONG_IS_64BIT' >> $file;;
esac

case "$has_exp2" in
no) echo '#define NOEXP2' >> $file;;
esac

case "$has_ulong" in
no) echo '#define ULONG_NOT_DEFINED' >> $file;;
esac

case "$has_getrusage" in
yes) echo '#define USE_GETRUSAGE 1' >> $file;;
  *) case "$has_times" in
     yes) echo '#define USE_TIMES 1' >> $file;;
       *) case "$has_ftime" in
          yes) echo '#define USE_FTIME 1' >> $file;;
          esac;;
     esac;;
esac

case "$has_sigrelse" in
yes) echo '#define USE_SIGRELSE 1' >> $file;;
  *) case "$has_sigsetmask" in
     yes) echo '#define USE_SIGSETMASK 1' >> $file;;
     esac;;
esac

case $has_dlopen in
yes) cat >> $file << EOT
#define HAS_DLOPEN
#define DL_DFLT_NAME "libpari.$sodest"
EOT
;;
esac

case $has_TIOCGWINSZ in
yes) echo '#define HAS_TIOCGWINSZ' >> $file;;
esac

case $has_strftime in
yes) echo '#define HAS_STRFTIME' >> $file;;
esac
echo '#endif' >> $file
