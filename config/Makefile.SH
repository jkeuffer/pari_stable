file=$objdir/Makefile

case "$asmarch" in
  sparcv8*) ASMARCH=sparcv8;;
  *) ASMARCH=$asmarch;;
esac

echo Extracting $file
rm -f $file

# Path to directories
case "$config_dir" in /*) cfg=$config_dir ;; *) cfg=../$config_dir ;; esac
case "$data_dir"   in /*) data=$data_dir ;;  *) data=../$data_dir ;; esac
case "$doc_dir"    in /*) doc=$doc_dir ;;    *) doc=../$doc_dir ;; esac
case "$emacs_dir"  in /*) emx=$emacs_dir ;;  *) emx=../$emacs_dir ;; esac
case "$examples_dir" in /*) ex=$examples_dir ;; *) ex=../$examples_dir ;; esac
case "$misc_dir"   in /*) misc=$misc_dir ;;  *) misc=../$misc_dir ;; esac
case "$src_dir"    in /*) src=$src_dir ;;    *) src=../$src_dir ;; esac

# File lists
kernel="kernel mp"
inline="mpinl"
khlist="pariinl"

graph="plot plotport"
gp="gp gp_init gp_rl highlvl whatnow"
case "$osname" in
  cygwin*) graphdyn="plot-dyn plotport-dyn";
           gpdyn="gp-dyn gp_init-dyn gp_rl-dyn";;
esac

language=`ls $src_dir/language/*.c | sed 's,.*/\(.*\)\.c,\1,'`
basemath=`ls $src_dir/basemath/*.c | sed 's,.*/\(.*\)\.c,\1,'`
modules=`ls $src_dir/modules/*.c   | sed 's,.*/\(.*\)\.c,\1,'`

if test -s $src_dir/kernel/$ASMARCH/MakeVar.SH; then
  . $src_dir/kernel/$ASMARCH/MakeVar.SH
fi

case "$ASMARCH" in
  m68k) hlist=pari68k
  kerntest=kernel.old;; # OLD_CODES should be defined
  *) hlist=pariport
  kerntest=kernel;;
esac
hlist="pari paritype paricast paricom parierr parigen paristio parisys $hlist"

HEADERS=''
for f in $khlist; do
  HEADERS="$HEADERS $f.h";
done
for f in $hlist; do
  HEADERS="$HEADERS $src/headers/$f.h";
done

# We don't want to recompile everything when only changing a prototype
hlist="$hlist paridecl"

KERNOBJS=''
for f in $kernel; do
  KERNOBJS="$KERNOBJS $f\$(_O)"
done
OBJS=$KERNOBJS
for f in $basemath $modules $language; do
  OBJS="$OBJS $f\$(_O)"
done
OBJSGP=''
OBJSDGP=''
for f in $gp $graph; do
  OBJSGP="$OBJSGP $f\$(_O)"
  OBJSDGP="$OBJSDGP $f-dyn\$(_O)"
done
for f in $inline; do
  OBJS="$OBJS $f\$(_O)"
done

case "$which_graphic_lib" in
none)
  PLOTFILE=plotnull.c
  PLOTCFLAGS=
  PLOTLIBS=
  plotrunpath=
  ;;
gnuplot)
  PLOTFILE=plotgnuplot.c
  PLOTCFLAGS=
  GNUPLOT_OBJS="bitmap\$(_O) term\$(_O) util\$(_O) version\$(_O) stdfn\$(_O)"
  PLOTLIBS="$gnuplot_libs"
  plotrunpath=
  case "$osname" in
    os2) libgnuplot=$gnuplot/gnuplot.a;;
    *) libgnuplot=$gnuplot/libgnuplot.a;;
  esac
  ;;
X11)
  PLOTFILE=plotX.c
  PLOTCFLAGS=-I$Xincroot
  PLOTLIBS="-L$X11 -lX11 $extralib"
  if test "$osname" = concentrix; then PLOTLIBS="-lX11"; fi
  plotrunpath=$X11
  ;;
esac

case "$runpathprefix" in
  -R) RUNPTH_FINAL="-R$runpath"
      if test -n "$plotrunpath"; then
        RUNPTH_FINAL="$RUNPTH_FINAL -R$plotrunpath"
      fi
      RUNPTH="-R$TOP/$objdir $RUNPTH_FINAL";;
  *-rpath*)
      tmp="$runpath:$plotrunpath"
      RUNPTH_FINAL="$runpathprefix $tmp"
      RUNPTH="$runpathprefix $TOP/$objdir:$tmp";;
esac

if test -z "$DLLD"; then
  exec="gp-sta"; static=y
else
  exec="gp-sta gp-dyn"
fi
doexec="env \"LD_LIBRARY_PATH=.;\$\$LD_LIBRARY_PATH\" \$(SHELL) $src/test/dotest $sizeof_long"
case "$sizeof_long" in
  4) numbits=32;;
  8) numbits=64;;
esac
if test -z "$emacs"; then
  install_emacs_files=
  pari_elc=
else
  install_emacs_files=install_emacs_files
  pari_elc=$emx/pari.elc
fi
case "$static" in
  n) dft=dyn; libdft=lib-dyn;;
  y) dft=sta; libdft= ;;
esac

cat > $file << EOT
# Makefile for Pari/GP -- $pretty
#
#  This file was created by Configure. Any change made to it will be
#  lost when Configure is run.
#
SHELL      = $make_sh

AS         = $AS
ASFLAGS    = $ASFLAGS
AR	   = ar

CC         = $CC
CPPFLAGS   = -I. -I$src/headers
CFLAGS     = $cflags
LD         = $LD
LDFLAGS    = $LDFLAGS
DLLD       = $DLLD
DLLDFLAGS  = $DLLDFLAGS
EXTRADLLDFLAGS = $EXTRADLLDFLAGS
CPP        = $CPP

# HIGHLY EXPERIMENTAL (only tested with gmp-4.0 on ix86 and Ultra):
# If you've configured and compiled GMP and would like to tune PARI using
# the nice cycle counting functions in GMP, uncomment the 4 lines below
# (correct the first one to the path to your gmp source tree).
#
#GMP     = /some/directory/gmp-4.0/tune
#GMPFLAGS= -DGMP_TIMER
#GMPO1 = \$(GMP)/time.o \$(GMP)/freq.o
#GMPOBJS=\$(GMPO1) \$(GMPO2)
#
#You may need to add a few object files to GMPOBJS. On UltraSparc,
#uncomment the following line:
#GMPO2 = \$(GMP)/sparcv9.o

_O	   = .o
_A	   = .a
LIB_PREFIX = lib
LIBPARI    = \$(LIB_PREFIX)$libpari_base
LIBPARI_STA= \$(LIBPARI)\$(_A)
LIBPARI_SO = \$(LIBPARI).$DLSUFFIX
LIBPARI_DYN   = \$(LIBPARI_SO).$sodest
LIBPARI_SONAME= \$(LIBPARI_SO).$soname

RUNPTH       = $RUNPTH
RUNPTH_FINAL = $RUNPTH_FINAL
LDDYN        = $LDDYN
DLCFLAGS     = $DLCFLAGS
LIBS         = $LIBS
DYNLIBS      = $DYNLIBS
DYNFLAGS     = $DYNFLAGS
DYNRELOC     = $DYNRELOC

RM = rm -f
MV = mv -f
LN = $ln_s

# Change these installation directories to suit your needs.
# DESTDIR is used to install to a false hierachy (to build a Debian package)
INCLUDEDIR = \$(DESTDIR)$includedir
LIBDIR = \$(DESTDIR)$libdir
BINDIR = \$(DESTDIR)$bindir
DATADIR= \$(DESTDIR)$datadir
MANDIR = \$(DESTDIR)$mandir
ALLDIR = \$(DESTDIR)$miscdir
READMEDIR = \$(ALLDIR)
DOCDIR  = \$(ALLDIR)/doc
EMACSDIR= \$(ALLDIR)/emacs
EXDIR   = \$(ALLDIR)/examples
MISCDIR = \$(ALLDIR)/misc

INSTALL = $cfg/install
INSTALL_PROGRAM = \$(INSTALL)
INSTALL_DATA = \$(INSTALL) -m 644

# Graphic library.
PLOTFILE   = $PLOTFILE
PLOTCFLAGS = $PLOTCFLAGS
PLOTLIBS   = $PLOTLIBS
GNUPLOT_OBJS = $GNUPLOT_OBJS
# Try uncommenting this line if you're using X11 and linking fails:
#  PLOTLIBS=-L$X11 -lX11

EOT
if test -n "$readline"; then
cat >> $file << EOT

RLINCLUDE = $RLINCLUDE
RLLIBS    = $RLLIBS

EOT
fi

case "$ln_s" in
  *cp*) ln_objdir=".";;
  *)    ln_objdir="$objdir"
esac

cat >> $file << EOT
TOPLDDYN     = -L$TOP/$objdir \$(RLLIBS)

OBJS   = $OBJS
OBJSGP = $OBJSGP
OBJSDGP = $OBJSDGP

dft: gp $pari_elc
	-

gp: gp-$dft ../gp$suffix$exe_suff $libdft
	-

../gp$suffix$exe_suff: gp-$dft
	-\$(RM) \$@
	-\$(LN) $ln_objdir/gp-$dft$exe_suff \$@

all: $exec lib-sta

lib-sta: \$(LIBPARI_STA)
lib-dyn: \$(LIBPARI_DYN)

\$(LIBPARI_STA): \$(OBJS)
	-\$(RM) \$@
	\$(AR) r \$@ \$(OBJS)

kerntest\$(_O): ../src/test/kerntest.c 
	\$(CC) -c \$(CFLAGS) -I$src/language \$(CPPFLAGS) -o \$@ \$<

kerntest: $KERNOBJS mp\$(_O) kerntest\$(_O)
	\$(CC) \$(CFLAGS) \$(CPPFLAGS) -o \$@ $KERNOBJS kerntest\$(_O) \$(LIBS)

test-kernel:: kerntest
	@./kerntest > gp.out;\
	diff -c gp.out $src/test/$numbits/$kerntest > kern.dif;\
	if test -s kern.dif; then echo "KERNEL BUG"; else echo OK; fi

tune.o: $src/test/tune.c
	\$(CC) \$(CFLAGS) \$(GMPFLAGS) \$(CPPFLAGS) -o \$@ \$< -c

tune: tune-sta
	-\$(RM) tune
	-\$(LN) tune-sta tune
	-\$(LN) $ln_objdir/tune ../tune

tune-dyn: tune.o lib-dyn
	\$(CC) \$(LDFLAGS) \$(RUNPTH) -o \$@ \$< \$(GMPOBJS) -L. \$(LDDYN) \$(LIBS)
tune-sta: tune.o lib-sta
	\$(CC) \$(LDFLAGS) -o \$@ \$< \$(GMPOBJS) ./\$(LIBPARI_STA) \$(LIBS)
EOT

if test -n "$ranlib"; then
cat >> $file << EOT

EOT
fi
cat >> $file << EOT

gp-sta: \$(OBJS) \$(OBJSGP) \$(GNUPLOT_OBJS)
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJS) \$(OBJSGP) \$(GNUPLOT_OBJS) \$(RUNPTH) \$(RLLIBS) \$(PLOTLIBS) \$(LIBS)
EOT

cat >> $file << EOT

bench: $exec
	@$doexec
test-compat: $exec
	@$doexec -c
test-graphic: $exec
	@$doexec -g

cleantest:
	\$(RM) *.dif gp.out pari.ps

dobench::
	@$doexec
dotest-compat::
	@$doexec -c
dotest-graphic::
	@$doexec -g

cleanobj: cleantest
	-\$(RM) *\$(_O) *.s pariinl.h \$(LIBPARI_STA) libpari.* $exec

clean: cleanobj

.headers: $HEADERS
	@touch \$@

install: install-lib-$dft install-include install-bin install-man install-misc install-data install-doc install-examples

install-include:
	-mkdir -p \$(INCLUDEDIR)
	\$(INSTALL_DATA) paricfg.h                 \$(INCLUDEDIR)
	-for i in $khlist; do \\
	   \$(INSTALL_DATA) \$\$i.h                \$(INCLUDEDIR); done
	-for i in $hlist; do \\
	   \$(INSTALL_DATA) $src/headers/\$\$i.h   \$(INCLUDEDIR); done
	-\$(RM) \$(INCLUDEDIR)/genpari.h
	-\$(LN) pari.h \$(INCLUDEDIR)/genpari.h

install-bin: install-bin-$dft

install-bin-dyn: gp-dyn
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version \$(BINDIR)/gp$exe_suff
	-\$(LD) -o \$(BINDIR)/gp-$version \$(LDFLAGS) \$(OBJSGP) \$(RUNPTH_FINAL) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS)
	-strip \$(BINDIR)/gp-$version
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff

install-bin-sta: gp-sta
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version \$(BINDIR)/gp$exe_suff
	\$(INSTALL_PROGRAM) gp-sta$exe_suff \$(BINDIR)/gp-$version$exe_suff
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff
# Can't strip it if we want install() to work on Linux or OSF.
#	-strip \$(BINDIR)/gp-$version

install-man::
	-mkdir -p \$(MANDIR)
	\$(INSTALL_DATA) $doc/gphelp.1 \$(MANDIR)
	\$(INSTALL_DATA) $doc/gp.1 \$(MANDIR)
	-\$(RM) \$(MANDIR)/pari.1
	-\$(LN) gp.1 \$(MANDIR)/pari.1

install-misc: $install_emacs_files install-top
	-mkdir -p \$(MISCDIR) \$(BINDIR)
	\$(INSTALL_PROGRAM) $misc/tex2mail \$(BINDIR)
	\$(INSTALL_DATA) $doc/tex2mail.1 \$(MANDIR)
	\$(INSTALL_DATA) $misc/README    \$(MISCDIR)
	\$(INSTALL_DATA) $misc/color.dft \$(MISCDIR)
	\$(INSTALL_DATA) $misc/gpalias   \$(MISCDIR)
	\$(INSTALL_PROGRAM) $misc/gpflog \$(MISCDIR)
	\$(INSTALL_DATA) $misc/gprc.dft  \$(MISCDIR)
	\$(INSTALL_DATA) $misc/new.dic   \$(MISCDIR)
	\$(INSTALL_DATA) $misc/pari.xpm  \$(MISCDIR)
	\$(INSTALL_PROGRAM) $misc/xgp    \$(MISCDIR)

install-top::
	-mkdir -p \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/AUTHORS      \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/Announce.2.1 \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/CHANGES      \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/COMPAT       \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/COPYING      \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/CVS.txt      \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/MACHINES     \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/NEW          \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/README       \$(READMEDIR)
	\$(INSTALL_DATA) $TOP/TODO         \$(READMEDIR)

install-doc::
	-mkdir -p \$(BINDIR) \$(DOCDIR)
	-cd $doc; \$(MAKE) all
	-\$(INSTALL_PROGRAM) $doc/gphelp    \$(BINDIR)
	-\$(INSTALL_DATA) $doc/Makefile     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/translations \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/appa.tex     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/appb.tex     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/appc.tex     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/parimacro.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/pdfmacs.tex  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/refcard.tex  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/tutorial.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/users.tex    \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch1.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch2.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch3.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch4.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch5.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/paricfg.tex  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/users.dvi    \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/tutorial.dvi \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/refcard.dvi  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/refcard.ps   \$(DOCDIR)

install-examples:
	-mkdir -p \$(EXDIR)
	-\$(INSTALL_DATA) $ex/EXPLAIN     \$(EXDIR)
	-\$(INSTALL_DATA) $ex/Inputrc     \$(EXDIR)
	-\$(INSTALL_DATA) $ex/Makefile    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/bench.gp    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/cl.gp       \$(EXDIR)
	-\$(INSTALL_DATA) $ex/classno.gp  \$(EXDIR)
	-\$(INSTALL_DATA) $ex/contfrac.gp \$(EXDIR)
	-\$(INSTALL_DATA) $ex/lucas.gp    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/matexp.c    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/rho.gp      \$(EXDIR)
	-\$(INSTALL_DATA) $ex/squfof.gp   \$(EXDIR)
	-\$(INSTALL_DATA) $ex/taylor.gp   \$(EXDIR)

install-data:
	-mkdir -p \$(DATADIR)
	-for f in $data/*; do \$(INSTALL_DATA)  \$\$f \$(DATADIR); done 2>/dev/null

install-lib-sta: \$(LIBPARI_STA)
	-mkdir -p \$(LIBDIR)
	-\$(RM) \$(LIBDIR)/\$(LIBPARI_STA)
	\$(INSTALL_DATA) \$(LIBPARI_STA) \$(LIBDIR)/\$(LIBPARI_STA).$version
	-\$(LN) \$(LIBPARI_STA).$version \$(LIBDIR)/\$(LIBPARI_STA)

install-lib-dyn: \$(LIBPARI_DYN)
	-mkdir -p \$(LIBDIR)
	-\$(RM) \$(LIBDIR)/\$(LIBPARI_DYN)
	\$(INSTALL_PROGRAM) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_DYN)
EOT
if test "$soname" != "$sodest"; then
  cat >> $file << EOT
	-\$(RM) \$(LIBDIR)/\$(LIBPARI_SONAME)
	-\$(RM) \$(LIBDIR)/\$(LIBPARI_SO)
	-\$(LN) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SONAME)
	-\$(LN) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SO)

EOT
fi

if test -z "$DLLD"; then
  cat >> $file << EOT

\$(LIBPARI_DYN)::
	@echo "Configure could not find a way to build a shared library on this machine."

EOT
else
  if test -z "$DYNLIBS"; then
    cat >> $file << EOT
gp-dyn: \$(OBJSGP) \$(LIBPARI_DYN) \$(GNUPLOT_OBJS)
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJSGP) \$(GNUPLOT_OBJS) \$(RUNPTH) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS)

\$(LIBPARI_DYN): \$(OBJS)
	-\$(RM) \$(LIBPARI_DYN)
	\$(DLLD) -o \$@ \$(DLLDFLAGS) \$(OBJS) \$(EXTRADLLDFLAGS)
EOT
    if test "$soname" != "$sodest"; then
      cat >> $file << EOT
	-\$(RM) \$(LIBPARI_SONAME)
	-\$(RM) \$(LIBPARI_SO)
	-\$(LN) \$(LIBPARI_DYN) \$(LIBPARI_SONAME)
	-\$(LN) \$(LIBPARI_DYN) \$(LIBPARI_SO)
EOT
    fi
  else
    cat >> $file << EOT
gp-dyn: \$(OBJSDGP) \$(LIBPARI_DYN)
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJSDGP) \$(RUNPTH) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS) \$(DYNLIBS)
EOT
  fi
fi

if test -n "$GNUPLOT_OBJS"; then
cat >> $file << EOT
\$(GNUPLOT_OBJS):
	\$(AR) x $libgnuplot \$(GNUPLOT_OBJS)

EOT
fi

if test -n "$emacs"; then
  cat >> $file << EOT
$pari_elc: $emx/pari.el
	@echo "Byte-Compiling pari.el..."
	-cd $emx; $emacs -batch -l compile

$install_emacs_files: $pari_elc
	-mkdir -p \$(EMACSDIR)
	-\$(INSTALL_DATA)   $pari_elc           \$(EMACSDIR)
	\$(INSTALL_DATA)    $emx/pari.el        \$(EMACSDIR)
	\$(INSTALL_DATA)    $emx/pariemacs.txt  \$(EMACSDIR)
	\$(INSTALL_DATA)    $emx/with-syntax.el     \$(EMACSDIR)
	\$(INSTALL_DATA)    $emx/pari-translator.el \$(EMACSDIR)
EOT
fi

if test -s $src_dir/kernel/$ASMARCH/Makefile.SH; then
  . $src_dir/kernel/$ASMARCH/Makefile.SH
fi
HUGELINE=
for dir in basemath modules language gp graph gpdyn graphdyn; do
  eval list='$'$dir
  for f in $list; do

  source="$src/$dir/$f.c"
  depend=
  cflags=
  case "$f" in
  plot)
    source="$src/graph/\$(PLOTFILE)"
    cflags="\$(PLOTCFLAGS)"
    depend="$src/graph/rect.h"
    ;;
  gp|gp_rl)
    cflags="-I$src/language \$(RLINCLUDE)"
    depend="$src/language/anal.h $src/gp/gp.h ./paricfg.h"
    ;;
  gp_init|plotport)
    cflags="-I$src/graph"
    depend="$src/graph/rect.h"
    ;;
  plot-dyn)
    source="$src/graph/\$(PLOTFILE)"
    cflags="\$(DYNFLAGS) \$(PLOTCFLAGS)"
    depend="$src/graph/rect.h \$(LIBPARI).dll libpari_dll.h libpari_globals.h \$(LIBPARI).dll"
    ;;
  gp-dyn|gp_rl-dyn)
    source=$src\/`echo $dir | sed -e "s/dyn//"`\/`echo $f | cut -f1 -d-`.c
    cflags="\$(DYNFLAGS) -I$src/language \$(RLINCLUDE)"
    depend="$src/language/anal.h $src/gp/gp.h ./paricfg.h libpari_dll.h libpari_globals.h \$(LIBPARI).dll"
    ;;
  gp_init-dyn|plotport-dyn)
    source=$src\/`echo $dir | sed -e "s/dyn//"`\/`echo $f | cut -f1 -d-`.c
    cflags="\$(DYNFLAGS) -I$src/graph"
    depend="$src/graph/rect.h libpari_dll.h libpari_globals.h \$(LIBPARI).dll"
    ;;
  init|es|sumiter)
    depend="$src/language/anal.h"
    ;;
  anal)
    depend="$src/language/anal.h $src/headers/parinf.h"
    ;;
  base1|bibli1|buch2)
    depend="$src/headers/parinf.h"
    ;;
  esac

HUGELINE="$HUGELINE
$f\$(_O): .headers $depend $source
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) $cflags -o $f\$(_O) $source"
  done
done
#to avoid execing too many "cat".
echo "$HUGELINE" >> $file

if test -n "$DYNFLAGS"; then
  echo "include Makefile.DLLs" >> $file
  cp $config_dir/Makefile.DLLs $objdir
fi
