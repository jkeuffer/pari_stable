file=$objdir/Makefile

if test ! -s $src_dir/kernel/$asmarch/Makefile.SH; then
  echo "No Makefile for asmarch $asmarch !" >&2; fi

echo Extracting $file
rm -f $file

# Path to directories
case "$src_dir"    in /*) src=$src_dir ;;    *) src=../$src_dir ;; esac
case "$data_dir"   in /*) data=$data_dir ;;  *) data=../$data_dir ;; esac
case "$doc_dir"    in /*) doc=$doc_dir ;;    *) doc=../$doc_dir ;; esac
case "$emacs_dir"  in /*) emx=$emacs_dir ;;  *) emx=../$emacs_dir ;; esac
case "$config_dir" in /*) cfg=$config_dir ;; *) cfg=../$config_dir ;; esac

# File lists
kernel="kernel mp"
inline="mpinl"
khlist="pariinl"
. $src_dir/kernel/$asmarch/Makefile.SH

graph="plot plotport"
gp="gp gp_init gp_rl highlvl whatnow"
case "$osname" in
  cygwin*) graphdyn="plot-dyn plotport-dyn";
           gpdyn="gp-dyn gp_init-dyn gp_rl-dyn";;
esac

language=`ls $src_dir/language/*.c | sed 's,.*/\(.*\)\.c,\1,'`
basemath=`ls $src_dir/basemath/*.c | sed 's,.*/\(.*\)\.c,\1,'`
modules=`ls $src_dir/modules/*.c   | sed 's,.*/\(.*\)\.c,\1,'`

if test m68k = "$asmarch"; then hlist=pari68k; else hlist=pariport; fi
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

OBJS=''
for f in $kernel $basemath $modules $language; do
  OBJS="$OBJS $f.o"
done
OBJSGP=''
OBJSDGP=''
for f in $gp $graph; do
  OBJSGP="$OBJSGP $f.o"
  OBJSDGP="$OBJSDGP $f-dyn.o"
done
OINLINE=''
for f in $inline; do
  if test -n "$__gnuc__" -a "$optimization" != debugging; then
    OINLINE="$OINLINE $f.o"
  else
    OBJS="$OBJS $f.o"
  fi
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
  GNUPLOT_OBJS="bitmap.o term.o util.o version.o stdfn.o"
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
doexec="env \"LD_LIBRARY_PATH=.;\$\$LD_LIBRARY_PATH\" $src/test/dotest $sizeof_long"
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

CC         = $CC
CPPFLAGS   = -I. -I$src/headers
CFLAGS     = $cflags
LD         = $LD
LDFLAGS    = $LDFLAGS
DLLD       = $DLLD
DLLDFLAGS  = $DLLDFLAGS
EXTRADLLDFLAGS  = $EXTRADLLDFLAGS
CPP        = $CPP

RUNPTH       = $RUNPTH
RUNPTH_FINAL = $RUNPTH_FINAL
LDDYN        = $LDDYN
DLCFLAGS     = $DLCFLAGS
LIBS = -lm $LIBS
DYNLIBS      = $DYNLIBS
DYNFLAGS     = $DYNFLAGS
DYNRELOC     = $DYNRELOC

RM = rm -f
MV = mv -f
LN = $ln_s

# Change these installation directories to suit your needs.

LIBDIR = $libdir
BINDIR = $bindir
DATADIR= $datadir
MANDIR = $mandir
MISCDIR = $miscdir
INCLUDEDIR = $includedir

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
OINLINE = $OINLINE

dft: gp $pari_elc
	-

gp: gp-$dft ../gp$suffix$exe_suff $libdft
	-

../gp$suffix$exe_suff: gp-$dft
	-\$(RM) \$@
	-\$(LN) $ln_objdir/gp-$dft$exe_suff \$@

all: $exec lib-sta

lib-sta: libpari.a
lib-dyn: libpari.$somake

libpari.a: \$(OBJS) \$(OINLINE)
	-\$(RM) \$@
	ar r \$@  \$(OBJS) \$(OINLINE)
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

bench: $exec dobench
test-compat: $exec dotest-compat
test-graphic: $exec dotest-graphic

cleantest:
	\$(RM) *.dif gp.out pari.ps

dobench::
	@$doexec
dotest-compat::
	@$doexec -c
dotest-graphic::
	@$doexec -g

clean: cleantest
	-\$(RM) *.o *.s pariinl.h libpari.* $exec

.headers: $HEADERS
	@touch \$@

install: install-lib-$dft install-include install-bin install-man install-misc install-data install-doc

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
	strip \$(BINDIR)/gp-$version
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff

install-bin-sta: gp-sta
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version \$(BINDIR)/gp$exe_suff
	\$(INSTALL_PROGRAM) gp-sta$exe_suff \$(BINDIR)/gp-$version$exe_suff
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff
# Can't strip it if we want install() to work on Linux or OSF.
#	strip \$(BINDIR)/gp-$version

install-man::
	-mkdir -p \$(MANDIR)
	\$(INSTALL_DATA) $doc/gphelp.1 \$(MANDIR)
	\$(INSTALL_DATA) $doc/gp.1 \$(MANDIR)
	-\$(RM) \$(MANDIR)/pari.1
	-\$(LN) \$(MANDIR)/gp.1 \$(MANDIR)/pari.1

install-misc: $install_emacs_files
	-mkdir -p \$(MISCDIR)
	\$(INSTALL_PROGRAM) $doc/gphelp       \$(BINDIR)
	\$(INSTALL_DATA)    $doc/translations \$(MISCDIR)

install-doc:
	-cd $doc; \$(MAKE) all
	-\$(INSTALL_DATA) $doc/paricfg.tex   \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/parimacro.tex \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/usersch1.tex \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/usersch2.tex \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/usersch3.tex \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/usersch4.tex \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/usersch5.tex \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/users.dvi    \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/tutorial.dvi \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/refcard.dvi  \$(MISCDIR)
	-\$(INSTALL_DATA) $doc/refcard.ps   \$(MISCDIR)

install-data:
	-mkdir -p \$(DATADIR)
	@-for f in $data/*; do \$(INSTALL_DATA)  \$\$f \$(DATADIR); done 2>/dev/null

install-lib-sta: libpari.a
	-mkdir -p \$(LIBDIR)
	-\$(RM) \$(LIBDIR)/libpari.a
	\$(INSTALL_DATA) libpari.a \$(LIBDIR)/libpari.a.$version
	-\$(LN) libpari.a.$version \$(LIBDIR)/libpari.a

install-lib-dyn: libpari.$somake
	-mkdir -p \$(LIBDIR)
	-\$(RM) \$(LIBDIR)/libpari.$sodest
	\$(INSTALL_DATA) libpari.$sodest \$(LIBDIR)/libpari.$sodest
EOT
if test "$somake" != "$sodest"; then
  cat >> $file << EOT
	-\$(RM) \$(LIBDIR)/libpari.$somake
	-\$(LN) libpari.$sodest \$(LIBDIR)/libpari.$somake
	-\$(RM) \$(LIBDIR)/libpari.$DLSUFFIX
	-\$(LN) libpari.$sodest \$(LIBDIR)/libpari.$DLSUFFIX

EOT
fi

if test -z "$DLLD"; then
  cat >> $file << EOT

libpari.$somake::
	@echo "Configure could not find a way to build a shared library on this machine."

EOT
else
  if test -z "$DYNLIBS"; then
    cat >> $file << EOT
gp-dyn: \$(OBJSGP) libpari.$somake \$(GNUPLOT_OBJS)
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJSGP) \$(GNUPLOT_OBJS) \$(RUNPTH) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS)

libpari.$somake: \$(OBJS) \$(OINLINE)
	-\$(RM) libpari.$somake
	\$(DLLD) -o \$@ \$(DLLDFLAGS) \$(OBJS) \$(OINLINE) \$(EXTRADLLDFLAGS)
EOT
# CYGWIN32 FIXME: somake & sodest make no difference...
    if test "$somake" != "$sodest"; then
      cat >> $file << EOT
	-\$(RM) libpari.$sodest
	-\$(MV) libpari.$somake libpari.$sodest
	-\$(LN) libpari.$sodest libpari.$somake
	-\$(RM) libpari.$DLSUFFIX
	-\$(LN) libpari.$sodest libpari.$DLSUFFIX
EOT
    fi
  else
    cat >> $file << EOT
gp-dyn: \$(OBJSDGP) libpari.$somake
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJSDGP) \$(RUNPTH) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS) \$(DYNLIBS)
EOT
  fi
fi

if test -n "$GNUPLOT_OBJS"; then
cat >> $file << EOT
\$(GNUPLOT_OBJS):
	ar x $libgnuplot \$(GNUPLOT_OBJS)

EOT
fi

if test -n "$emacs"; then
  cat >> $file << EOT
$pari_elc: $emx/pari.el
	@echo "Byte-Compiling pari.el..."
	-cd $emx; $emacs -batch -l compile

$install_emacs_files: $pari_elc
	-mkdir -p \$(MISCDIR)
	-\$(INSTALL_DATA)   $pari_elc           \$(MISCDIR)
	\$(INSTALL_DATA)    $emx/pari.el        \$(MISCDIR)
	\$(INSTALL_DATA)    $emx/pariemacs.txt  \$(MISCDIR)
	\$(INSTALL_DATA)    $emx/with-syntax.el     \$(MISCDIR)
	\$(INSTALL_DATA)    $emx/pari-translator.el \$(MISCDIR)
EOT
fi

if test -s $src_dir/kernel/$asmarch/Makefile.SH; then
  . $src_dir/kernel/$asmarch/Makefile.SH rules
else
  echo "No Makefile for asmarch $asmarch !" >&2
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
    depend="$src/graph/rect.h libpari.dll libpari_dll.h libpari_globals.h libpari.dll"
    ;;
  gp-dyn|gp_rl-dyn)
    source=$src\/`echo $dir | sed -e "s/dyn//"`\/`echo $f | cut -f1 -d-`.c
    cflags="\$(DYNFLAGS) -I$src/language \$(RLINCLUDE)"
    depend="$src/language/anal.h $src/gp/gp.h ./paricfg.h libpari_dll.h libpari_globals.h libpari.dll"
    ;;
  gp_init-dyn|plotport-dyn)
    source=$src\/`echo $dir | sed -e "s/dyn//"`\/`echo $f | cut -f1 -d-`.c
    cflags="\$(DYNFLAGS) -I$src/graph"
    depend="$src/graph/rect.h libpari_dll.h libpari_globals.h libpari.dll"
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
$f.o: .headers $depend $source
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) $cflags -o $f.o $source"
  done
done
#to avoid execing too many "cat".
echo "$HUGELINE" >> $file

if test -n "$DYNFLAGS"; then
  echo "include Makefile.DLLs" >> $file
  cp $config_dir/Makefile.DLLs $objdir
fi
