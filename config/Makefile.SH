file=$objdir/Makefile

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

graph="plotport"
gp="gp gp_init gp_rl highlvl whatnow"

language=`ls $src_dir/language/*.c | sed 's,.*/\(.*\)\.c,\1,'`
basemath=`ls $src_dir/basemath/*.c | sed 's,.*/\(.*\)\.c,\1,'`
modules=`ls $src_dir/modules/*.c   | sed 's,.*/\(.*\)\.c,\1,'`
systems=
if test -d "$src_dir/systems/$osname"; then
  systems=`ls $src_dir/systems/$osname/*.c | sed 's,.*/\(.*\)\.c,\1,'`
fi
lib_prefix=lib
dllib_prefix=lib
case "$osname" in
  os2)  dllib_prefix=	# != lib_prefix to allow gp-dyn link with DLL
	export_lib_create=emximp; export_lib='$(DLLIBPARI)$(_A)'
	export_file=pari.def; export_create="emxexp -u"
	# Actually, the build will fail until the switch to -Zomf
	dlld_ignore=- ;;
esac

hlist='pari paritype paricast paricom parierr parigen paristio parisys pariport'
HEADERS=pariinl.h
for f in $hlist; do
  HEADERS="$HEADERS $src/headers/$f.h";
done

# We don't want to recompile everything when only changing a prototype
hlist="$hlist paridecl"

case "$graphic_lib_dll" in
  NULL)	_graphic_lib_dll="$graphic_lib_dll" ;;
  *)	_graphic_lib_dll="\\\"$graphic_lib_dll\\\"" ;;
esac
case "$osname" in
  cygwin) WIN_LIBS="-lgdi32 -lole32 -luuid -lwsock32 -lsupc++";;
esac
case "$which_graphic_lib" in
none)
  PLOTCFLAGS=
  PLOTLIBS=
  plotrunpath=
  graph="$graph plotnull"
  ;;
qt)
  PLOTCFLAGS='-D__FANCY_WIN__ -I$(QTDIR)/include'
  PLOTLIBS='-L$(QTDIR)/lib -lqt'
  graph="$graph plotQt"
  ;;
fltk)
  PLOTCFLAGS="-I\$(FLTKDIR)/include $X11_INC"
  PLOTLIBS="-L\$(FLTKDIR)/lib -lfltk $X11_LIBS $WIN_LIBS"
  graph="$graph plotfltk"
  ;;
gnuplot)
  PLOTCFLAGS=
  GNUPLOT_OBJS="bitmap\$(_O) term\$(_O) util\$(_O) version\$(_O) stdfn\$(_O)"
  PLOTLIBS="$gnuplot_libs"
  plotrunpath=
  case "$osname" in
    os2) libgnuplot=$gnuplot/gnuplot.a;;
    *) libgnuplot=$gnuplot/libgnuplot.a;;
  esac
  graph="$graph plotgnuplot"
  ;;
gnuplot-dynamic)
  PLOTCFLAGS="-DDYNAMIC_PLOTTING -DDYNAMIC_PLOTTING_RUNTIME_LINK=$_graphic_lib_dll"
  PLOTLIBS=
  plotrunpath=
  graph="$graph plotgnuplot"
  ;;
builtin.X11-gnuplot)
  CFLAGS="$CFLAGS -DBOTH_GNUPLOT_AND_X11"
  PLOTCFLAGS=$X11_INC
  GNUPLOT_OBJS="bitmap\$(_O) term\$(_O) util\$(_O) version\$(_O) stdfn\$(_O)"
  PLOTLIBS="$gnuplot_libs $X11_LIBS"
  plotrunpath=$X11
  case "$osname" in
    os2) libgnuplot=$gnuplot/gnuplot.a;;
    *) libgnuplot=$gnuplot/libgnuplot.a;;
  esac
  graph="$graph plotgnuplot plotX"
  ;;
builtin.X11-gnuplot-dynamic)
  CFLAGS="$CFLAGS -DBOTH_GNUPLOT_AND_X11"
  PLOTCFLAGS="$X11_INC -DDYNAMIC_PLOTTING -DDYNAMIC_PLOTTING_RUNTIME_LINK=$_graphic_lib_dll"
  PLOTLIBS=$X11_LIBS
  plotrunpath=$X11
  graph="$graph plotgnuplot plotX"
  ;;
X11)
  PLOTCFLAGS=$X11_INC
  PLOTLIBS=$X11_LIBS
  plotrunpath=$X11
  graph="$graph plotX"
  ;;
esac

KERNOBJS=''
for f in $kernel; do
  KERNOBJS="$KERNOBJS $f\$(_O)"
done
OBJS=$KERNOBJS
for f in $basemath $modules $language $systems; do
  OBJS="$OBJS $f\$(_O)"
done
OBJSGP=''
OBJSDGP=''

for f in $gp $graph; do
  OBJSGP="$OBJSGP $f\$(_O)"
done
for f in $inline; do
  OBJS="$OBJS $f\$(_O)"
done

tmp=$runpath
if test -n "$plotrunpath"; then
  tmp="$tmp$dir_sep$plotrunpath"
fi
if test -n "$gmp"; then
  tmp="$tmp$dir_sep$gmp"
fi
case "$tmp" in
  /usr/lib);;
  *$dir_sep/usr/lib);;
  *$dir_sep/usr/lib$dir_sep);;
  *) tmp="$tmp$dir_sep/usr/lib";;
esac
RUNPTH_FINAL=
RUNPTH=
if test -n "$runpathprefix"; then
  RUNPTH_FINAL=`$config_dir/ldflags "$LDneedsWl" "$runpathprefix$tmp"`
  RUNPTH=`$config_dir/ldflags "$LDneedsWl" "$runpathprefix$TOP/$objdir$dir_sep$tmp"`
fi

if test -z "$DLLD"; then
  exec="gp-sta"; static=y
else
  exec="gp-sta gp-dyn"
fi
doexec="env \"LD_LIBRARY_PATH=.$dir_sep\$\$LD_LIBRARY_PATH\" \$(SHELL) $src/test/dotest \$(SIZEOF_LONG)"
case "$sizeof_long" in
  4) numbits=32;;
  8) numbits=64;;
esac
if test -z "$emacs"; then
  install_emacs_files=
else
  install_emacs_files=install_emacs_files
fi
case "$static" in
  n) dft=dyn; libdft=lib-dyn;;
  y) dft=sta; libdft= ;;
esac

CPPFLAGS="-I. -I$src/headers"
if test "$has_dlopen" = builtin; then
  CPPFLAGS="$CPPFLAGS -I$src/systems/$osname"
fi

case "$ln_s" in
  *cp*) ln_objdir=".";;
  *)    ln_objdir="$objdir"
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

SIZEOF_LONG= $sizeof_long

CC_FLAVOR  =
CC         = $CC \$(CC_FLAVOR)
CPPFLAGS   = $CPPFLAGS
CFLAGS     = $CFLAGS
LD_FLAVOR  = \$(CC_FLAVOR)
LD         = $LD \$(LD_FLAVOR)
LDFLAGS    = $LDFLAGS
DLLD_FLAVOR  = \$(LD_FLAVOR)
DLLD       = $DLLD \$(DLLD_FLAVOR)
DLLDFLAGS  = $DLLDFLAGS
EXTRADLLDFLAGS = $EXTRADLLDFLAGS
CPP        = $CPP

# HIGHLY EXPERIMENTAL (only tested with gmp-4.0 on ix86 and Ultra).
# If you've configured and compiled GMP and would like to tune PARI using
# the nice cycle counting functions in GMP, uncomment the 4 lines below
# (correct the first one to the path to your gmp source tree).
#
#GMP     = /some/directory/gmp-4.0/tune
#GMPFLAGS= -DGMP_TIMER
#GMPO1 = \$(GMP)/time.o \$(GMP)/freq.o
#GMPOBJS=\$(GMPO1) \$(GMPO2)
#
#You may need to add a few object files to GMPOBJS. On UltraSparc, uncomment
#the following line
#GMPO2 = \$(GMP)/sparcv9.o

_O	   = .o
_A	   = .a
LIB_PREFIX = $lib_prefix
DLLIB_PREFIX = $dllib_prefix
LIBPARI_BASE = $libpari_base
LIBPARI      = \$(LIB_PREFIX)\$(LIBPARI_BASE)
DLLIBPARI    = \$(DLLIB_PREFIX)\$(LIBPARI_BASE)
LIBPARI_STA  = \$(LIBPARI)\$(_A)
LIBPARI_SO   = \$(DLLIBPARI).$DLSUFFIX
LIBPARI_DYN   = \$(LIBPARI_SO)$sodest
LIBPARI_SONAME= \$(LIBPARI_SO)$soname
EXPORT_FILE   = $export_file
EXPORT_CREATE = $export_create
EXPORT_LIB = $export_lib
EXPORT_LIB_CREATE = $export_lib_create
DLLD_IGNORE = $dlld_ignore

RUNPTH       = $RUNPTH
RUNPTH_FINAL = $RUNPTH_FINAL
LDDYN        = $LDDYN
DLCFLAGS     = $DLCFLAGS
LIBS         = $LIBS

RM = rm -f
MV = mv -f
LN = $ln_s
CP_F = cp -f
STRIP      = strip
STRIPFLAGS =

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

# Readline
RLINCLUDE = $RLINCLUDE
RLLIBS    = $RLLIBS
# GMP
GMPINCLUDE = $GMPINCLUDE
# Graphic library.
QTDIR      = $QTDIR
MOC        = \$(QTDIR)/bin/moc
PLOTCFLAGS = $PLOTCFLAGS
PLOTLIBS   = $PLOTLIBS
GNUPLOT_OBJS = $GNUPLOT_OBJS
CPLUSPLUS  = g++

FLTKDIR    = $FLTKDIR

TOPLDDYN     = -L$TOP/$objdir \$(RLLIBS)

OBJS   = $OBJS
OBJSGP = $OBJSGP
OBJSDGP = $OBJSDGP

gp: gp-$dft ../gp$suffix$exe_suff $libdft

../gp$suffix$exe_suff: gp-$dft
	-\$(RM) \$@
	-\$(LN) $ln_objdir/gp-$dft$exe_suff \$@

all: $exec lib-sta

lib-sta: \$(LIBPARI_STA)
lib-dyn: \$(LIBPARI_DYN)

\$(LIBPARI_STA): $src/funclist \$(OBJS)
	-\$(RM) \$@
	\$(AR) r \$@ \$(OBJS)
EOT
if test -n "$ranlib"; then
cat >> $file << EOT
	$ranlib \$@

EOT
fi
cat >> $file << EOT

kerntest\$(_O): ../src/test/kerntest.c
	\$(CC) -c \$(CFLAGS) -I$src/language \$(CPPFLAGS) -o \$@ \$<

kerntest: $KERNOBJS mp\$(_O) kerntest\$(_O)
	\$(CC) \$(CFLAGS) \$(CPPFLAGS) -o \$@ $KERNOBJS kerntest\$(_O) \$(LIBS)

test-kernel:: kerntest
	@./kerntest > gp.out;\
	diff -c gp.out $src/test/$numbits/kernel > kern.dif;\
	if test -s kern.dif; then echo "KERNEL BUG"; else echo OK; fi

tune.o: $src/test/tune.c
	\$(CC) \$(CFLAGS) \$(GMPFLAGS) \$(CPPFLAGS) -o \$@ \$< -c

tune: tune-sta
	-\$(RM) tune ../tune
	-\$(LN) tune-sta tune
	-\$(LN) $ln_objdir/tune ../tune

tune-dyn: tune.o lib-dyn
	\$(LD) \$(LDFLAGS) \$(RUNPTH) -o \$@ \$< \$(GMPOBJS) -L. \$(LDDYN) \$(LIBS)
tune-sta: tune.o lib-sta
	\$(LD) \$(LDFLAGS) -o \$@ \$< \$(GMPOBJS) ./\$(LIBPARI_STA) \$(LIBS)

gp-sta: $src/funclist \$(OBJS) \$(OBJSGP) \$(GNUPLOT_OBJS)
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
dobench::
	@$doexec
dotest-compat::
	@$doexec -c
dotest-graphic::
	@$doexec -g

cleanemacs:
	\$(RM) $emx/*.elc
cleantest:
	\$(RM) *.dif gp.out pari.ps
cleanobj:
	-\$(RM) *\$(_O) mp.c *.s pariinl.h parilvl0.h parilvl1.h libpari* tune* $exec

clean: cleanobj cleantest cleanemacs

.headers: $HEADERS
	@touch \$@

install: install-lib-$dft install-include install-bin install-man install-misc install-data install-doc install-examples

install-include:
	-mkdir -p \$(INCLUDEDIR)
	\$(INSTALL_DATA) paricfg.h                \$(INCLUDEDIR)
	\$(INSTALL_DATA) pariinl.h                \$(INCLUDEDIR)
	-for i in $hlist; do \\
	   \$(INSTALL_DATA) $src/headers/\$\$i.h  \$(INCLUDEDIR); done
	-\$(RM) \$(INCLUDEDIR)/genpari.h
	-\$(LN) pari.h \$(INCLUDEDIR)/genpari.h

install-bin: install-bin-$dft

install-bin-dyn: gp-dyn
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version \$(BINDIR)/gp$exe_suff
	-\$(LD) -o \$(BINDIR)/gp-$version \$(LDFLAGS) \$(OBJSGP) \$(RUNPTH_FINAL) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS)
	-\$(STRIP) \$(STRIPFLAGS) \$(BINDIR)/gp-$version
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff

install-bin-sta: gp-sta
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version \$(BINDIR)/gp$exe_suff
	\$(INSTALL_PROGRAM) gp-sta$exe_suff \$(BINDIR)/gp-$version$exe_suff
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff
# Can't strip it if we want install() to work on Linux or OSF.
# Note: it seems that strip work on linux.
#	-\$(STRIP) \$(STRIPFLAGS)  \$(BINDIR)/gp-$version

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
	-if test "\$(LIBPARI_SONAME)" != "\$(LIBPARI_SO)"; then \
	  \$(RM) \$(LIBDIR)/\$(LIBPARI_SONAME);\
	  \$(RM) \$(LIBDIR)/\$(LIBPARI_SO);\
	  \$(LN) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SONAME);\
	  \$(LN) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SO); fi

EOT

if test -z "$DLLD"; then
  cat >> $file << EOT

\$(LIBPARI_DYN)::
	@echo "Configure could not find a way to build a shared library on this machine."

EOT
else
  if test -n "$export_file"; then
    cat >> $file << EOT

EXPORT_FILE_BASE = $src/systems/os2/pari.def.base
VERSION_VERBOSE = $pari_release_verbose

\$(EXPORT_FILE): \$(OBJS) \$(EXPORT_FILE_BASE)
	cat \$(EXPORT_FILE_BASE) | sed 's/<DLL_BASE>/\$(DLLIBPARI)/' | sed 's/<VENDOR>/www.parigp-home.de\//' | sed 's/<VERSION>/\$(VERSION_VERBOSE)/' | sed 's/<DESCR>/GP\/PARI compiled with \$(CFLAGS)/' > \$@
	\$(EXPORT_CREATE) \$(OBJS) >> \$@

\$(DLLIBPARI)\$(_A): \$(EXPORT_FILE)
	\$(EXPORT_LIB_CREATE) -o \$@ \$(EXPORT_FILE)

EOT
  fi
  cat >> $file << EOT

gp-dyn: $src/funclist \$(OBJSGP) \$(LIBPARI_DYN) \$(GNUPLOT_OBJS) \$(EXPORT_LIB)
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJSGP) \$(GNUPLOT_OBJS) \$(RUNPTH) \$(TOPLDDYN) \$(LDDYN) \$(PLOTLIBS) \$(LIBS)

\$(LIBPARI_DYN): $src/funclist \$(OBJS) \$(EXPORT_FILE)
	-\$(RM) \$(LIBPARI_DYN)
	\$(DLLD_IGNORE)\$(DLLD) -o \$@ \$(DLLDFLAGS) \$(OBJS) \$(EXTRADLLDFLAGS) \$(EXPORT_FILE)
	-if test "\$(LIBPARI_SONAME)" != "\$(LIBPARI_SO)"; then \
	  \$(RM) \$(LIBPARI_SONAME);\
	  \$(RM) \$(LIBPARI_SO);\
	  \$(LN) \$(LIBPARI_DYN) \$(LIBPARI_SONAME);\
	  \$(LN) \$(LIBPARI_DYN) \$(LIBPARI_SO); fi
EOT
fi

if test -n "$GNUPLOT_OBJS"; then
cat >> $file << EOT
\$(GNUPLOT_OBJS):
	\$(AR) x $libgnuplot \$(GNUPLOT_OBJS)

EOT
fi

if test -n "$emacs"; then
  cat >> $file << EOT
elc:
	@echo "Byte-Compiling elisp files..."
	-cd $emx; $emacs -batch \
	   --eval '(setq load-path (append (list ".") load-path))' \
	   -f batch-byte-compile *.el

$install_emacs_files: elc
	-mkdir -p \$(EMACSDIR)
	-cd $emx; for f in *.elc *.el pariemacs.txt; do \
	  \$(INSTALL_DATA) \$\$f \$(EMACSDIR); \
	done
EOT
fi

cat >> $file << EOT
pariinl.h: parilvl0.h parilvl1.h
	cat parilvl0.h parilvl1.h > pariinl.h

$src/funclist::
	@ls -l $src/functions/*/* > $src/funclist.tmp
	@sh $cfg/mv-if-diff $src/funclist.tmp $src/funclist

$src/desc/Def: $src/funclist
	cd $src/desc; $(MAKE) Def

$src/gp/gp_init.h $src/gp/highlvl.h $src/language/init.h: $src/desc/Def 
	cd $src/desc; $(MAKE)
EOT

if test -s $src_dir/kernel/$kernlvl0/MakeLVL0.SH; then
  . $src_dir/kernel/$kernlvl0/MakeLVL0.SH
fi
if test -s $src_dir/kernel/$kernlvl1/MakeLVL1.SH; then
  . $src_dir/kernel/$kernlvl1/MakeLVL1.SH
fi

HUGELINE=
for dir in basemath modules language gp graph gpdyn graphdyn systems; do
  eval list='$'$dir
  if test "$dir" = systems; then
    SRC=$src/$dir/$osname
  else
    SRC=$src/$dir
  fi
  for f in $list; do

  source="$SRC/$f.c"
  depend=
  cflags="\$(CFLAGS) \$(CPPFLAGS)"
  compile='$(CC)'
  case "$f" in
  gp|gp_rl)
    cflags="$cflags -I$src/language \$(RLINCLUDE)"
    depend="$src/language/anal.h $src/gp/gp.h ./paricfg.h"
    ;;
  gp_init)
    cflags="$cflags -I$src/graph"
    depend="$src/graph/rect.h $src/gp/gp_init.h"
    ;;
  plotport)
    cflags="$cflags -I$src/graph"
    depend="$src/graph/rect.h"
    ;;
  highlvl)
    depend="$src/gp/highlvl.h"
    ;;
  plotQt)
    cflags="$cflags \$(PLOTCFLAGS)"
    depend="$src/graph/rect.h"
    compile="\$(MOC) -o plotQt.moc.cpp $src/graph/plotQt.c && \$(CPLUSPLUS)"
    ;;
  plotfltk)
    cflags="$cflags \$(PLOTCFLAGS)"
    depend="$src/graph/rect.h"
    compile="\$(CPLUSPLUS)"
    ;;
  plot*)
    cflags="$cflags \$(PLOTCFLAGS)"
    depend="$src/graph/rect.h"
    ;;
  es|sumiter)
    depend="$src/language/anal.h"
    ;;
  init)
    depend="$src/language/anal.h $src/language/init.h"
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
	$compile -c $cflags -o $f\$(_O) $source"
  done
done
#to avoid execing too many "cat".
echo "$HUGELINE" >> $file

echo ".PHONY: gp dft clean"  >> $file
