dir=examples
name=Makefile.$osname-$arch
file=$dir/$name
lnfile=Makefile

echo Extracting $file
rm -f $file $dir/$lnfile

case "$runpathprefix" in
  -R)       RUNPTH="-R$runpath";;
  *-rpath*) RUNPTH="$runpathprefix $runpath";;
esac

if test -z "$DLLD"; then static=y; fi
case "$static" in
  n) dft=dyn ;;
  y) dft=sta ;;
esac

# remove soname imformation
MYDLLDFLAGS=`echo $DLLDFLAGS | sed -e 's/-[hsoname]* \\$(LIBPARI.*)//'`

cat > $file << EOT
# Generic Makefile for PARI programs -- $pretty
#
#  This file was created by Configure. Any change made to it will be
#  lost when Configure is run.
#
# make all will create
#  matexp-dyn (linked dynamically with libpari)
#  matexp-sta (linked statically)
#  libmatexp.so (to be used by "install" under GP)
#
# Under GP: install(matexp, Gp, mexp, "./libmatexp.so") enables you to
# subsequently use mexp to call matexp (see the reference manual).
#

# change this TARGET to compile your own programs
TARGET = matexp
SHELL  = $make_sh

DBGFLAGS   = $DBGFLAGS $CFLAGS
CFLAGS     = $OPTFLAGS $CFLAGS
#CFLAGS    = \$(DBGFLAGS)

# Various linkers use different flags to force static compilation. Choose
# the one which is relevant for your installation.
#
# Solaris ld (global)
#STATIC    = -dn

# Solaris ld (toggle: no shared object accepted until -B dynamic is seen
#STATIC    = -B static

# gcc
#STATIC    = -static

CC         = $CC
CPPFLAGS   = -I. -I$includedir
LD         = $LD
LDFLAGS    = $LDFLAGS
DLLD       = $DLLD
DLLDFLAGS  = $MYDLLDFLAGS
EXTRADLLDFLAGS  = $EXTRADLLDFLAGS
EXTRALIBS  =

RUNPTH     = $RUNPTH
LIBDIR     = -L$libdir
DLCFLAGS   = $DLCFLAGS
LIBS       = $LIBS -lpari

RM = rm -f


OBJS = \$(TARGET).o
DYN = lib\$(TARGET).$DLSUFFIX
ALL = \$(TARGET)-sta \$(TARGET)-dyn \$(DYN)

dft: \$(TARGET)-$dft

all: \$(ALL)

sta: \$(TARGET)-sta

dyn: \$(TARGET)-dyn

dynlib: \$(DYN)

\$(DYN): \$(OBJS)
	\$(DLLD) -o \$@ \$(DLLDFLAGS) \$(OBJS) \$(EXTRADLLDFLAGS)

\$(TARGET)-sta: \$(OBJS)
	\$(LD) -o \$@ \$(LDFLAGS) \$< \$(LIBDIR) \$(EXTRALIBS) \$(STATIC) \$(LIBS)

\$(TARGET)-dyn: \$(OBJS)
	\$(LD) -o \$@ \$(LDFLAGS) \$< \$(RUNPTH) \$(LIBDIR) \$(LIBS)

%.o: %.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) \$<
clean:
	-\$(RM) *.o \$(ALL)
EOT

( cd $dir ; $ln_s $name $lnfile )

