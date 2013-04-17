#!/bin/sh
aclocal || die "aclocal failed"
echo "Regenerating configure with autoconf "
echo autoconf --warnings=all -o ../configure configure.ac || die "autoconf failed"
autoconf --warnings=all -o ../configure configure.ac || die "autoconf failed"
