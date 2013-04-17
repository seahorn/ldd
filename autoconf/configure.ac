dnl **************************************************************************
dnl * Initialize
dnl **************************************************************************
AC_INIT([[LDD]],[[1.0]],[arie@cmu.edu])

dnl Basic configure to detect compilation flags

AC_CONFIG_AUX_DIR(autoconf)

dnl Verify that the source directory is valid
AC_CONFIG_SRCDIR(["src/Makefile.common.in"])

dnl Configure a common Makefile
AC_CONFIG_FILES([src/Makefile.common cudd-2.4.2/Makefile])

dnl Configure project makefiles
dnl List every Makefile that exists within your source tree
dnl AC_CONFIG_MAKEFILE(Makefile)
dnl AC_CONFIG_MAKEFILE(lib/Makefile)
dnl AC_CONFIG_MAKEFILE(tools/Makefile)


dnl **************************************************************************
dnl * Determine which system we are building on
dnl **************************************************************************

dnl **************************************************************************
dnl * Check for programs.
dnl **************************************************************************

dnl **************************************************************************
dnl * Check for libraries.
dnl **************************************************************************



dnl **************************************************************************
dnl * Checks for header files.
dnl **************************************************************************

dnl **************************************************************************
dnl * Checks for typedefs, structures, and compiler characteristics.
dnl **************************************************************************

dnl **************************************************************************
dnl * Checks for library functions.
dnl **************************************************************************

dnl **************************************************************************
dnl * Enable various compile-time options
dnl **************************************************************************

dnl **************************************************************************
dnl * Set the location of various third-party software packages
dnl **************************************************************************

dnl **************************************************************************
dnl * Create the output files
dnl **************************************************************************

AC_LANG([C])

dnl **************************************************************************
dnl Find the host

AC_CANONICAL_TARGET

AC_CHECK_SIZEOF([void *])
AC_SUBST(SIZEOF_VOID_P, $ac_cv_sizeof_void_p)

AC_CHECK_SIZEOF([long])
AC_SUBST(SIZEOF_LONG, $ac_cv_sizeof_long)

dnl This must be last
AC_OUTPUT
