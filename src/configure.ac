AC_PREREQ(2.59)
AC_INIT(FULL-PACKAGE-NAME, VERSION, BUG-REPORT-ADDRESS)
AC_CONFIG_SRCDIR([linfit.c])

# Checks for programs.
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_MAKE_SET

# Checks for libraries.
AC_CHECK_LIB([die], [die])
AC_CHECK_LIB([m], [asin])

# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST

# Checks for library functions.
AC_FUNC_MALLOC
AC_FUNC_MEMCMP
AC_FUNC_REALLOC
AC_TYPE_SIGNAL
AC_FUNC_STAT
AC_FUNC_VPRINTF
AC_CHECK_FUNCS([floor getcwd pow sqrt strchr strdup])

if test -f /proc/cpuinfo ; then
  if grep "^model name" /proc/cpuinfo | grep "Pentium III" > /dev/null ; then
    AC_SUBST([cpu_flags],[-march=pentium3])
  fi
  if grep "^model name" /proc/cpuinfo | grep "Pentium(R) 4" > /dev/null ; then
    AC_SUBST([cpu_flags],[-march=pentium4])
  fi
  if grep "^flags" /proc/cpuinfo | grep "sse" > /dev/null ; then
    AC_SUBST([fpu_flags],[-mfpmath=sse])
  fi
fi

AC_CONFIG_FILES([Makefile])

AC_OUTPUT
