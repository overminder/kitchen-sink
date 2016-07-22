#ifndef _COMMON_HPP
#define _COMMON_HPP

#include <cstdio>

#ifdef DCHECK_IS_ON
# define DCHECK(x) dcheck(x, __FILE__, __LINE__, #x)
static void dcheck(bool ok, const char *fileName, int line, const char *expr) {
  if (!ok) {
    fprintf(stderr, "%s:%d: DCHECK(%s)\n", fileName, line, expr);
    exit(1);
  }
}
#else
# define DCHECK(x)
#endif

#endif  // _COMMON_HPP
