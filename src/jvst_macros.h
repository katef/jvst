#ifndef JVST_MACROS_H
#define JVST_MACROS_H

#define NCOUNTERS 2

#define ARRAYLEN(x) (sizeof (x) / sizeof (x)[0])
#define STRINGIFY0(x) # x
#define STRINGIFY(x) STRINGIFY0(x)
#define SYMCAT0(x,y) x ## y
#define SYMCAT(x,y) SYMCAT0(x,y)
#define SYMCAT3(x,y,z) SYMCAT(SYMCAT(x,y),z)

#ifdef static_assert
#  define STATIC_ASSERT(x,name) static_assert((x),STRINGIFY(name))
#else
#  define STATIC_ASSERT(x,name) struct { char tmp[2*(x)-1]; } SYMCAT3(static_assert_, name, __LINE__)
#endif


#endif /* JVST_MACROS_H */

