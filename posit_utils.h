#ifndef UGHOAVGFHW_POSIT_UTILS_H_
#define UGHOAVGFHW_POSIT_UTILS_H_

#include "posit_config.h"

#include <limits.h>  // For CHAR_BIT.

namespace posit_internal {

static constexpr unsigned lzcnt(unsigned char x) noexcept {
  return __builtin_clz(x) -
      ((sizeof(unsigned) - sizeof(unsigned char))*CHAR_BIT);
}
static constexpr unsigned lzcnt(unsigned short x) noexcept {
  return __builtin_clz(x) -
      ((sizeof(unsigned) - sizeof(unsigned short))*CHAR_BIT);
}
static constexpr unsigned lzcnt(unsigned x) noexcept {
  return __builtin_clz(x); }
static constexpr unsigned lzcnt(unsigned long x) noexcept {
  return __builtin_clzl(x); }
static constexpr unsigned lzcnt(unsigned long long x) noexcept {
  return __builtin_clzll(x); }

static constexpr unsigned tzcnt(unsigned char x) noexcept {
  return __builtin_ctz(x); }
static constexpr unsigned tzcnt(unsigned short x) noexcept {
  return __builtin_ctz(x); }
static constexpr unsigned tzcnt(unsigned x) noexcept {
  return __builtin_ctz(x); }
static constexpr unsigned tzcnt(unsigned long x) noexcept {
  return __builtin_ctzl(x); }
static constexpr unsigned tzcnt(unsigned long long x) noexcept {
  return __builtin_ctzll(x); }

#if __has_builtin(__builtin_is_constant_evaluated)
# define CARRY_OP_BODY(type, op) \
    __builtin_assume(c_in <= 1); \
    /* Not if-constexpr as it creates a constant-evaluated context, */ \
    /* meaning the builtin will return true independent of whether or not */ \
    /* the function is in a constant-evaluated context. */ \
    if (__builtin_is_constant_evaluated()) { \
      CARRY_OP_NONCONST(type) \
    } else { \
      return __builtin_ ## op (a, b, c_in, c_out); \
    }
#else
# define CARRY_OP_BODY(type, op) \
    __builtin_assume(c_in <= 1); \
    CARRY_OP_NONCONST(type);
#endif

#define CARRY_OP_NONCONST(type) \
  type r = a + b + c_in; \
  *c_out = (r < a || (r == a && c_in)); \
  return r;
static constexpr unsigned char builtin_addc(
    unsigned char a, unsigned char b,
    unsigned char c_in, unsigned char* c_out) noexcept {
  CARRY_OP_NONCONST(unsigned char);
}
static constexpr unsigned short builtin_addc(
    unsigned short a, unsigned short b,
    unsigned short c_in, unsigned short* c_out) noexcept {
  CARRY_OP_NONCONST(unsigned short);
}
static constexpr unsigned builtin_addc(
    unsigned a, unsigned b, unsigned c_in, unsigned* c_out) noexcept {
  CARRY_OP_BODY(unsigned, addc);
}
static constexpr unsigned long builtin_addc(
    unsigned long a, unsigned long b,
    unsigned long c_in, unsigned long* c_out) noexcept {
  CARRY_OP_BODY(unsigned long, addcl);
}
static constexpr unsigned long long builtin_addc(
    unsigned long long a, unsigned long long b,
    unsigned long long c_in, unsigned long long* c_out) noexcept {
  CARRY_OP_BODY(unsigned long long, addcll);
}
#undef CARRY_OP_NONCONST

#define CARRY_OP_NONCONST(type) \
  type r = a - b - c_in; \
  *c_out = (r > a || (r == a && c_in)); \
  return r;
static constexpr unsigned char builtin_subc(
    unsigned char a, unsigned char b,
    unsigned char c_in, unsigned char* c_out) noexcept {
  CARRY_OP_NONCONST(unsigned char);
}
static constexpr unsigned short builtin_subc(
    unsigned short a, unsigned short b,
    unsigned short c_in, unsigned short* c_out) noexcept {
  CARRY_OP_NONCONST(unsigned short);
}
static constexpr unsigned builtin_subc(
    unsigned a, unsigned b, unsigned c_in, unsigned* c_out) noexcept {
  CARRY_OP_BODY(unsigned, subc);
}
static constexpr unsigned long builtin_subc(
    unsigned long a, unsigned long b,
    unsigned long c_in, unsigned long* c_out) noexcept {
  CARRY_OP_BODY(unsigned long, subcl);
}
static constexpr unsigned long long builtin_subc(
    unsigned long long a, unsigned long long b,
    unsigned long long c_in, unsigned long long* c_out) noexcept {
  CARRY_OP_BODY(unsigned long long, subcll);
}
#undef CARRY_OP_NONCONST

#undef CARRY_OP_BODY

#if POSIT_HAS_INT128
static constexpr unsigned lzcnt(unsigned __int128 x) noexcept {
  return (x >> 64) ? lzcnt(static_cast<uint64_t>(x >> 64))
                   : (64 + lzcnt(static_cast<uint64_t>(x)));
}
static constexpr unsigned tzcnt(unsigned __int128 x) noexcept {
  return static_cast<uint64_t>(x)
             ? tzcnt(static_cast<uint64_t>(x))
             : (64 + tzcnt(static_cast<uint64_t>(x >> 64)));
}
static constexpr unsigned __int128 builtin_addc(
    unsigned __int128 a, unsigned __int128 b,
    unsigned __int128 c_in, unsigned __int128* c_out) noexcept {
  __builtin_assume(c_in <= 1);
  unsigned __int128 r = a + b + c_in;
  *c_out = r < a || (r == a && c_in);
  return r;
}
static constexpr unsigned __int128 builtin_subc(
    unsigned __int128 a, unsigned __int128 b,
    unsigned __int128 c_in, unsigned __int128* c_out) noexcept {
  __builtin_assume(c_in <= 1);
  unsigned __int128 r = a - b - c_in;
  *c_out = r > a || (r == a && c_in);
  return r;
}
#endif

#if POSIT_HAS_EXTINT
template <int N>
static constexpr unsigned lzcnt(unsigned _ExtInt(N) x) noexcept {
# if POSIT_HAS_INT128
    if constexpr (N <= 128) {
      return lzcnt(static_cast<unsigned __int128>(x) - (128 - N));
    }
# else
    if constexpr (N <= 64) {
      return lzcnt(static_cast<uint64_t>(x) - (64 - N));
    }
# endif
  constexpr int n = N/2;
  return (x >> n) ? lzcnt(static_cast<unsigned _ExtInt(n)>(x >> n))
                  : (N - n + lzcnt(static_cast<unsigned _ExtInt(n)>(x)));
}
template <int N>
static constexpr unsigned tzcnt(unsigned _ExtInt(N) x) noexcept {
# if POSIT_HAS_INT128
    if constexpr (N <= 128) {
      return tzcnt(static_cast<unsigned __int128>(x));
    }
# else
    if constexpr (N <= 64) {
      return tzcnt(static_cast<uint64_t>(x));
    }
# endif
  constexpr int n = (N + 1)/2;
  return static_cast<unsigned _ExtInt(n)>(x)
             ? tzcnt(static_cast<unsigned _ExtInt(n)>(x))
             : (n + tzcnt(static_cast<unsigned _ExtInt(n)>(x >> n)));
}
template <int N>
static constexpr unsigned _ExtInt(N) builtin_addc(
    unsigned _ExtInt(N) a, unsigned _ExtInt(N) b,
    unsigned _ExtInt(N) c_in, unsigned _ExtInt(N)* c_out) noexcept {
  __builtin_assume(c_in <= 1);
  unsigned _ExtInt(N) r = a + b + c_in;
  *c_out = r < a || (r == a && c_in);
  return r;
}
static constexpr unsigned _ExtInt(N) builtin_subc(
    unsigned _ExtInt(N) a, unsigned _ExtInt(N) b,
    unsigned _ExtInt(N) c_in, unsigned _ExtInt(N)* c_out) noexcept {
  __builtin_assume(c_in <= 1);
  unsigned _ExtInt(N) r = a - b - c_in;
  *c_out = r > a || (r == a && c_in);
  return r;
}
#endif

template <bool> struct cond {
 private:
  // This implementation of `cond` is only used for false conditions. Having
  // the actual type referenced by `then` be named `enable_if` causes some
  // compilers to output nicer diagnostics for SFINAE failures, but it must
  // also have the actual predicate as the first template parameter. If
  // disabling through a multi-part `cond`, only the last condition will be
  // listed in the diagnostic.
  template <bool, typename>
  struct enable_if {
    template <bool b>
    using next = cond<b>;

    template <typename T>
    using otherwise = T;

    template <bool b, typename T>
    using enable_if_t = typename cond<b>::template sfinae<T>;
  };

 public:
  template <typename T>
  using sfinae = typename enable_if<false, T>::type;

  template <typename>
  using then = enable_if<false, void>;

  // Used by conjunct<>. This version (`cond<false>`) is used when PN is empty.
  // It simply returns the predicate, since it is the last item.
  template <typename Pred>
  using conjunct2 = Pred;
};
template <> struct cond<true> {
  template <typename T>
  using sfinae = T;

  template <typename T>
  struct then {
    using type = T;

    template <bool>
    struct next {
      template <typename>
      using then = cond<true>::then<T>;

      // Used by conjunct<>. This version (`cond<true>::then<T>`) is used when
      // the predicate `T` evaluates to false. The result is therefore `T`.
      template <typename...>
      using conjunct2 = T;
    };

    template <typename>
    using otherwise = T;

    template <bool, typename>
    using enable_if_t = T;

    template <typename...>
    using conjunct1 = T;
  };

  // Used by conjunct<>. This version (`cond<true>`) is used when PN is not
  // empty. It returns P1 if it is false and recurses otherwise.
  template <typename P1, typename... PN>
  using conjunct2 =
      typename cond<!P1::value>::template then<P1>
          ::template next<1 < sizeof...(PN)>::template conjunct2<PN...>;
};

// Alias templates for enabling must be named `enable_if_t` for the condition
// to be expanded. This name must be the top-level alias, or the condition will
// simply be `false`. When chaining multiple conditions but deferring
// instantiation of some, `cond<>::then<>` provides an `enable_if_t` alias
// which is equivalent to `next<>::then<>::type`, allowing the final condition
// to be printed.
template <bool b, typename T = void>
using enable_if_t = typename cond<b>::template sfinae<T>;

// Returns the value of the first predicate where `P::value` converted to a
// bool evaluates to false, or of the last predicate. Types after the first
// false predicate are not instantiated.
template <typename P1, typename... PN>
inline constexpr auto conjunct =
    cond<0 < sizeof...(PN)>::template conjunct2<P1, PN...>::value;

}  // namespace posit_internal

#endif  // UGHOAVGFHW_POSIT_UTILS_H_
