#ifndef UGHOAVGFHW_POSIT_CONFIG_H_
#define UGHOAVGFHW_POSIT_CONFIG_H_

/* CONFIGURATION OPTIONS
 *
 * The following macros may be pre-defined to control the posit library:
 * - POSIT_HAS_INT128: May be pre-defined to 0 or 1 to prevent or allow use of
 *   `__int128` and `unsigned __int128` types. Default: auto-detect
 * - POSIT_HAS_EXTINT: May be pre-defined to 0 or 1 to prevent or allow use of
 *   `_ExtInt(N)` and `unsigned _ExtInt(N)` types. Default: auto-detect
 * - POSIT_HEADER_ONLY: May be pre-defined to 1 to remove explicit template
 *   instantiations, allowing use as a header-only library. Default: unset
 * - POSIT_PRE_INCLUDE: May be pre-defined to an include path, which is
 *   #included in this file. This can be used to ensure consistent handling
 *   of non-macro customization, such as custom storage types. Default: unset
 * Setting any of these macros to an unlisted value is not supported; behavior
 * of other values may change in the future.
 *
 * By default, posits up to 64 bits are supported. If `__int128` is available
 * (as per POSIT_HAS_INT128), then up to 128 bits are supported. If `_ExtInt`
 * is available (as per POSIT_HAS_EXTINT), then arbitrary sizes are supported
 * as allowed by the compiler. Additionally, custom storage types may be
 * configured via specialization of `struct PositStorage`.
 *
 * Posits can convert to or from some types implicitly, including custom types
 * with numeric_limits specializations. For non-integer types, this requires
 * `frexp`, `trunc`, and `exp2` library functions, which may be found via
 * argument-dependent lookup. If a more efficient or accurate conversion is
 * available, type traits can be specialized to modify these conversions,
 * either by making them explicit (such that external implicit conversions are
 * preferred), or removing them via SFINAE.
 * - posit<N, E>::IntAlwaysFits<T> affects conversion from integer types. If
 *   it has `value = false`, the conversion is explicit.
 * - Conversion to integer types is always explicit.
 * - posit<N, E>::FloatAlwaysFits<T> affects conversion from non-integer types.
 *   If it has `value = false`, the conversion is explicit. If it does not have
 *   a `value` member, the conversion does not exist.
 * - posit<N, E>::FitsIntoFloat<T> affects conversion to non-integer types. If
 *   it has `value = false`, the conversion is explicit. If it does not have a
 *   `value` member, the conversion does not exist.
 */

#ifndef __has_feature
# define __has_feature(x) (x > 0)
#endif
#ifndef __has_extension
# define __has_extension(x) __has_feature(x)
#endif

#ifdef POSIT_PRE_INCLUDE
# include POSIT_PRE_INCLUDE
#endif

#if !defined(POSIT_HAS_INT128) || !defined(POSIT_HAS_EXTINT)
# ifdef __is_identifier
#   define POSIT_HAS_INT128 (!__is_identifier(__int128))
#   define POSIT_HAS_EXTINT (!__is_identifier(_ExtInt))
# elif defined(__SIZEOF_INT128__) && \
       (defined(__x86_64__) || defined(__aarch64__) || defined(__powerpc64__))
#   define POSIT_HAS_INT128 1
#   define POSIT_HAS_EXTINT 0
# else
#   define POSIT_HAS_INT128 0
#   define POSIT_HAS_EXTINT 0
# endif
#endif

#if !__has_builtin(__builtin_clz) || !__has_builtin(__builtin_ctz) || \
	!__has_builtin(__builtin_assume) || !__has_builtin(__builtin_expect) || \
	!__has_builtin(__builtin_addc) || !__has_builtin(__builtin_subc)
# error Compiler does not have required features.
#endif

#endif  // UGHOAVGFHW_POSIT_CONFIG_H_
