#ifndef UGHOAVGFHW_POSIT_MATH_H_
#define UGHOAVGFHW_POSIT_MATH_H_

#include <math.h>
#include "posit.h"

template <int N, int E> constexpr posit<N, E> abs(posit<N, E> x) noexcept {
  return x < 0 ? -x : x; }
template <int N, int E> constexpr posit<N, E> fabs(posit<N, E> x) noexcept {
  return abs(x); }
template <int N, int E> constexpr posit<N, E> fmod(posit<N, E> n,
                                                   posit<N, E> d) noexcept;
template <int N, int E> constexpr posit<N, E> remainder(posit<N, E> n,
                                                        posit<N, E> d) noexcept;
template <int N, int E> constexpr posit<N, E> remquo(
    posit<N, E> n, posit<N, E> d, int* quo) noexcept;
template <int N, int E> constexpr posit<N, E> fma(
    posit<N, E> x, posit<N, E> y, posit<N, E> z) noexcept {
  return fused_add(x * y, z); }
template <int N, int E> constexpr posit<N, E> fmax(
    posit<N, E> a, posit<N, E> b) noexcept { return a >= b ? a : b; }
template <int N, int E> constexpr posit<N, E> fmin(
    posit<N, E> a, posit<N, E> b) noexcept {
  return (a < b && a != posit<N, E>::NaR()) ? a : b; }
template <int N, int E> constexpr posit<N, E> fdim(posit<N, E> a,
                                                   posit<N, E> b) noexcept;
template <int N, int E> constexpr posit<N, E> lerp(
    posit<N, E> a, posit<N, E> b, posit<N, E> t) noexcept;
template <int N, int E> constexpr posit<N, E> exp(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> expm1(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> exp2(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> log(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> log1p(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> log2(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> log10(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> pow(posit<N, E>,
                                                  posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> sqrt(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> cbrt(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> hypot(posit<N, E> x,
                                                    posit<N, E> y) noexcept;
template <int N, int E> constexpr posit<N, E> hypot(
    posit<N, E> x, posit<N, E> y, posit<N, E> z) noexcept;
template <int N, int E> constexpr posit<N, E> sin(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> cos(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> tan(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> asin(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> acos(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> atan(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> atan2(posit<N, E> y,
                                                    posit<N, E> x) noexcept;
template <int N, int E> constexpr posit<N, E> sinh(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> cosh(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> tanh(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> asinh(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> acosh(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> atanh(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> ceil(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> floor(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> trunc(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> round(posit<N, E>) noexcept;
template <int N, int E> constexpr typename PositTraits<N, E>::Signed iround(
    posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> nearbyint(posit<N, E> x)
    noexcept { return round(x); }
template <int N, int E> constexpr posit<N, E> rint(posit<N, E> x) noexcept {
  return round(x); }
template <int N, int E> constexpr typename PositTraits<N, E>::Signed irint(
    posit<N, E> x) noexcept { return iround(x); }
// Non-standard. Returns INT_MIN or INT_MAX on range errors.
template <int N, int E> constexpr posit<N, E> modf(posit<N, E>, int*) noexcept;
template <int N, int E> constexpr posit<N, E> modf(posit<N, E>,
                                                   posit<N, E>*) noexcept;
template <int N, int E> constexpr posit<N, E> frexp(posit<N, E>, int* exponent)
    noexcept;
template <int N, int E> constexpr posit<N, E> ldexp(posit<N, E>, int exponent)
    noexcept;
template <int N, int E> constexpr int ilogb(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> logb(posit<N, E>) noexcept;
template <int N, int E> constexpr posit<N, E> scalbn(posit<N, E>, int exponent)
    noexcept;
// nextafter and nexttoward are implemented by the core posit library.
template <int N, int E> constexpr posit<N, E> copysign(
    posit<N, E> mag, posit<N, E> sign) noexcept;
template <int N, int E> constexpr bool signbit(posit<N, E>) noexcept;
template <int N, int E> constexpr int fpclassify(posit<N, E>) noexcept;
template <int N, int E> constexpr bool isfinite(posit<N, E> x) noexcept {
  return x != posit<N, E>::NaR(); }
template <int N, int E> constexpr bool isinf(posit<N, E>) noexcept {
  return false; }
template <int N, int E> constexpr bool isnan(posit<N, E> x) noexcept {
  return x == posit<N, E>::NaR(); }
template <int N, int E> constexpr bool isnormal(posit<N, E> x) noexcept {
  return x != posit<N, E>::Zero() && x != posit<N, E>::NaR(); }
template <int N, int E> constexpr bool isgreater(
    posit<N, E> a, posit<N, E> b) noexcept { return a > b; }
template <int N, int E> constexpr bool isgreaterequal(
    posit<N, E> a, posit<N, E> b) noexcept { return a >= b; }
template <int N, int E> constexpr bool isless(
    posit<N, E> a, posit<N, E> b) noexcept { return a < b; }
template <int N, int E> constexpr bool islessequal(
    posit<N, E> a, posit<N, E> b) noexcept { return a <= b; }
template <int N, int E> constexpr bool islessgreater(
    posit<N, E> a, posit<N, E> b) noexcept { return a != b; }
template <int N, int E> constexpr bool isunordered(  // All posits are ordered.
    posit<N, E> a, posit<N, E> b) noexcept { return false; }

template <typename T> constexpr T e_pos;
template <typename T> constexpr T log2e_pos;
template <typename T> constexpr T log10e_pos;
template <typename T> constexpr T pi_pos;
template <typename T> constexpr T inv_pi_pos;
template <typename T> constexpr T inv_sqrtpi_pos;
template <typename T> constexpr T ln2_pos;
template <typename T> constexpr T ln10_pos;
template <typename T> constexpr T sqrt2_pos;
template <typename T> constexpr T sqrt3_pos;
template <typename T> constexpr T inv_sqrt3_pos;
template <typename T> constexpr T egamma_pos;
template <typename T> constexpr T phi_pos;

// Used by some math functions to directly adjust the exponent in a
// mult-intermediate, without losing any bits of precision. Most useful when
// the result is added to a quire.
template <int N, int E>
constexpr posit_mult_intermediate<N, E> adjust_mult_exponent(
    posit_mult_intermediate<N, E> p, int adjust) noexcept {
  p.exponent_ += adjust;
  return static_cast<posit_mult_intermediate<N, E>&&>(p);
}

template <int N, int E>
constexpr posit<N, E> fmod(posit<N, E> n, posit<N, E> d) noexcept {
  posit<N, E> r = fused_add(n, trunc(n / d) * -d);
  if (__builtin_expect((n > 0) != (r > 0), 0)) {
    // This occurs when the division result rounds up to an integer.
    return r + copysign(d, n);
  }
  return r;
}

template <int N, int E>
constexpr posit<N, E> remainder(posit<N, E> n, posit<N, E> d) noexcept {
  return fused_add(n, round(n / d) * -d);
}

template <int N, int E>
constexpr posit<N, E> remquo(posit<N, E> n, posit<N, E> d, int* quo) noexcept {
  posit<N, E> quotient = round(n / d);
  posit<N, E> remainder = fused_add(n, quotient * -d);
  if (quotient >= 0) {
    *quo = static_cast<unsigned>(quotient) % 0x80;
  } else {
    *quo = -(static_cast<unsigned>(-quotient) % 0x80);
  }
  return remainder;
}

template <int N, int E>
constexpr posit<N, E> fdim(posit<N, E> a, posit<N, E> b) noexcept {
  if (a == posit<N, E>::NaR() || b == posit<N, E>::NaR()) {
    return posit<N, E>::NaR();
  }
  if (a <= b) return posit<N, E>::Zero();
  return a - b;
}

template <int N, int E>
constexpr posit<N, E> lerp(posit<N, E> a, posit<N, E> b, posit<N, E> t)
    noexcept {
  if (t == posit<N, E>::Zero()) return a;
  if (t == posit<N, E>::One()) return b;
  return fused_add(a, t * (b - a));
}

// Computes `(e^(x * 2^-EA))^(2^SC)`. It is required that `|x| in (0.5, 1.0]`
// and `EA > 0`. This is the same as calculating `e^y` where
// `y = x * 2^(SC-EA)`; this form provides less rounding and faster
// convergence, as each term in the taylor series has a factor of `2^(-EA*k)`.
//
// After k terms, the error is bounded by `(e^t * t^(k+1)) / (k+1)!`. Since
// `t` is `x*2^-EA, |x| <= 1, EA > 0`, `e^t` is at most the square root of e,
// ~1.65, between 2^0 and 2^1.
// `t^(k+1)` is `x^(k+1)*2^(-EA * (k+1)) <= 2^(-EA * (k+1))`, and
// `1/(k+1)!` shrinks super-exponentially. The exponent of the latter is
// approximated using a piecewise linear function, which is always an
// underestimate but is fairly close for over 150 iterations:
//     [see half_bits_after]
// Additionally, each squaring increases the error:
// `(x + err)^2 = x^2 + (2*x*err + err^2)`. For the first EA squares,
// `x` is a root of E and so must be between 1 and 2, so the error after each
// squaring is approximated as 4 times the error before, meaning an
// additional two bits are needed for each such squaring. If `SC > EA`, each
// further squaring requires 1 + 1.5*i bits, where i is 1, 2, ....
//
// The total number of bits of accuracy needed is:
//     MFB + 0.5 + 1 /* 1 < e^t < 2 */ + 2*min(EA, SC) + 0.5*max(SC-EA, 0)
// The total number of bits available after k rounds is:
//     k*EA + m(k)*k + b(k), where m and b form the piecewise function.
class exp_impl {
 private:
  template <int N, int E>
  friend constexpr posit<N, E> exp(posit<N, E>) noexcept;
  template <int N, int E>
  friend constexpr posit<N, E> expm1(posit<N, E>) noexcept;

  static constexpr int half_bits_after(int k) noexcept {
    if (k <= 1) return 0;
    if (k <= 8) return 5 * k - 7;
    if (k <= 21) return 8 * k - 32;
    if (k <= 44) return 10 * k - 75;
    if (k <= 90) return 12 * k - 165;
    return 14 * k - 346;
  }

  // Sums terms of the Taylor's series into a quire. For normal `exp`, quire
  // should contain the value 1.0, extra_bits should be the number of bits
  // needed due to squaring, and exponent_adjust must be positive.
  // For `expm1`, quire should contain the value 0.0, extra_bits is the
  // expected exponent of the result, and exponent_adjust must be the original
  // exponent of x.
  template <int N, int E>
  static constexpr void taylor(
      const posit<N, E> x, const int exponent_adjust,
      const int extra_bits, typename posit<N, E>::quire_type& quire) noexcept {
    using Traits = PositTraits<N, E>;
    // We start with the approximation `k = MFB / (EA + 5) + EA`.
    const int kHalfBitsNeeded =
        Traits::MaxFractionBits * 2 + 3 + extra_bits * 2;
    int k = Traits::MaxFractionBits / (exponent_adjust + 5) + exponent_adjust;
    if (half_bits_after(k) + 2 * k * exponent_adjust >= kHalfBitsNeeded) {
      while (half_bits_after(k - 1) + 2 * (k - 1) * exponent_adjust >=
             kHalfBitsNeeded) {
        --k;
      }
    } else {
      do {
        ++k;
      } while (half_bits_after(k) + 2 * k * exponent_adjust < kHalfBitsNeeded);
    }
    posit<N, E> factor = posit<N, E>::One();
    for (int i = 1; i <= k; ++i) {
      auto mult = factor * (x / posit<N, E>(i));
      factor = mult;
      quire += adjust_mult_exponent(
          static_cast<posit_mult_intermediate<N, E>&&>(mult),
          -i * exponent_adjust);
    }
  }

  template <int N, int E>
  static constexpr posit<N, E> exp(
      const posit<N, E> x, const int exponent_adjust,
      const int square_count) noexcept {
    typename posit<N, E>::quire_type quire = posit<N, E>::One();
    const int extra_squares = square_count - exponent_adjust;
    const int extra_bits =
        square_count > exponent_adjust
            ? 4 * exponent_adjust + 2 * extra_squares +
              3 * extra_squares * (extra_squares + 1) / 2
            : 4 * square_count;
    taylor<N, E>(x, exponent_adjust, extra_bits, quire);
    for (int i = 0; i < square_count; ++i) {
      // TODO: Avoid a quire for squaring. The two mult_intermediates can be
      // added using the same code as for fused_add, but extracting a pair of
      // posits.
      posit<N, E> x_high = quire.to_posit();
      quire -= x_high;
      posit<N, E> x_low = quire.to_posit();
      quire.clear();
      quire += adjust_mult_exponent(x_low * x_high, 1);
      quire += x_high * x_high;
      // Leaving off x_low^2, as it affects error less than only using two
      // posits worth of accuracy does.
    }
    return quire.to_posit();
  }

  template <int N, int E>
  static constexpr posit<N, E> expm1_large(
      const posit<N, E> x, const int original_exponent) noexcept {
    typename posit<N, E>::quire_type quire{};
    // One extra bit, as leaving off the 1.0 term can affect the exponent.
    // Two extra bits for the first squaring.
    // 1+1.5*i extra bits for each squaring up to the final exponent.
    const int extra_bits =
        2 + 4 + 2 * original_exponent +
        3 * original_exponent * (original_exponent + 1) / 2;
    taylor<N, E>(x, 1, extra_bits, quire);
    for (int i = 0; i < original_exponent + 1; ++i) {
      posit<N, E> x_high = quire.to_posit();
      quire -= x_high;
      posit<N, E> x_low = quire.to_posit();
      quire.clear();
      quire += adjust_mult_exponent(x_low * x_high, 1);
      quire += x_high * x_high;
      // Leaving off x_low^2, as it affects error less than only using two
      // posits worth of accuracy does.

      // (x - 1)^2 = x^2 - 2x + 1 = (x^2 - 1) - 2(x - 1) = (x' - 1) - 2(x - 1)
      // Add back two of the original value. This multiplies by 1 then adjusts
      // the exponent because 2 is not representable for some posit types.
      quire += adjust_mult_exponent(posit<N, E>::One() * x_high, 1);
      quire += adjust_mult_exponent(posit<N, E>::One() * x_low, 1);
    }
    return quire.to_posit();
  }
};

template <int N, int E>
constexpr posit<N, E> exp(posit<N, E> x) noexcept {
  if (x == posit<N, E>::Zero()) return posit<N, E>::One();
  if (x == posit<N, E>::NaR()) return x;
  using Traits = PositTraits<N, E>;
  int exponent = 0;
  if constexpr (Traits::MaxFractionBits > 0) {
    x = frexp(x, &exponent);
    constexpr auto kHalf = posit<N, E>(2).imprecise_inverse();
    if (x == kHalf) {
      x = posit<N, E>::One();
      --exponent;
    }
  } else {
    // All posits of this type are a power of two, and frexp may not exist
    // since the correct result, ±0.5, might not be representable.
    exponent = ilogb(x);
    x = posit<N, E>::One();
  }
  // Required: EA > 0, SC >= 0, SC - EA = exponent.
  // When possible, aim for EA,SC <= G = ceil(lg(MFB)), which provides a
  // good tradeoff between the number of Taylor series iterations and
  // number of squaring iterations.
  constexpr int G =
      Traits::MaxFractionBits > 0
          ? 31 - lzcnt(uint32_t{Traits::MaxFractionBits})
          : 0;
  int EA = 0, SC = 0;
  if (exponent > G) {
    // EA must be positive, so a large number of squares is necessary.
    EA = 1;
    SC = exponent + 1;
  } else if (exponent >= 0) {
    // Push SC up to G, and maximize EA under that.
    EA = G - exponent;
    SC = G;
  } else if (exponent >= -G) {
    // Push EA up to G, and square as needed.
    EA = G;
    SC = G + exponent;
  } else {
    // A higher EA would cause the posit precision to roll off more quickly,
    // so stick with -exponent.
    EA = -exponent;
    SC = 0;
  }
  return exp_impl::exp<N, E>(x, EA, SC);
}

template <int N, int E>
constexpr posit<N, E> expm1(posit<N, E> x) noexcept {
  if (x == posit<N, E>::Zero() || x == posit<N, E>::NaR()) return x;
  using Traits = PositTraits<N, E>;
  int exponent = 0;
  if constexpr (Traits::MaxFractionBits > 0) {
    x = frexp(x, &exponent);
    constexpr auto kHalf = posit<N, E>(2).imprecise_inverse();
    if (x == kHalf) {
      x = posit<N, E>::One();
      --exponent;
    }
  } else {
    // All posits of this type are a power of two, and frexp may not exist
    // since the correct result, ±0.5, might not be representable.
    exponent = ilogb(x);
    x = posit<N, E>::One();
  }
  if (exponent >= 0) return exp_impl::expm1_large<N, E>(x, exponent);
  typename posit<N, E>::quire_type q{};
  // It is always true that `e^x - 1 > x`, though for small `|x|` they will be
  // close. Therefore, requiring the number of extra bits to match the exponent
  // should be enough, though excessive for numbers closer to 1.
  exp_impl::taylor<N, E>(x, -exponent, -exponent, q);
  return q.to_posit();
}

template <int N, int E>
constexpr posit<N, E> exp2(posit<N, E> x) noexcept {
  if (x == posit<N, E>::Zero()) return posit<N, E>::One();
  if (x == posit<N, E>::NaR()) return x;
  // 2^x = 2^(i.f) = 2^(i + 0.f) = 2^i * 2^(0.f).
  // If x > 0, 2^(0.f) is in the range (1.0, 2.0), with an exponent of 0.
  // If x < 0, 2^(0.f) is in the range (0.5, 1.0), with an exponent of -1.
  // In either case, simply calculate 2^(0.f) and then adjust the exponent.
  int exponent = 0;
  x = modf(x, &exponent);  // Non-standard overload provides an `int` exponent.
  // 2^f = e^(ln(2^f)) = e^(f * ln(2))
  x = exp(posit<N, E>(x * ln2_pos<posit<N, E>>));
  return ldexp(x, exponent);
}

template <int N, int E>
constexpr posit<N, E> log1p_impl(
    posit<N, E> x, posit<N, E> additional = posit<N, E>::Zero()) noexcept {
  // sum n=1->inf -(-1)^n * x^n/n = sum x^(2n)/(2n) - x^(2n+1)/(2n+1)
  using Traits = PositTraits<N, E>;
  // additional is added separately for the first term. If adding it to x
  // causes it to be rounded off for future terms, it is assumed that it would
  // not affect the result anyway.
  typename posit<N, E>::quire_type quire = x;
  quire += additional;
  x += additional;
  if (x == posit<N, E>::Zero()) return x;
  auto mult = x * x;
  const posit<N, E> square = mult;
  quire -= adjust_mult_exponent(
      static_cast<posit_mult_intermediate<N, E>&&>(mult), -1);
  quire += x * (square / posit<N, E>(3));
  posit<N, E> first = square, second = square * x;
  __builtin_assume(first >= posit<N, E>::Min());
  const int bits_per_two_iters = -ilogb(square) - 1;
  if (bits_per_two_iters > 0) {
    const int iters = Traits::MaxFractionBits / bits_per_two_iters * 2 + 2;
    for (int i = 4; i < iters; i += 2) {
      quire -= (first / posit<N, E>(i)) * square;
      quire += (second / posit<N, E>(i + 1)) * square;
      first *= square;
      second *= square;
    }
  } else {
    using U = typename Traits::Unsigned;
    // x could be 1, which means terms are only dropping for 1/i. The worst
    // case is x=1, where the result is ln(2)=0.69... with an exponent of -1.
    // Therefore we need 1/i <= 2^-(MFB+1) for stored bits, and two extra bits
    // for rounding.
    constexpr U iters = U{1} << (Traits::MaxFractionBits + 3);
    for (U i = 4; i < iters; i += 2) {
      quire -= (first / posit<N, E>(i)) * square;
      quire += (second / posit<N, E>(i + 1)) * square;
      first *= square;
      second *= square;
    }
  }
  return quire.to_posit();
}

template <int N, int E>
constexpr posit<N, E> log(posit<N, E> x) noexcept {
  // Also handles NaR.
  if (x <= posit<N, E>::Zero()) return posit<N, E>::NaR();
  // ln(x*2^p) = ln(x) + p*ln(2) = log1p(x - 1) + p*ln(2)
  // log1p(x - 1) wants x in (0, 2], but can lose precision if x < 1. Aim
  // for x in [1, 2).
  using Traits = PositTraits<N, E>;
  int exponent = 0;
  if constexpr (Traits::MaxFractionBits > 0) {
    // TODO: Get a function which actually returns the range [1, 2).
    x = ldexp(frexp(x, &exponent), 1);
    --exponent;
  } else {
    // All posits of this type are a power of two, and frexp may not exist
    // since the correct result, 0.5, might not be representable.
    exponent = ilogb(x);
    x = posit<N, E>::One();
  }
  // x is in range [1, 2), so x - 1 subtracts off the hidden bit. In the worst
  // case, with ExpBits=0, one bit of precision is lost for every leading zero
  // in the fraction part but the first, but the fraction is also shifted more
  // than that so none of the lost bits can be set. Thus, the only rounding
  // here is within log1p_impl and after the final add.
  return fused_add(log1p_impl<N, E>(x - posit<N, E>::One()),
                   posit<N, E>(exponent) * ln2_pos<posit<N, E>>);
}

template <int N, int E>
constexpr posit<N, E> log1p(posit<N, E> x) noexcept {
  // Also handles NaR.
  if (x <= -posit<N, E>::One()) return posit<N, E>::NaR();
  if (x < posit<N, E>::One()) return log1p_impl<N, E>(x);
  // ln(1 + x*2^p) = ln((2^-p + x)*2^p) = ln(2^-p + x) + p*ln(2)
  // = log1p(1 + (2^-p + x - 1)) + p*ln(2)
  using Traits = PositTraits<N, E>;
  int exponent = 0;
  if constexpr (Traits::MaxFractionBits > 0) {
    x = frexp(x, &exponent);
  } else {
    // All posits of this type are a power of two, and frexp may not exist
    // since the correct result, 0.5, might not be representable.
    exponent = ilogb(x);
    x = posit<N, E>::One();
  }
  return fused_add(log1p_impl<N, E>(
                       x - posit<N, E>::One(),
                       ldexp(posit<N, E>::One(), -exponent)),
                   posit<N, E>(exponent) * ln2_pos<posit<N, E>>);
}

template <int N, int E>
constexpr posit<N, E> log10(posit<N, E> x) noexcept {
  // Also handles NaR.
  if (x <= posit<N, E>::Zero()) return posit<N, E>::NaR();
  // TODO: Does this need extra precision?
  return log(x) * log10e_pos<posit<N, E>>;
}

template <int N, int E>
constexpr posit<N, E> log2(posit<N, E> x) noexcept {
  // Also handles NaR.
  if (x <= posit<N, E>::Zero()) return posit<N, E>::NaR();
  // lg(x*2^p) = lg(x) + p
  using Traits = PositTraits<N, E>;
  int exponent = 0;
  if constexpr (Traits::MaxFractionBits > 0) {
    // TODO: Get a function which actually returns the range [1, 2).
    x = ldexp(frexp(x, &exponent), 1);
    --exponent;
  } else {
    // All posits of this type are a power of two, and frexp may not exist
    // since the correct result, 0.5, might not be representable.
    return ilogb(x);
  }
  // Inlined the definition of log(x) for x in [1, 2).
  // TODO: Does this need extra precision for the division?
  return log1p_impl<N, E>(x - posit<N, E>::One()) * log2e_pos<posit<N, E>>
             + posit<N, E>(exponent);
}

template <int N, int E>
constexpr posit<N, E> pow(posit<N, E> x, posit<N, E> y) noexcept {
  // IEEE-defined special cases.
  if (x == posit<N, E>::One()) return x;  // Even for 1^NaR.
  if (y == posit<N, E>::Zero()) return posit<N, E>::One();  // Even for NaR^0.
  if (x == posit<N, E>::NaR() || y == posit<N, E>::NaR() ||
      (x == posit<N, E>::Zero() && y < posit<N, E>::Zero())) {
    return posit<N, E>::NaR();
  }
  if (x == posit<N, E>::Zero() || y == posit<N, E>::One()) return x;
  // x^y = e^(y*ln(x)) = e^(y*ln(a*2^b)) = e^(y*(ln(a) + b*ln(2)))
  // = e^(y*ln(a)) * e^(y*b*ln(2))
  using Traits = PositTraits<N, E>;
  int b = 0;
  if constexpr (Traits::MaxFractionBits > 0) {
    // TODO: Get a function which actually returns the range [1, 2).
    x = ldexp(frexp(x, &b), 1);
    --b;
  } else {
    // All posits of this type are a power of two, and frexp may not exist
    // since the correct result, 0.5, might not be representable.
    // This makes things simpler though: (2^b)^y = 2^(b * y)

    // Exact for powers of two.
    if (y == -posit<N, E>::One()) return x.imprecise_inverse();
    b = ilogb(x);  // Cannot be zero, as x is not 1.
    if (x < posit<N, E>::Zero() && y < posit<N, E>::One() &&
        y > -posit<N, E>::One()) {
      return posit<N, E>::NaR();
    }
    auto ival = iround(posit<N, E>(b) * y);
    // Both y == 1 and y == -1 have been checked, so either x is positive or
    // y is an even integer. The result is always even.
    if (ival > INT_MAX) return posit<N, E>::Max();
    if (ival < INT_MIN) return posit<N, E>::Min();
    return ldexp(posit<N, E>::One(), static_cast<int>(ival));
  }
  int result_sign = 1;
  if (x < posit<N, E>::Zero()) {
    auto ival = iround(y);
    if (posit<N, E>(ival) != y) return posit<N, E>::NaR();
    if (ival & 1) result_sign = -1;
    x = -x;
  }
  // e^(y*log1p(a - 1)) * e^(y*b*ln(2))
  posit<N, E> ln_a = log1p_impl<N, E>(x - posit<N, E>::One());
  posit<N, E> ln_2_b = posit<N, E>(b) * ln2_pos<posit<N, E>>;
  posit<N, E> r =  exp(posit<N, E>(y * ln_a)) * exp(posit<N, E>(y * ln_2_b));
  return result_sign >= 0 ? r : -r;
}

template <int N, int E>
constexpr posit<N, E> sqrt(posit<N, E> x) noexcept {
  if (!isnormal(x)) return x;
  if (x < posit<N, E>::Zero()) return posit<N, E>::NaR();
  using Traits = PositTraits<N, E>;
  if constexpr (Traits::MaxFractionBits <= 0) {
    // x is a power of 2. Additionally, the value 2 might not be representable.
    // sqrt(2^b) = 2^(b / 2).
    int orig = ilogb(x);
    int half = orig / 2;
    // Round to even. This works even if the exponent isn't fully stored, as
    // then `orig & 1` would be 0.
    if ((orig & 1) && (half & 1)) {
      if (orig >= 0) ++half; else --half;
    }
    return frexp(posit<N, E>::One(), half);
  }
  // x^0.5 = (a*2^b)^0.5 = a^0.5 * 2^(b/2) = e^(ln(a)/2) * 2^(b/2)
  // TODO: Get a function which actually returns the range [1, 2).
  int b = 0;
  posit<N, E> a = ldexp(frexp(x, &b), 1);
  --b;
  posit<N, E> half_ln_a =
      log1p_impl<N, E>(a - posit<N, E>::One()) *
      posit<N, E>(2).imprecise_inverse();
  posit<N, E> sqrt_2_b =
      ldexp((b & 1) ? sqrt2_pos<posit<N, E>> : posit<N, E>::One(), b >> 1);
  return exp(half_ln_a) * sqrt_2_b;
}

template <int N, int E>
constexpr posit<N, E> cbrt(posit<N, E> x) noexcept {
  if (!isnormal(x)) return x;
  using Traits = PositTraits<N, E>;
  if constexpr (Traits::MaxFractionBits <= 0) {
    // x is a power of 2. Additionally, the value 2 might not be representable.
    // cbrt(s*2^b) = s*2^(b / 3).
    int orig = ilogb(x);
    int third = orig / 3;
    int mod = orig % 3;
    if (mod == 2) ++third;
    if (mod == -2) --third;
    return copysign(frexp(posit<N, E>::One(), third), x);
  }
  // x^(1/3) = (a*2^b)^(1/3) = a^(1/3) * 2^(b/3) = e^(ln(a)/3) * 2^(b/3)
  // TODO: Get a function which actually returns the range [1, 2).
  int b = 0;
  posit<N, E> a = ldexp(frexp(x, &b), 1);
  --b;
  posit<N, E> ln_a = log1p_impl<N, E>(a - posit<N, E>::One());
  int third = b / 3;
  int mod = b % 3;
  if (mod < 0) { ++third; mod += 3; }
  constexpr posit<N, E> cbrt_2 = exp(ln2_pos<posit<N, E>> / posit<N, E>(3));
  constexpr posit<N, E> cbrt_4 = exp(log(posit<N, E>(4)) / posit<N, E>(3));
  posit<N, E> cbrt_2_b =
      ldexp(mod == 0 ? posit<N, E>::One() : mod == 1 ? cbrt_2 : cbrt_4, third);
  return exp(ln_a / posit<N, E>(3)) * copysign(cbrt_2_b, x);
}

template <int N, int E>
constexpr posit<N, E> hypot(posit<N, E> x, posit<N, E> y) noexcept {
  if (x == posit<N, E>::Zero()) return fabs(y);
  if (y == posit<N, E>::Zero()) return fabs(x);
  if (x == posit<N, E>::NaR() || y == posit<N, E>::NaR()) {
    return posit<N, E>::NaR();
  }
  // Whichever is larger gets the exponent 0, to maximize available bits in
  // the fused_add result. If they are the same, give them the exponent -1 so
  // their sum likely has exponent 0.
  // TODO: Get a function which actually returns the range [1, 2).
  int x_exp = ilogb(x);
  int y_exp = ilogb(y);
  if (x_exp < y_exp) {
    x_exp = y_exp;
  } else if (x_exp == y_exp) {
    ++x_exp;
  }
  x = ldexp(x, -x_exp);
  y = ldexp(y, -x_exp);
  return ldexp(sqrt(fused_add(x * x, y * y)), x_exp);
}

template <int N, int E>
constexpr posit<N, E> hypot(
    posit<N, E> x, posit<N, E> y, posit<N, E> z) noexcept {
  if (x == posit<N, E>::Zero()) return hypot(y, z);
  if (y == posit<N, E>::Zero()) return hypot(x, z);
  if (z == posit<N, E>::Zero()) return hypot(x, y);
  if (x == posit<N, E>::NaR() || y == posit<N, E>::NaR() ||
      z == posit<N, E>::NaR()) {
    return posit<N, E>::NaR();
  }
  // Whichever is largest gets the exponent 0, to maximize available bits in
  // the quire sum. If at least two have the same exponent, give them the
  // exponent -1 so their sum likely has exponent 0.
  // TODO: Get a function which actually returns the range [1, 2).
  int x_exp = ilogb(x);
  int y_exp = ilogb(y);
  int z_exp = ilogb(z);
  if (x_exp > y_exp && x_exp < z_exp) {
    x_exp = z_exp;
  } else if (x_exp < y_exp && y_exp > z_exp) {
    x_exp = y_exp;
  } else if (x_exp <= y_exp || x_exp <= z_exp) {
    ++x_exp;
  }
  x = ldexp(x, -x_exp);
  y = ldexp(y, -x_exp);
  z = ldexp(z, -x_exp);
  return ldexp(sqrt(posit<N, E>::quire_type::add_all(x * x, y * y, z * z)
                         .to_posit()),
               x_exp);
}

//posit modf(posit, int*);  // Non-standard.

// Can't just call modf(posit, int*) because the result might not fit.
template <int N, int E>
constexpr posit<N, E> modf(posit<N, E> x, posit<N, E>* e) noexcept;

template <int N, int E>
constexpr posit<N, E> frexp(posit<N, E> x, int* exponent) noexcept {
  if (x == posit<N, E>::Zero()) { *exponent = 0; return x; }
  if (x == posit<N, E>::NaR()) { *exponent = FP_ILOGBNAN; return x; }
  using Traits = PositTraits<N, E>;
  static_assert(Traits::UncappedMaxFractionBits >= 0,
                "frexp is not implemented for this type as there are no "
                "representable values in the result range [0.5, 1).");
  using U = typename Traits::Unsigned;
  constexpr posit<N, E> kHalf = posit<N, E>(2).imprecise_inverse();
  bool neg = x < posit<N, E>::Zero();
  U bits =
      (x.bits_ >= 0 ? static_cast<U>(x.bits_) : static_cast<U>(-x.bits_))
      & Traits::kMask;
  if (bits == Traits::kMax) {
    *exponent = Traits::MaxExp + 1;
    return neg ? -kHalf : kHalf;
  }
  int lz = 0, regime = 0;
  if (bits & (Traits::kHighBit >> 1)) {
    lz = lzcnt(U(~(bits << 1)));
    regime = lz - 1;
  } else {
    lz = lzcnt(bits << 1);
    regime = -lz;
  }
  if (lz >= Traits::NBits - 2) {
    *exponent = regime * (1 << Traits::ExpBits) + 1;
    return neg ? -kHalf : kHalf;
  }
  int exp = regime * (1 << Traits::ExpBits);
  int shift = Traits::SBits - Traits::ExpBits - lz - 2;
  U kExpMask = (U{1} << Traits::ExpBits) - 1;
  if (shift >= 0) {
    exp += static_cast<int>((bits >> shift) & kExpMask);
    bits = bits & ((U{1} << shift) - 1);
    bits <<= Traits::SBits - Traits::ExpBits - 3 - shift;
  } else {
    exp += static_cast<int>((bits << -shift) & kExpMask);
    bits = 0;
  }
  *exponent = exp + 1;
  // Set the output exponent to -1.
  bits |= kExpMask << (Traits::SBits - Traits::ExpBits - 3);
  bits |= U{1} << (Traits::SBits - 3);
  x = posit<N, E>::WithBits(bits);
  return neg ? -x : x;
}

template <int N, int E>
constexpr posit<N, E> ldexp(posit<N, E> x, int exponent) noexcept {
  if (x == posit<N, E>::Zero() || x == posit<N, E>::NaR() || exponent == 0) {
    return x;
  }
  // TODO: Try to optimize this.
  decoded_posit dec = decode_posit<N, E>(x.bits_);
  dec.exponent += exponent;
  return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
}

template <int N, int E>
constexpr int ilogb(posit<N, E> x) noexcept {
  if (x == posit<N, E>::Zero()) return FP_ILOGB0;
  if (x == posit<N, E>::NaR()) return FP_ILOGBNAN;
  using Traits = PositTraits<N, E>;
  using U = typename Traits::Unsigned;
  U bits =
      (x.bits_ >= 0 ? static_cast<U>(x.bits_) : static_cast<U>(-x.bits_))
      & Traits::kMask;
  if (bits == Traits::kMax) return Traits::MaxExp;
  int lz = 0, regime = 0;
  if (bits & (Traits::kHighBit >> 1)) {
    lz = lzcnt(U(~(bits << 1)));
    regime = lz - 1;
  } else {
    lz = lzcnt(bits << 1);
    regime = -lz;
  }
  if (Traits::ExpBits == 0 || lz >= Traits::NBits - 2) {
    return regime * (1 << Traits::ExpBits);
  }
  int exponent = regime * (1 << Traits::ExpBits);
  int shift = Traits::SBits - Traits::ExpBits - lz - 2;
  if constexpr (Traits::SBits > Traits::ExpBits) {
    U kExpMask = (U{1} << Traits::ExpBits) - 1;
    if (shift >= 0) {
      exponent += static_cast<int>((bits >> shift) & kExpMask);
    } else {
      exponent += static_cast<int>((bits << -shift) & kExpMask);
    }
  } else {
    unsigned kExpMask = (unsigned{1} << Traits::ExpBits) - 1;
    exponent += (static_cast<unsigned>(bits) << -shift) & kExpMask;
  }
  return exponent;
}

template <int N, int E>
constexpr posit<N, E> scalbn(posit<N, E> x, int e) noexcept {
  return ldexp(x, e);
}

template <int N, int E>
inline constexpr posit<N, E> e_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0x5BF0A8B145769535U;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = 1;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    // G here can be any integer in [1, MFB]. `G = ceil(lg(MFB))` was chosen
    // as it provides a good tradeoff between the number of Taylor series
    // iterations and number of squaring iterations.
    constexpr int G =
      Traits::MaxFractionBits > 0
          ? 31 - lzcnt(uint32_t{Traits::MaxFractionBits})
          : 0;
    return exp_impl::exp<N, E>(posit<N, E>::One(), G, G);
  }
}();

template <int N, int E>
inline constexpr posit<N, E> ln2_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0x62E42FEFA39EF357U;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = -1;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    return log1p_impl<N, E>(posit<N, E>::One());
  }
}();

template <int N, int E>
inline constexpr posit<N, E> ln10_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0x26BB1BBB5551582DU;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = 1;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else if constexpr (Traits::IntRangeMax >= 10) {
    return log(posit<N, E>(10));
  } else {
    // If the integer 10 isn't representable, then at most 5 bits should be
    // needed for proper rounding. This has 18.
    return posit<N, E>(0x2.4D76p0);
  }
}();

template <int N, int E>
inline constexpr posit<N, E> log2e_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0x71547652B82FE177U;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = 0;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    return 1 / ln2_pos<posit<N, E>>;
  }
}();

template <int N, int E>
inline constexpr posit<N, E> log10e_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0xBCB7B1526E50E32AU;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = -2;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    return 1 / ln10_pos<posit<N, E>>;
  }
}();

template <int N, int E>
inline constexpr posit<N, E> sqrt2_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0x6A09E667F3BCC908U;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = 0;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    // This can't use sqrt(2), as it is defined using sqrt2_pos. Instead,
    // this inlines pow(2, 0.5) and simplifies to: e^(ln(2) / 2).
    return exp(posit<N, E>(ln2_pos<posit<N, E>> *
                           posit<N, E>(2).imprecise_inverse()));
  }
}();

template <int N, int E>
inline constexpr posit<N, E> sqrt3_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0xBB67AE8584CAA73BU;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = 0;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    return sqrt(posit<N, E>(3));
  }
}();

template <int N, int E>
inline constexpr posit<N, E> inv_sqrt3_pos<posit<N, E>> = [] {
  using Traits = PositTraits<N, E>;
  if constexpr (N <= 64) {
    constexpr uint64_t fraction_64 = 0x279A74590331D000U;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    dec.exponent = -1;
    dec.fraction = (fraction_64 >> (64 - Traits::SBits));
    dec.fraction |= 1;
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(dec));
  } else {
    return pow(posit<N, E>(3),
               posit<N, E>(-posit<N, E>(2).imprecise_inverse()));
  }
}();

#if __has_include(<numbers>)
# include <numbers>
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::e_v<posit<N, E>> =
      e_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::log2e_v<posit<N, E>> =
      log2e_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::log10e_v<posit<N, E>> =
      log10e_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::pi_v<posit<N, E>> =
      pi_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::inv_pi_v<posit<N, E>> =
      inv_pi_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::inv_sqrtpi_v<posit<N, E>> =
      inv_sqrtpi_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::ln2_v<posit<N, E>> =
      ln2_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::ln10_v<posit<N, E>> =
      ln10_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::sqrt2_v<posit<N, E>> =
      sqrt2_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::sqrt3_v<posit<N, E>> =
      sqrt3_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::inv_sqrt3_v<posit<N, E>> =
      inv_sqrt3_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::egamma_v<posit<N, E>> =
      egamma_pos<posit<N, E>>;
  template <int N, int E>
  inline constexpr posit<N, E> std::numbers::phi_v<posit<N, E>> =
      phi_pos<posit<N, E>>;
#endif

#endif  // UGHOAVGFHW_POSIT_MATH_H_
