#include <iomanip>
#include <iostream>

#ifndef USE_POSIT_LIB
#define USE_POSIT_LIB 1
#endif

#if USE_POSIT_LIB

#ifdef POSIT_BENCHMARK

// This is bad, and there are standards-compliant ways to access private
// members, but they compile to indirect calls, which could impact benchmarks.
// For best correctness, we remove protections and use the members directly.
#define private public
#include "posit.h"
#undef private

posit32 make_posit(int32_t p) {
  return posit32::WithBits(p);
}

int32_t posit_bits(posit32 p) {
  return p.bits_;
}

#else  // Not a benchmark

#include "posit.h"

using hacker = const char;
template <auto& var, auto val>
hacker steals_private = (void(var = val), 0);

posit32 make_posit(int32_t p) { return posit32::WithBits(p); }

int32_t (posit32::* pos_bits_fld);
template hacker steals_private<pos_bits_fld, &posit32::bits_>;
int32_t posit_bits(posit32 p) {
  return p.*pos_bits_fld;
}

#endif // POSIT_BENCHMARK
#else

#include <math.h>
#include <stdint.h>
#include <limits>

double posit_val(int32_t p) {
  if (p == 0) return 0.0;
  if (p == -0x80000000) return std::numeric_limits<double>::infinity();

  double r = 1.0;
  if (p < 0) {
    p = -p;
    r = -r;
  }
  uint32_t b = p;
  const uint32_t high = 0x80000000U;
  b <<= 1;
  int regime;
  if (b & high) {
    regime = __builtin_clz(~b | 1);
    b <<= regime + 1;
    --regime;
  } else {
    regime = __builtin_clz(b | 1);
    b <<= regime + 1;
    regime = -regime;
  }
  int exp = (b >> 30) & 3;
  exp += regime * 4;
  r *= exp2(exp);
  b <<= 2;
  r *= 1.0 + b / exp2(32);
  return r;
}

int32_t posit_inv(int32_t p) {
  return 0x80000000U - static_cast<uint32_t>(p);
}

int32_t to_posit(double d) {
  if (d == 0.0) return 0;
  if (isinf(d)) return -0x80000000;
  bool neg = d < 0;
  if (neg) d = -d;
  int exp = ilogb(d);
  uint32_t f = floor(d / scalbn(1.0, exp - 32));
  /*
  std::cerr << std::hexfloat << d << " " << (neg ? "-" : "+")
            << "1." << std::hex << std::setfill('0') << std::setw(8) << f
            << "p" << std::dec << exp << "\n";
  */
  int regime = exp >> 2;
  exp = exp & 3;
  uint32_t bits;
  int f_bits;
  if (regime >= 0) {
    bits = -1U;
    bits <<= 31 - regime;
    bits >>= 1;
    f_bits = 27 - regime;
  } else {
    bits = 1;
    bits <<= 30 + regime;
    f_bits = 28 + regime;
  }
  /*
  std::cerr << "regime=" << regime << " exp=" << exp << " f_bits=" << f_bits
            << "\nEncoded regime=" << std::hex << std::setfill('0')
            << std::setw(8) << bits;
  */
  if (f_bits > 0) {
    bits |= exp << f_bits;
    // std::cerr << "\nEncoded exp: " << std::setw(8) << bits;
    bits |= f >> (32 - f_bits);
    if (bits != 0x7FFFFFFF) {  // No overflow.
      uint32_t top = 1U << (32 - f_bits);
      uint32_t dropped = f & (top - 1);
      if (dropped > top/2 || (dropped == top/2 && (bits & 1))) {
        ++bits;
      }
    }
    // std::cerr << "\nEncoded frac: " << std::setw(8) << bits << "\n\n";
  } else {
    bits |= exp >> -f_bits;
    // std::cerr << "\nEncoded exp: " << std::setw(8) << bits;
    if (bits != 0x7FFFFFFF) {  // No overflow.
      if (f_bits < 0) {
        uint32_t top = 1U << -f_bits;
        uint32_t dropped = static_cast<uint32_t>(exp) & (top - 1);
        // Add a bit and use it to encode if the fraction was non-zero, to
        // ensure proper rounding.
        dropped <<= 1;
        if (f != 0) dropped |= 1;
        if (dropped > top || (dropped == top && (bits & 1))) {
          ++bits;
        }
      } else {  // The fraction was dropped, but the exponent encoded fully.
        constexpr uint32_t high = uint32_t{1} << 31;
        if (f > high || (f == high && (bits & 1))) {
          ++bits;
        }
      }
    }
    // std::cerr << "\nRounded exp: " << std::setw(8) << bits << "\n\n";
  }
  if (regime >= 30) bits = 0x7FFFFFFF;
  else if (regime <= -30) bits = 1;
  if (neg) return -static_cast<int32_t>(bits);
  return bits;
}

#endif

int main() {
  uint32_t p = 0;
  uint32_t errors = 0, multi_errors = 0;
  long double sum_ape = 0.0l;
  double max_ape = 0.0;
  quire32 q;
  do {
#ifdef POSIT_BENCHMARK
    posit32 pos = make_posit(p);
    double dbl = pos;
    __asm__ volatile ("" : : "rm"(dbl));
# if POSIT_BENCHMARK >= 2
    posit32 roundtrip{dbl};
    __asm__ volatile ("" : : "rm"(roundtrip));
# endif
#else
# if USE_POSIT_LIB
    posit32 pos = make_posit(p);
    double orig = pos;
    posit32 est_pos = pos.imprecise_inverse();
    double real = isnan(orig) ? 0.0 : (1.0 / orig);
    posit32 near_pos{real};
    double est_val = est_pos;
    uint32_t est = posit_bits(est_pos);
    uint32_t nearest = posit_bits(near_pos);
    if (pos != posit32::NaR()) q += pos;
# else
    double orig = posit_val(p);
    uint32_t est = posit_inv(p);
    double real = 1.0 / orig;
    uint32_t nearest = to_posit(real);
    double est_val = posit_val(est);
# endif
    if (nearest != est) {
      ++errors;
      double ape = (est_val - real) / real;
      if (ape < 0) ape = -ape;
      sum_ape += ape;
      if (ape > max_ape) max_ape = ape;
      if (nearest != est + 1 && nearest != est - 1) {
        ++multi_errors;
      }
    }
#endif
    ++p;
    if (!(p & 0x03FFFFFF)) {
      std::cerr << ".";
      if (!(p & 0x1FFFFFFF)) {
        std::cerr << " ";
      }
    }
  } while (p != 0);
  std::cerr << "\nErrors: " << errors
            << "\nOff by more than one: " << multi_errors
            << "\nAvg abs pct error: " << ((sum_ape / errors) * 100)
            << "%\nMax abs pct error: " << (max_ape * 100) << "%\n";
  if (posit32(q) != 0.0e3_pos32) {
    std::cerr << "Quire is not zero! " << std::hexfloat << (long double)q.to_posit<64>() << "\n";
  }
  q += (2.0 == posit32::One()) * posit32::Max();
  if (!(posit32(quire32::add_all(q, q, q, q, q, q, q, q)) == posit32(0LL))) {
    std::cerr << "Adding 8 quires is not zero!\n";
  }
  static_assert(std::is_same_v<posit64,
                               decltype(posit(q.to_posit<64>()))>);
  static_assert(std::is_same_v<posit32,
                               decltype(posit(1.0_pos32 * 2.0_pos32))>);
  static_assert(std::is_same_v<posit32,
                               decltype(posit(q))>);
  static_assert(std::is_same_v<quire32,
                               decltype(quire(q))>);
  static_assert(std::is_same_v<quire32,
                               decltype(quire(1.0_pos32))>);
  static_assert(std::is_same_v<quire32,
                               decltype(quire(0123_pos32 * 0x2.0p3_pos32))>);
  static_assert(1.25_pos8 == 0x14.p-4_pos16);
  static_assert(0123_pos32 == 83_pos64);
  static_assert(-0b1011_pos32 == -0xB_pos128);
  constexpr posit _ = (0_pos8 + 1.3_pos16 - 1.3_pos16) * 0x0FF_pos32 / 07_pos64;
  static_assert(_ == posit128());
  static_assert(!posit32(
      0_pos32 * (((0_pos32 * 0_pos32) * (0_pos32 * 0_pos32)) * 0_pos32)));
  return 0;
}
