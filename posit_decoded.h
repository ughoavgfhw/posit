#ifndef UGHOAVGFHW_POSIT_DECODED_H_
#define UGHOAVGFHW_POSIT_DECODED_H_

#include "posit_config.h"
#include "posit_utils.h"
#include "posit_traits.h"

template <int S>
struct decoded_posit {
  int sign;
  int exponent;
  typename PositStorageTraits<S>::Unsigned fraction;  // Aligned to high bits.
};

template <int N, int E>
constexpr decoded_posit<PositTraits<N, E>::SBits> decode_posit(
    typename PositTraits<N, E>::Signed val) noexcept {
  using Traits = PositTraits<N, E>;
  using U = typename Traits::Unsigned;
  // A zero input produces {1, (1-NBits) << ExpBits, 0}.
  // A NaR input produces {-1, (1-NBits) << ExpBits, 0}.
  // Note that this exponent is not possible for any other value.
  constexpr U kHighBit = Traits::kHighBit;
  constexpr U kLowBit = Traits::kLowBit;
  // The input gets masked so that the result fraction doesn't accidentally
  // contain set bits which aren't used in the posit.
  constexpr U kMask = Traits::kMask;
  U bits = 0;
  decoded_posit<Traits::SBits> res{};
  if (val < 0) {
    res.sign = -1;
    bits = static_cast<U>(-val) & kMask;
  } else {
    res.sign = 1;
    bits = static_cast<U>(val) & kMask;
  }
  bits <<= 1;
  int lz = 0, regime = 0;
  if (bits & kHighBit) {
    lz = posit_internal::lzcnt(U(U(~bits) | kLowBit));
    regime = lz - 1;
  } else {
    lz = posit_internal::lzcnt(U(bits | kLowBit));
    regime = -lz;
  }
  bits <<= lz; bits <<= 1;
  res.exponent = regime * (1 << Traits::ExpBits);
  if constexpr (Traits::ExpBits > 0) {
    if constexpr (Traits::SBits > Traits::ExpBits) {
      res.exponent +=
          static_cast<int>(bits >> (Traits::SBits - Traits::ExpBits));
      bits <<= Traits::ExpBits;
    } else {
      res.exponent +=
          static_cast<int>(bits) << (Traits::ExpBits - Traits::SBits);
      bits = 0;
    }
  }
  res.fraction = bits;
  __builtin_assume(res.sign == 1 || res.sign == -1);
  return res;
}

// This cannot be used to encode zero or NaR.
template <int N, int E>
constexpr typename PositTraits<N, E>::Signed encode_regular_posit(
    decoded_posit<PositTraits<N, E>::SBits> dec) noexcept {
  __builtin_assume(dec.sign == 1 || dec.sign == -1);
  using Traits = PositTraits<N, E>;
  using U = typename Traits::Unsigned;
  using S = typename Traits::Signed;
  constexpr U kHighBit = Traits::kHighBit;
  constexpr U kLowBit = Traits::kLowBit;
  constexpr U kMask = Traits::kMask;

  int regime = dec.exponent >> Traits::ExpBits;
  // Intentionally left at int size instead of storage size.
  unsigned exp = dec.exponent & ((1 << Traits::ExpBits) - 1);
  if (regime >= Traits::NBits - 2) {
    // Avoid overflow, either from high exponents or rounding later.
    return dec.sign * static_cast<S>(kMask & U(~kHighBit));
  }
  if (regime < 2 - Traits::NBits) {
    // Avoid underflow from very negative exponents. The minimum regime is not
    // handled here, as it can be rounded up to a larger regime.
    return dec.sign * static_cast<S>(kLowBit);
  }

  U bits = 0;
  int f_bits = 0;
  if (regime >= 0) {
    bits = ~U{0};
    bits <<= Traits::SBits - 1 - regime;
    bits >>= 1;
    f_bits = Traits::NBits - 1 - Traits::ExpBits - 2 - regime;
  } else {
    bits = 1;
    bits <<= Traits::SBits - 1 - 1 + regime;
    f_bits = Traits::NBits - 1 - Traits::ExpBits - 1 + regime;
  }
  // f_bits >= -ExpBits. This means the regime terminator is represented in the
  // bits, so at least one bit in the representation is unset (below the sign).

  if (f_bits > 0) {
    bits |= static_cast<U>(exp) << (f_bits + Traits::XBits);
    bits |= (dec.fraction >> (Traits::NBits - f_bits)) & kMask;
    U dropped = dec.fraction << f_bits;
    if (dropped >= kHighBit && (dropped > kHighBit || (bits & kLowBit) != 0)) {
      bits += kLowBit;
    }
  } else {
    bits |= static_cast<U>(exp >> -f_bits) << Traits::XBits;
    if (f_bits < 0) {
      // At least one exponent bit was truncated.
      unsigned cut_bit = 1U << -f_bits;
      unsigned dropped = exp & (cut_bit - 1);
      // Add a low bit indicating if the fraction was non-zero. The shift also
      // puts the high bit of dropped at cut_bit.
      dropped = (dropped << 1) + (dec.fraction != 0);
      if (dropped >= cut_bit && (dropped > cut_bit || (bits & kLowBit) != 0)) {
        bits += kLowBit;
      }
    } else {
      // The entire exponent was stored but no fraction bits.
      if (dec.fraction >= kHighBit &&
          (dec.fraction > kHighBit || (bits & kLowBit) != 0)) {
        bits += kLowBit;
      }
    }
  }

  return dec.sign * static_cast<S>(bits);
}

#endif  // UGHOAVGFHW_POSIT_DECODED_H_
