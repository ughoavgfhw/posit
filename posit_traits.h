#ifndef UGHOAVGFHW_POSIT_TRAITS_H_
#define UGHOAVGFHW_POSIT_TRAITS_H_

#include "posit_config.h"

#include <limits.h>  // For CHAR_BIT
#include <stdint.h>

#include "posit_utils.h"
#include "posit_fwd.h"

template <int N, typename Enable = void>
struct PositStorage {
  using Signed = typename posit_internal::cond<N <= 8>::template then<int8_t>
                     ::template next<N <= 16>::template then<int16_t>
                     ::template next<N <= 32>::template then<int32_t>
                     ::template next<N <= 64>::template then<int64_t>
#if POSIT_HAS_INT128
                     ::template next<N <= 128>::template then<__int128>
#endif
#if POSIT_HAS_EXTINT
                     ::template next<true>::template then<_ExtInt(N)>
#endif
                     ::template otherwise<void>;

  using Unsigned = typename posit_internal::cond<N <= 8>::template then<uint8_t>
                       ::template next<N <= 16>::template then<uint16_t>
                       ::template next<N <= 32>::template then<uint32_t>
                       ::template next<N <= 64>::template then<uint64_t>
#if POSIT_HAS_INT128
                       ::template next<N <= 128>
                           ::template then<unsigned __int128>
#endif
#if POSIT_HAS_EXTINT
                       ::template next<true>::template then<unsigned _ExtInt(N)>
#endif
                       ::template otherwise<void>;
};

template <int N>
struct PositStorageTraits {
  static_assert((N & (N - 1)) == 0 ||
                (N % (CHAR_BIT * sizeof(ptrdiff_t))) == 0,
                "N must be a power of two or multiple of a pointer difference");
  static_assert(N >= 3, "N must be at least 3");

  static constexpr int SBits = N;

  using Signed = typename PositStorage<N>::Signed;
  using Unsigned = typename PositStorage<N>::Unsigned;
  static_assert(!std::is_same_v<void, Signed>,
                "No posit storage type available for this size.");

  static constexpr bool DoubleSizeAvailable =
      !std::is_same_v<void, typename PositStorage<N * 2>::Signed>;

  static constexpr Signed kZero = 0;
  static constexpr Signed kNaR = Signed{1} << (N - 1);
  static constexpr Signed kOne = Signed{1} << (N - 2);

  static constexpr Unsigned kHighBit = Unsigned{1} << (SBits - 1);
};

template <int S, bool AllowArray = false>
using PositDoubleUnsigned =
    typename posit_internal::cond<PositStorageTraits<S>::DoubleSizeAvailable>
        ::template then<typename PositStorage<S * 2>::Unsigned>
    ::template next<AllowArray>
        ::template then<typename PositStorage<S>::Unsigned[2]>
    ::type;

template <int N, int E>
struct PositTraits {
  // A 2-bit posit has values 0, 1, -1, and NaR.
  static_assert(N >= 2, "Posits must have at least 2 bits of encoding.");
  static_assert(N > 2 || E == 0, "A 2 bit posit must have 0 exponent bits.");
  static_assert(E <= 20 && E <= sizeof(int) * CHAR_BIT - 2,
                "Exponents may only be up to 20 bits, or 2 fewer than an int, "
                "whichever is smaller.");

  static constexpr int NBits = N;
  static constexpr int ExpBits = E;
  static constexpr int SBits =
      (N <= (POSIT_HAS_INT128 ? 128 : 64))
          ? (N <= 8 ? 8 : N <= 16 ? 16 : N <= 32 ? 32 : N <= 64 ? 64 : 128)
          : ((N + CHAR_BIT * sizeof(ptrdiff_t) - 1)
                 / (CHAR_BIT * sizeof(ptrdiff_t))
                 * CHAR_BIT * sizeof(ptrdiff_t));
  static constexpr int XBits = SBits - NBits;
  static constexpr int UncappedMaxFractionBits =
      NBits - 1 /* sign */ - 2 /* minimal regime */ - ExpBits;
  static constexpr int MaxFractionBits =
      UncappedMaxFractionBits > 0 ? UncappedMaxFractionBits : 0;

  using Storage = PositStorageTraits<SBits>;
  using Signed = typename Storage::Signed;
  using Unsigned = typename Storage::Unsigned;

  static constexpr Unsigned kHighBit = Storage::kHighBit;
  static constexpr Unsigned kLowBit = Unsigned{1} << XBits;
  static constexpr Unsigned kMask = Unsigned(~Unsigned{0}) << XBits;
  static constexpr Signed kZero = Storage::kZero;
  static constexpr Signed kNaR = Storage::kNaR;
  static constexpr Signed kOne = Storage::kOne;
  static constexpr Signed kMax = (kOne + (kOne - 1)) & kMask;
  static constexpr Signed kMin = 1 << XBits;

  static constexpr int MaxExp = (NBits - 2) * (1 << ExpBits);
  static constexpr int MinExp = -MaxExp;

  // The approximate power of 10 of Max(). This is always >= the true value.
  // Note that this is the exponent of the value, so it is possible that
  // `Max() > pow10(ApproxMaxExp10)`. In fact, Max() will only be less than
  // this power of 10 if this is an over-estimate.
  static constexpr int ApproxMaxExp10 =
      // Standard approximation 10 bits = 3 decimal digits, rounded up.
      (MaxExp + 9) / 10 * 3 +
      // The standard approximation is an under-estimate, with an extra digit
      // needed every ~970.9 bits. Since the approximation is rounded up, the 
      // extra digit can be delayed until the multiple of 10 after 970. With
      // this, we have an over-estimate for all values of MaxExp. For large
      // values, starting around MaxExp=11650, it is never the true value and
      // may grow further and further from the true value.
      ((MaxExp - 10) / 970);
  // Like ApproxMaxExp10, but always less than or equal the true value. See
  // the documentation there for a more thorough explanation.
  static constexpr int ApproxMaxExp10LowerBound =
      // This is actually diverges from the true value more slowly than the
      // over-estimate, since the correction factor is much closer to every
      // 971 bits than every 970.
      MaxExp / 10 * 3 + MaxExp / 971;

  // To understand this calculation, first recognize that the result must be
  // a power of 2:
  // a) If `2^k + 1` is representable, there must be at least k fraction bits
  //    in that representation.
  // b) The number of fraction bits available only changes if the regime does,
  //    which happens on power of 2 boundaries.
  // c) Given (a) and (b), then `2^k + 1` being representable implies that
  //    all numbers up to and including `2^(k+1) - 1` are also representable.
  // d) `2^(k+1)` requires 0 fraction bits, so is only non-representable if a
  //    non-zero exponent bit does not fit the representation.
  // e) If k > 0, there is at least one fraction bit in the representation.
  //    Thus, if `2^k` and `2^(k+1)` have the same regime, `2^(k+1)` is also
  //    representable. If they have different regimes, then the exponent field
  //    of `2^(k+1)` cannot have any non-zero bits.
  // f) Therefore, if k > 0 and `2^k + 1` is representable, `2^(k+1)` must also
  //    be representable. If k == 0, then `2^k + 1 == 2 == 2^(k+1)`, which is
  //    a power of 2. If k < 0, then `2^k` is not an integer and something has
  //    gone terribly wrong.
  // g) Given (c) and (f), if `x` is representable then `x + 1` is also
  //    representable unless `x` is a power of 2. Therefore the boundary must
  //    be a power of 2.
  //
  // Having settled that, we must find the minimal k where `2^k + 1` is
  // representable but `2^(k+1) + 1` is not. As mentioned in point (a),
  // `2^x + 1` is representable if it has at least `x` fraction bits. The
  // representation for the integer 1 has exactly `MaxFractionBits` (a.k.a. MFB)
  // fraction bits. Growing from there, every increment of the regime reduces
  // the number of fraction bits by one. The regime for `2^k` is
  // `k_r = k >> ExpBits`, and the exponent field is `k_e = k % (1 << ExpBits)`.
  //
  // Then, `2^k + 1` is representable iff
  //     MFB - (k >> ExpBits) >= k
  // or equivalently
  //     MFB - k_r >= k_r * 2^ExpBits + k_e
  // Rearranging and distributing, we get
  //     MFB - k_e >= k_r * (2^ExpBits + 1)
  // and finally solving for `k_r`
  //     k_r <= (MFB - k_e) / (2^ExpBits + 1)
  // By definition `k_e` must be less than `2^ExpBits`, and every increment of
  // `k_r` increases our range by a factor of `2^ExpBits`, so we want to
  // find the maximum `k_r` for any `k_e`. We simply set `k_e` to 0.
  //     k_r <= MFB / (2^ExpBits + 1)  // Truncating integer division.
  // Once we fix our `k_r`, we set `k_e` to use all remaining fraction bits.
  //     k_x = MFB - k_r * (2^ExpBits + 1)
  //         = MFB - (MFB / (2^ExpBits + 1)) * (2^ExpBits + 1)
  //         = MFB % (2^ExpBits + 1)
  // However, it's possible there are `2^ExpBits` fraction remaining, but
  // `k_e` must be less than `2^ExpBits`. This occurs when `2^k` has all bits
  // in the exponent field set and exactly `k+1` fraction bits. There are
  // enough fraction bits to increment the exponent, but doing so would also
  // increment the regime and reduce the number of fraction bits; the last
  // fraction bit does not increase the range of representable integers.
  //     k_x = MFB % (2^ExpBits + 1)
  //     k_e = k_x - (k_x == 2^ExpBits ? 1 : 0)
  //
  // Finally, putting the pieces back together, the range of fully
  // representable integers ends at
  //     2^(k+1) = 2^(k_r * 2^ExpBits + k_e + 1)
  // There is an exception for `MFB < 0`, which would result in a non-integral
  // `2^k`. All posits can represent -1, 0, and 1. When `MFB < 0`, at least one
  // exponent bit has been lost for all values, so 2 is not representable.
  // Therefore, in this case the integer range ends at `1 == 2^0`.
  static constexpr int IntRangeMaxExp =
      UncappedMaxFractionBits >= 0
          ? // Regime << ExpBits.
            ((MaxFractionBits / (1 + (1 << ExpBits))) << ExpBits)
            // Exponent field.
            + (MaxFractionBits % (1 + (1 << ExpBits)))
            // Correction for exponent field overflow.
            - ((MaxFractionBits % (1 + (1 << ExpBits))) == (1 << ExpBits))
            // We want k+1
            + 1
          : 0;
  static constexpr Signed IntRangeMax = Signed{1} << IntRangeMaxExp;
  static constexpr Signed IntRangeMin = -IntRangeMax;

  static constexpr int FractionBitsAtExponent(int exponent) noexcept {
    int regime = exponent >> ExpBits;
    // Minimal regime bits are already accounted for in MaxFractionBits.
    int extra_regime_bits = regime >= 0 ? regime : (-regime - 1);
    int fraction_bits = MaxFractionBits - extra_regime_bits;
    return fraction_bits >= 0 ? fraction_bits : 0;
  }

  using quire_type = quire<(NBits - 2) << (ExpBits + 1), NBits>;

  // This makes no sense, constructing a PositTraits never really makes sense,
  // but is used to extract the N and E from a posit type for the posit
  // deduction guides. DO NOT depend on its existence.
  explicit PositTraits(posit<N, E>);
};

template <int S>
struct PositByStorage {
  using Traits = PositStorageTraits<S>;
  using Signed = typename Traits::Signed;
  using Unsigned = typename Traits::Unsigned;
  static constexpr int SBits = Traits::SBits;

  static constexpr Signed kZero = Traits::kZero;
  static constexpr Signed kNaR = Traits::kNaR;
  static constexpr Signed kOne = Traits::kOne;

  struct BasicPrecheckResult {
    Signed value;
    bool has_value;
  };

  using FromFloatPrecheckResult = BasicPrecheckResult;
  template <typename F>
  static constexpr FromFloatPrecheckResult FromFloatPrecheck(
      F floatval) noexcept;

  template <typename F>
  static constexpr decoded_posit<S> FromFloat(F floatval) noexcept;

  template <typename F>
  static constexpr F ToFloat(decoded_posit<SBits> dec) noexcept;

  // Assumes abs(intval) > 1.
  template <typename I>
  static constexpr decoded_posit<S> FromInt(I intval) noexcept;

  template <typename I>
  static constexpr I ToInt(decoded_posit<SBits> dec) noexcept;

  struct mult_intermediate;

  static constexpr mult_intermediate Multiply(
      decoded_posit<S> l_dec, decoded_posit<S> r_dec) noexcept;

  using DividePrecheckResult = BasicPrecheckResult;
  static constexpr DividePrecheckResult DividePrecheck(Signed n,
                                                       Signed d) noexcept;

  // MaxFractionBits is only used if Traits::DoubleSizeAvailable is false.
  template <int MaxFractionBits>
  static constexpr decoded_posit<S> DivideImpl(
      decoded_posit<SBits> n, decoded_posit<SBits> d) noexcept;

  template <typename PosTraits>
  static constexpr typename PosTraits::Signed Divide(
      typename PosTraits::Signed n, typename PosTraits::Signed d) noexcept;

  struct AddSubPrecheckResult {
    // If pre_result is set, a holds the result, though it may need to be
    // negated if the order switched for `0 - x`.
    // Otherwise, a has a larger magnitude than b.
    Signed a;
    Signed b;
    bool pre_result : 1;  // a holds the final result, not an input.
    bool switched_order : 1;  // a and b were swapped.
    bool differing_signs : 1;  // a and b have different signs.
  };

  static constexpr AddSubPrecheckResult AddSubPrecheck(
      Signed l, Signed r) noexcept;

  static constexpr decoded_posit<S> Add(
      decoded_posit<S> a_dec, int b_exp, Unsigned b_fraction) noexcept;

  static constexpr decoded_posit<S> Subtract(
      decoded_posit<S> a_dec, int b_exp, Unsigned b_fraction) noexcept;
};

#endif  // UGHOAVGFHW_POSIT_TRAITS_H_
