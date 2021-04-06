#ifndef UGHOAVGFHW_POSIT_H_
#define UGHOAVGFHW_POSIT_H_

/* Posits are a floating point number format. In comparison to IEEE-754 formats:
 * - Posits have fewer redundant encodings, meaning more exact values.
 * - Posits do not overflow to infinity or underflow to 0. `max * max == max`.
 * - Posits are totally ordered. Zero is unsigned, NaR (not-a-real number) is
 *   sorted below all other values, `NaR == NaR`.
 * - Posits do not have infinities. Invalid operations, such as `1/0` return
 *   NaR. Valid operations which result in values outside the represented range
 *   are rounded to the maximum signed value.
 * - Posits provide quire types, which defer rounding of sums. This reduces
 *   error, and provides associativity of addition and distribution of
 *   multiplication over addition, when summing more than two values.
 * - Posits have gradual precision loss; values with a magnitude near 1 have
 *   the most precision, and it slowly decreases as the exponent increases.
 *   This allows a 16-bit posit to both provide 13 bits of accuracy as well as
 *   a positive range of [2^-28, 2^28]. For comparison, the IEEE-754 binary16
 *   type has 11 bits of accuracy and a normal positive range of [2^-24, <2^16]
 *   including subnormals.
 *
 * This library is based on the posit 3.2-draft standard of 2018-06-23,
 * currently available at https://posithub.org/docs/posit_standard.pdf, though
 * it is not verified to be precisely conforming.
 *
 * This library provides the posit and quire types, as well as basic operations
 * and comparisons. It also specializes std::numeric_traits for posit types.
 * See also posit_math.h for various standard functions and numeric constants.
 *
 *
 * OVERVIEW
 *
 * Types:
 * - posit<N, E>: A posit type with N bits and E exponent bits.
 * - quire<NQ, C>: A quire type with a range of 2^±NQ which is guaranteed not
 *   to overflow when summing up to `2^C - 1` values. Posit types provide a
 *   `quire_type` member alias to their "preferred" quire type.
 * - positN, quireN: Aliases to the standard posit and quire types, where N is
 *   one of 8, 16, 32, or 64. 128 is also supported on implementations with a
 *   128-bit integer type.
 *
 * Operations:
 * - Negation, addition, subtraction, multiplication, and division of posits,
 *   including corresponding assignment operators.
 * - Quire addition-assignment and subtraction-assignment for posits and quires.
 * - fused_add(): Performs the same operation as a quire for exactly two
 *   values, but more efficiently. If neither argument is the result of a
 *   multiplication, this is the same as using the addition operator.
 * - nextafter(posit, posit): Returns the next representable value after the
 *   first parameter in the direction of the second parameter.
 * - nexttoward(posit, T): The same as nextafter, except that the second value
 *   may be of a different type with values not representable by the first.
 *   The direction of movement is determined without rounding the second value.
 *   T may be either `long double`, or any posit type.
 * - User-defined literals for the standard posit types, _posN.
 *
 * Posits may be constructed from any numeric type. This constructor is
 * implicit if the posit type can represent all values of the source type.
 * Similarly, they may be converted to any numeric type. This is implicit if
 * the destination can represent all values of the posit type. Conversion to
 * an integer truncates, except conversion to a bool returns true for any
 * non-zero value. These rules also apply to conversion between posit types.
 *
 * Posits provide static member functions Zero(), One(), Min(), Max(), and
 * NaR(), returning the indicated values. Note: Min is the smallest positive
 * value, use -Max() to get the most negative value.
 *
 * Quires may be constructed from any type which may be summed into them. In
 * addition to their default posit type, or the result of a multiplication of
 * their default posit type, this includes other posit types or multiplication
 * results based only on their exponent range. Thus, a posit may be summed into
 * a quire even if it can't be implicitly converted to that quire's default
 * posit type, whether due to a larger range or more precision.
 *
 * Quires may be explicitly converted to their default posit type, which rounds
 * their contained value into that type. Additionally, any posit type may be
 * extracted from any quire type using `my_quire.to_posit<N, E>()`.
 *
 * std::numeric_limits is specialized for posit<N, E>. In addition to the
 * standard members, it additionally provides
 *     constexpr int digits_at_exponent(int exponent) noexcept;
 * which indicates the number of bits of precision for any value based on the
 * binary exponent of its highest set bit.
 */

#include "posit_config.h"

#include <fenv.h>
#include <math.h>
#include <stdint.h>
#include <string.h>
#include <limits>
#include <new>
#include <type_traits>
#if __has_include(<compare>)
# include <compare>
#endif

#include "posit_utils.h"
#include "posit_fwd.h"
#include "posit_traits.h"
#include "posit_decoded.h"

// TODO: Namespace things.
using namespace posit_internal;

// Note: This is forward declared here instead of hidden in posit_fwd.h, to
// avoid extra includes there.
template <int N1, int E1, int N2, int E2>
using fused_add_result =
    typename posit_internal
    ::cond<std::is_convertible_v<posit<N1, E1>, posit<N2, E2>>>
        ::template then<posit<N2, E2>>
    ::template next<std::is_convertible_v<posit<N2, E2>, posit<N1, E1>>>
        ::template then<posit<N1, E1>>
    ::type;
template <int N1, int E1, int N2, int E2>
constexpr fused_add_result<N1, E1, N2, E2> fused_add(
    posit_mult_intermediate<N1, E1> lhs, posit_mult_intermediate<N2, E2> rhs)
    noexcept;

template <int N, int E>
class posit {
 private:
  using Traits = PositTraits<N, E>;

  // numeric_limits' unspecialized definition default-constructs its type for
  // member functions, which causes errors if there is no accessible default
  // constructor. In order to avoid the errors,
  // - std::conjunction is used to avoid calculating them for non-specialized
  //   types
  // - their use is hidden behind a struct
  // The latter is important, and cannot be changed to an alias or variable, as
  // only putting them _inside_ a non-instantiated type will prevent them from
  // being calculated until needed.

  template <typename I>
  struct IntAlwaysFits :
      public std::bool_constant<
                 std::numeric_limits<I>::max() <= Traits::IntRangeMax &&
                 (std::numeric_limits<I>::lowest() >= Traits::IntRangeMin)> {};

  // Does not check for subnormals fitting. Specialized below to exclude posits.
  // Decimal types are never included as posits can't represent a single
  // decimal digit for large or small exponents.
  template <typename F>
  struct FloatAlwaysFits :
      public std::bool_constant<
                 std::numeric_limits<F>::radix == 2 &&
                 std::numeric_limits<F>::digits <= 1+Traits::MaxFractionBits &&
                 std::numeric_limits<F>::max_exponent <= 1+Traits::MaxExp &&
                 Traits::MinExp < std::numeric_limits<F>::min_exponent &&
                 std::numeric_limits<F>::digits <=
                     1+Traits::FractionBitsAtExponent(
                           std::numeric_limits<F>::max_exponent - 1) &&
                 std::numeric_limits<F>::digits <=
                     1+Traits::FractionBitsAtExponent(
                           std::numeric_limits<F>::min_exponent)> {};

  // Must fit while ignoring subnormals. Specialized below to exclude posits,
  // handle decimal floating point types, and handle types which have a
  // non-constant number of digits for normal values.
  template <typename F, typename = void>
  struct FitsIntoFloat :
      public std::bool_constant<
                 std::numeric_limits<F>::radix == 2 &&
                 Traits::MaxFractionBits < std::numeric_limits<F>::digits &&
                 Traits::MaxExp < std::numeric_limits<F>::max_exponent &&
                 std::numeric_limits<F>::min_exponent <= 1+Traits::MinExp> {};

  template <int N2, int E2>
  static constexpr bool PositAlwaysFits =
      // Increasing N increases both the fraction size and exponent range.
      // Changing E as well could counter one of these but make the other
      // worse, so increasing N always results in a non-fitting posit.
      N2 <= N &&
      // Changing E would increase either the fraction size or exponent range,
      // and decrease the other. Both can be countered by a decrease in N.
      // If the maximum fraction size is not bigger and the exponent range is
      // not bigger, then the fraction size must be no bigger at any exponent,
      // since all posits decrease linearly to 0.
      PositTraits<N2, E2>::MaxFractionBits <= Traits::MaxFractionBits &&
      PositTraits<N2, E2>::MaxExp <= Traits::MaxExp;

  using mult_intermediate = posit_mult_intermediate<N, E>;

 public:
  using quire_type = typename Traits::quire_type;

  static constexpr posit Zero() noexcept { return WithBits(Traits::kZero); }
  static constexpr posit One() noexcept { return WithBits(Traits::kOne); }
  static constexpr posit NaR() noexcept { return WithBits(Traits::kNaR); }
  static constexpr posit Min() noexcept { return WithBits(Traits::kMin); }
  static constexpr posit Max() noexcept { return WithBits(Traits::kMax); }

  constexpr posit() noexcept : bits_(Traits::kZero) {}

  // Other constructors. These are defined below but the declarations are
  // not so pleasant to read.
  //
  // Explicit unless all values of posit<N2, E2> are representable in
  // this posit.
  // explicit? posit(posit<N2, E2>) noexcept;
  //
  // Explicit unless all normalized values of FloatType are representable in
  // this posit.
  // explicit? posit(FloatType) noexcept;
  //
  // Explicit unless all values of IntType are representable in this posit.
  // explicit? posit(IntType) noexcept;

  constexpr posit(const posit&) noexcept = default;
  constexpr posit& operator=(const posit&) noexcept = default;

  // Conversion operators. These are defined below but the declarations are
  // not so pleasant to read.
  //
  // Explicit unless all values of this posit are representable in FloatType.
  // explicit? operator FloatType() const noexcept;
  //
  // explicit operator IntType() const noexcept;

  // The standard posit types are also constructible via user-defined literals.

  // For simplicity, all posit types are friends with all of the UDL functions.
  template <char... Chars>
  friend constexpr posit8 operator""_pos8() noexcept;
  template <char... Chars>
  friend constexpr posit16 operator""_pos16() noexcept;
  template <char... Chars>
  friend constexpr posit32 operator""_pos32() noexcept;
  template <char... Chars>
  friend constexpr posit64 operator""_pos64() noexcept;
#if POSIT_HAS_INT128
  template <char... Chars>
  friend constexpr posit128 operator""_pos128() noexcept;
#endif

  // This function produces a value somewhat near the multiplicative inverse,
  // but often with only a few bits of precision, with errors of up to 12.5%.
  // As a special case, powers of two always return an exact result.
  // In all cases, `x.imprecise_inverse().imprecise_inverse() == x`.
  //
  // This function does not special-case NaR; NaR().imprecise_inverse() == 0.
  constexpr posit imprecise_inverse() const noexcept {
    return WithBits(static_cast<typename Traits::Unsigned>(Traits::kNaR) -
                    static_cast<typename Traits::Unsigned>(bits_));
  }

  friend constexpr mult_intermediate operator* <N, E>(posit lhs, posit rhs)
      noexcept;
  friend constexpr posit operator/ <N, E>(posit n, posit d) noexcept;
  friend constexpr posit operator+ <N, E>(posit lhs, posit rhs) noexcept;
  friend constexpr posit operator- <N, E>(posit lhs, posit rhs) noexcept;

  constexpr posit operator-() const noexcept { return WithBits(-bits_); }
  // Note: This should be after the friend declaration for
  // `operator-(posit,posit)`, or the friend declaration would need to be
  // namespace qualified.

#if __has_feature(__cpp_impl_three_way_comparison)
  friend constexpr std::strong_ordering operator<=>(posit, posit) noexcept =
      default;
#endif
#if !__has_feature(__cpp_impl_three_way_comparison) || !(__cpp_lib_three_way_comparison >= 201907L)
  friend constexpr bool operator==(posit lhs, posit rhs) noexcept {
    return lhs.bits_ == rhs.bits_;
  }
  friend constexpr bool operator!=(posit lhs, posit rhs) noexcept {
    return !(lhs == rhs);
  }
  friend constexpr bool operator<(posit lhs, posit rhs) noexcept {
    return lhs.bits_ < rhs.bits_;
  }
  friend constexpr bool operator>(posit lhs, posit rhs) noexcept {
    return rhs < lhs;
  }
  friend constexpr bool operator<=(posit lhs, posit rhs) noexcept {
    return !(lhs > rhs);
  }
  friend constexpr bool operator>=(posit lhs, posit rhs) noexcept {
    return !(lhs < rhs);
  }
#endif

  // Posit conversions.
  // posit<N1, E1> -> posit<N2, E2> is implicit iff every value of
  // type posit<N1, E1> is exactly representable by posit<N2, E2>.
  // Specifically, this means posit<N2, E2> has at least as large of an
  // exponent range, and has at least as many bits of precision for the
  // entirety of posit<N1, E1>'s range.

  template <int N2, int E2, enable_if_t<(N != N2 || E != E2) &&
                                        PositAlwaysFits<N2, E2>>* = nullptr>
  constexpr posit(posit<N2, E2> p) noexcept : bits_(ReencodePosit(p)) {}

  template <int N2, int E2, enable_if_t<(N != N2 || E != E2) &&
                                        !PositAlwaysFits<N2, E2>>* = nullptr>
  explicit constexpr posit(posit<N2, E2> p) noexcept
      : bits_(ReencodePosit(p)) {}

  // Floating point conversions.
  // - Floating point type F -> posit is implicit iff every normalized value of
  //   type F is exactly representable by the posit. Infinity is converted to
  //   NaR, zero loses any sign, and subnormals may lose precision.
  // - Posit -> floating point type F is implicit iff all non-zero real values
  //   the posit are exactly representable by a normalized value of type F.
  //   Zero is always positive, and NaR maps to a quiet NaN unless only
  //   signalling NaNs are available.

  template <typename F,
            enable_if_t<
                enable_if_t<std::numeric_limits<F>::is_specialized &&
                                !std::numeric_limits<F>::is_integer,
                            FloatAlwaysFits<F>>::value>* = nullptr>
  constexpr posit(F floatval) noexcept : bits_(EncodeFloat(floatval)) {}

  template <typename F,
            enable_if_t<
                enable_if_t<
                    std::numeric_limits<F>::is_specialized &&
                        !std::numeric_limits<F>::is_integer,
                    std::negation<FloatAlwaysFits<F>>>::value>* = nullptr>
  explicit constexpr posit(F floatval) noexcept
      : bits_(EncodeFloat(floatval)) {}

  template <typename F,
            enable_if_t<
                enable_if_t<std::numeric_limits<F>::is_specialized &&
                                !std::numeric_limits<F>::is_integer,
                            FitsIntoFloat<F>>::value>* = nullptr>
  operator F() const noexcept { return ToFloat<F>(); }

  template <typename F,
            enable_if_t<
                enable_if_t<std::numeric_limits<F>::is_specialized &&
                                !std::numeric_limits<F>::is_integer,
                            std::negation<FitsIntoFloat<F>>>::value>* = nullptr>
  explicit operator F() const noexcept { return ToFloat<F>(); }

  // Integer conversions.
  // - Integer type I -> posit is implicit iff every value of type I is
  //   exactly representable by the posit.
  // - Posit -> integer type I is always explicit.

  template <typename I,
            enable_if_t<
                enable_if_t<std::numeric_limits<I>::is_integer &&
                                !std::is_same_v<bool, I>,
                            IntAlwaysFits<I>>::value>* = nullptr>
  constexpr posit(I intval) noexcept : bits_(EncodeInteger(intval)) {}

  template <typename I,
            enable_if_t<
                enable_if_t<std::numeric_limits<I>::is_integer &&
                                !std::is_same_v<bool, I>,
                            std::negation<IntAlwaysFits<I>>>::value>* = nullptr>
  explicit constexpr posit(I intval) noexcept
      : bits_(EncodeInteger(intval)) {}

  template <typename I,
            enable_if_t<std::numeric_limits<I>::is_integer &&
                        !std::is_same_v<bool, I>>* = nullptr>
  constexpr explicit operator I() const noexcept {
    static_assert(std::numeric_limits<I>::radix == 2);

    if (bits_ == Traits::kZero) return 0;
    if (bits_ == Traits::kNaR) return std::numeric_limits<I>::max();

    decoded_posit<Traits::SBits> dec = decode_posit<N, E>(bits_);
    return PositByStorage<Traits::SBits>::template ToInt<I>(dec);
  }

  // Construction from a bool.
  // The templates fail for bool, because make_unsigned<bool> has no type.
  //
  // This is a template that only allows bool. It cannot be a non-template,
  // because then it would take anything that can be implicitly converted
  // to bool, including other arithmetic types which should be handled by
  // other, explicit constructors.
  template <typename B, enable_if_t<std::is_same_v<bool, B>>* = nullptr>
  constexpr posit(B v) noexcept : bits_(v ? Traits::kOne : Traits::kZero) {}

  // Conversion to a bool. As normal for bool conversions, this is `*this != 0`.
  constexpr explicit operator bool() const noexcept { return bits_ != 0; }

  // Advanced construction, most users should not call this.
  static constexpr posit WithBits(typename Traits::Signed bits) noexcept {
    posit p;
    p.bits_ = bits;
    return p;
  }

 private:
  friend class posit_mult_intermediate<N, E>;
  template <int NQ, int C>
  friend class quire;
  template <int, int>
  friend class posit;

  friend constexpr posit nextafter<N, E>(posit from, posit to) noexcept;
  friend constexpr posit nexttoward<N, E>(posit from, long double to) noexcept;
  template <int N1, int E1, int N2, int E2>
  friend constexpr posit<N1, E1> nexttoward(posit<N1, E1> from,
                                            posit<N2, E2> to) noexcept;

  template <int N_, int E_>
  friend constexpr posit<N_, E_> frexp(posit<N_, E_>, int* exponent) noexcept;
  template <int N_, int E_>
  friend constexpr posit<N_, E_> ldexp(posit<N_, E_>, int exponent) noexcept;
  template <int N_, int E_>
  friend constexpr int ilogb(posit<N_, E_> x) noexcept;

  template <int N2, int E2>
  static constexpr typename Traits::Signed ReencodePosit(posit<N2, E2> p)
      noexcept;

  template <typename F>
  static constexpr typename Traits::Signed EncodeFloat(F floatval) noexcept {
    auto precheck = PositByStorage<Traits::SBits>::FromFloatPrecheck(floatval);
    if (precheck.has_value) return precheck.value;
    return encode_regular_posit<N, E>(
        PositByStorage<Traits::SBits>::FromFloat(floatval));
  }

  template <typename F>
  constexpr F ToFloat() const noexcept {
    if (bits_ == Traits::kZero) return F{0};
    if (bits_ == Traits::kNaR) {
      if constexpr (!std::numeric_limits<F>::has_quiet_NaN) {
        if constexpr (std::numeric_limits<F>::has_signaling_NaN) {
          return std::numeric_limits<F>::signaling_NaN();
        } else if constexpr (std::numeric_limits<F>::has_infinity) {
          // Not a great fallback, but better than returning a real number.
          return std::numeric_limits<F>::infinity();
        }
      }
      return std::numeric_limits<F>::quiet_NaN();
    }
    return PositByStorage<Traits::SBits>::template ToFloat<F>(
        decode_posit<N, E>(bits_));
  }

  template <typename I>
  static constexpr typename Traits::Signed EncodeInteger(I intval) noexcept {
    static_assert(std::numeric_limits<I>::radix == 2);

    if (intval == 0) return Traits::kZero;
    if (intval == 1) return Traits::kOne;
    if (std::numeric_limits<I>::is_signed && intval == -1) {
      return -Traits::kOne;
    }
    return encode_regular_posit<N, E>(
        PositByStorage<Traits::SBits>::FromInt(intval));
  }

  typename Traits::Signed bits_;
};
template <int N, int E>
posit(posit<N, E>) -> posit<N, E>;
template <int N, int E>
posit(posit_mult_intermediate<N, E>) -> posit<N, E>;
template <int NQ, int C,
          typename Traits = decltype(PositTraits(quire<NQ, C>().to_posit()))>
explicit posit(quire<NQ, C>) -> posit<Traits::NBits, Traits::ExpBits>;

// Quires allow many posits, or products of two posits, to be accumulated
// without intermediate rounding. For example:
//
//   quire32 sum_squares;
//   for (posit32 p : GetPosits()) {
//     // Neither the multiplication nor addition operations cause rounding.
//     // sum_squares contains the exact result, no matter the value of p.
//     sum_squares += p * p;
//   }
//   // Converting back to a posit performs the only rounding in this example.
//   posit32 p = sum_squares.to_posit();
//
// Note that only a single multiplication may be performed outside the quire
// before rounding, so the following all round once:
//
//   q += p1 * p2 * p3;  // Rounds after the first multiplication.
//   q += p1 + p2;       // Direct addition rounds. `(q += p1) += p2` would not.
//   q += p1 / p2;       // Division always rounds.
//   q += p1 * (1/p2);   // The inverse rounds, but the multiplication does not.
//
// Every posit type has an associated quire type, which can be determined via
// `posit::quire_type`. However, a quire will accept smaller or slightly larger
// posits as input, and can be converted to any posit for output.
//
//   quire32 q;
//   q += posit<32, 2>();  // aka posit32
//   q += posit8() * posit8();
//   q += posit<60, 2>();  // Larger than posit32, but not than posit32*posit32.
//   q.to_posit<64, 3>();  // Output as a posit64.
//   q.to_posit<64>();     // Exponent is optional for the standard sizes.
//   q.to_posit<128>();    // Even better precision, if supported.
template <int NQ, int C>
class quire {
 private:
  static constexpr int MinBits = NQ * 2 + 1 + C;
  // Exponent of the lowest bit.
  static constexpr int MinExp = -NQ;

  using ArrayType = typename cond<MinBits <= sizeof(unsigned int) * CHAR_BIT>
                        ::template then<unsigned int>
                        ::template otherwise<unsigned long>;
  static constexpr int ArrayEntries =
      (MinBits + sizeof(ArrayType) * CHAR_BIT - 1) /
      (sizeof(ArrayType) * CHAR_BIT);
  static constexpr int ArrayEntryBits = sizeof(ArrayType) * CHAR_BIT;
  static constexpr ArrayType kHighBit = ArrayType{1} << (ArrayEntryBits - 1);

  static constexpr int NBits = ArrayEntries * ArrayEntryBits;

  template <int N, int E>
  static constexpr bool kPositFits = posit<N, E>::Traits::MaxExp <= NQ;
  template <int N, int E>
  static constexpr bool kProductFits = posit<N, E>::Traits::MaxExp <= NQ/2;

  struct make_default_posit {
    static constexpr int N = C + 1;
    static constexpr int PowE = NQ / (2*(N - 2));
    static constexpr int E =
        PowE > 0 ? 31 - lzcnt(static_cast<uint32_t>(PowE)) : 0;
    // If exact, type::quire_type should be the same as this quire. Otherwise,
    // there was likely truncation in the calculations and this quire doesn't
    // exactly match any posit; the result type probably shouldn't be used for
    // conversions out, but is still a good choice for conversions in.
    static constexpr bool exact = NQ == (N - 2) * (1 << (E + 1)) && PowE > 0;
    using type = posit<N, E>;
  };

 public:
  using default_posit = typename make_default_posit::type;

  constexpr quire() noexcept = default;
  constexpr quire(const quire&) noexcept = default;
  template <int N, int E, enable_if_t<kPositFits<N, E>>* = nullptr>
  constexpr quire(posit<N, E> p) noexcept : quire() { *this += p; }
  template <int N, int E, enable_if_t<kProductFits<N, E>>* = nullptr>
  constexpr quire(posit_mult_intermediate<N, E> p) noexcept
      : quire() { *this += static_cast<posit_mult_intermediate<N, E>&&>(p); }
  // Non-template constructor for the default posit. This is provided specially
  // to allow implicit conversions from non-posit types to the default posit.
  constexpr quire(default_posit p) noexcept : quire() { *this += p; }

  constexpr void clear() noexcept { for (auto& entry : bits_) entry = 0; }
  constexpr quire& operator=(const quire&) noexcept = default;
  template <int N, int E>
  constexpr enable_if_t<kPositFits<N, E>, quire&> operator=(posit<N, E> p)
      noexcept {
    clear();
    return *this += p;
  }
  template <int N, int E>
  constexpr enable_if_t<kProductFits<N, E>, quire&> operator=(
      posit_mult_intermediate<N, E> p) noexcept {
    clear();
    return *this += static_cast<posit_mult_intermediate<N, E>&&>(p);
  }
  // Non-template assignment for the default posit. This is provided specially
  // to allow implicit conversions from non-posit types to the default posit.
  constexpr quire& operator=(default_posit p) noexcept {
    clear();
    return *this += p;
  }

  template <quire&..., bool ok = make_default_posit::exact>
  constexpr enable_if_t<ok, default_posit> to_posit() const noexcept {
    return to_posit<make_default_posit::N, make_default_posit::E>();
  }

  template <typename P,
            enable_if_t<make_default_posit::exact &&
                        std::is_same_v<default_posit, P>>* = nullptr>
  constexpr explicit operator P() const noexcept {
    return to_posit();
  }

  template <int N,
            // Only has a default value if N is a power of 2 between 8 and 128.
            int E = enable_if_t<
                8 <= N && N <= 128 && (N & (N - 1)) == 0,
                std::integral_constant<
                    int, tzcnt(static_cast<unsigned>(N))-3>>::value>
  constexpr posit<N, E> to_posit() const noexcept;

  constexpr quire operator-() const noexcept;

  template <int N, int E>
  constexpr enable_if_t<kPositFits<N, E>, quire&> operator+=(posit<N, E> p)
      noexcept;
  constexpr quire& operator+=(const quire& q) noexcept;
  template <int N, int E>
  constexpr enable_if_t<kProductFits<N, E>, quire&> operator+=(
      posit_mult_intermediate<N, E> p) noexcept;
  template <int N, int E>
  constexpr enable_if_t<kPositFits<N, E>, quire&> operator-=(posit<N, E> p)
      noexcept;
  constexpr quire& operator-=(const quire& q) noexcept;
  template <int N, int E>
  constexpr enable_if_t<kProductFits<N, E>, quire&> operator-=(
      posit_mult_intermediate<N, E> p) noexcept;
  // Non-template operators for the default posit. These are provided specially
  // to allow implicit conversions from non-posit types to the default posit.
  constexpr quire& operator+=(default_posit p) noexcept {
    return operator+= <make_default_posit::N, make_default_posit::E>(p);
  }
  constexpr quire& operator-=(default_posit p) noexcept {
    return operator-= <make_default_posit::N, make_default_posit::E>(p);
  }

  // Convenient way to sum multiple items into a new quire. This also may be
  // more efficient than repeatedly using +=.
  template <typename... T>
  static constexpr auto add_all(T&&... vals) noexcept
      // Note: Negation in the result type makes the result a non-reference.
      -> decltype(-(std::declval<quire>() += ... += vals)) {
    if constexpr (sizeof...(vals) == 0) return quire();
    if constexpr (sizeof...(vals) == 1) return quire(vals...);
    if constexpr ((... && std::is_same_v<
                              quire,
                              std::remove_cv_t<std::remove_reference_t<T>>>)) {
      quire q;
      if ((... || vals.IsNaR())) {
        q.MakeNaR();
      } else {
        SumRealQuiresIntoEmpty(q.bits_, vals.bits_...);
      }
      return q;
    } else {
      quire q;
      (q += ... += static_cast<T&&>(vals));
      return q;
    }
  }

 private:
  constexpr bool IsNaR() const noexcept {
    if (__builtin_expect(bits_[ArrayEntries - 1] != kHighBit, 1)) {
      return false;
    }
    for (int i = 0; i < ArrayEntries - 1; ++i) {
      if (bits_[i] != 0) return false;
    }
    return true;
  }

  constexpr void MakeNaR() noexcept {
    for (ArrayType& b : bits_) b = 0;
    bits_[ArrayEntries - 1] = kHighBit;
  }

  static constexpr void MakeMaxPos(ArrayType* bits) noexcept {
    // Overflowed positive; set to 0b0111...1.
    for (int i = 0; i < ArrayEntries - 1; ++i) bits[i] = ~ArrayType{0};
    bits[ArrayEntries - 1] = kHighBit - 1;
  }

  static constexpr void MakeMaxNeg(ArrayType* bits) noexcept {
    // Overflowed negative; set to 0b100...001.
    bits[0] = 1;
    for (int i = 1; i < ArrayEntries - 1; ++i) bits[i] = 0;
    bits[ArrayEntries - 1] = kHighBit;
  }

  template <typename UInt>
  constexpr void Add(int min_bit_pos, UInt significand) noexcept;
  template <typename UInt>
  constexpr void Sub(int min_bit_pos, UInt significand) noexcept;

  static constexpr void SumRealQuires(ArrayType* lhs,
                                      const ArrayType* rhs) noexcept;
  static constexpr void SumRealQuires(ArrayType* a, const ArrayType* b,
                                      const ArrayType* c) noexcept {
    SumRealQuires(a, b);
    SumRealQuires(a, c);
  }
  template <typename... Q>
  static constexpr void SumRealQuires(
      ArrayType* a, const ArrayType* b, const ArrayType* c, const ArrayType* d,
      const Q*... e) noexcept;
  // Like the above, but assumes dest is empty and simply copies the first in.
  template <typename... Q>
  static constexpr void SumRealQuiresIntoEmpty(
      ArrayType* dest, const ArrayType* a, const Q*... b) noexcept {
    memcpy(dest, a, sizeof(ArrayType) * ArrayEntries);
    SumRealQuires(dest, b...);
  }

  ArrayType bits_[ArrayEntries] = {0};
};
template <int NQ, int C>
quire(quire<NQ, C>) -> quire<NQ, C>;
template <int N, int E>
quire(posit<N, E>) -> quire<(N - 2) * (1 << (E + 1)), N - 1>;
template <int N, int E>
quire(posit_mult_intermediate<N, E>) -> quire<(N - 2) * (1 << (E + 1)), N - 1>;

// fused_add can be used to sum the result of two posit multiplications without
// intermediate rounding. This is more efficient than using a quire, but also
// more restrictive:
// - Performs only a single addition before rounding back to a posit.
// - If the two arguments have different posit types, one must be implicitly
//   convertible to the other. Quires are more lenient with allowed inputs.
// - The result is always rounded to the larger posit size. Quires allow
//   arbitrary output sizes to be requested.
//
// Examples:
//
//     result = a * b + c * d;            // Rounds 3 times.
//     result = fused_add(a * b, c * d);  // Rounds 1 time, at the end.
//     result = a * b + c;                // Rounds 2 times.
//     result = fused_add(a * b, c);      // Rounds 1 time, at the end.
template <int N1, int E1, int N2, int E2>
constexpr fused_add_result<N1, E1, N2, E2> fused_add(
    posit_mult_intermediate<N1, E1> lhs, posit_mult_intermediate<N2, E2> rhs)
    noexcept {
  if constexpr (N1 != N2 || E1 != E2) {
    if constexpr (std::is_convertible_v<posit<N1, E1>, posit<N2, E2>>) {
      return fused_add(
          posit_mult_intermediate<N2, E2>(
              static_cast<posit_mult_intermediate<N1, E1>&&>(lhs)),
          static_cast<posit_mult_intermediate<N2, E2>&&>(rhs));
    } else {
      return fused_add(
          static_cast<posit_mult_intermediate<N1, E1>&&>(lhs),
          posit_mult_intermediate<N1, E1>(
              static_cast<posit_mult_intermediate<N2, E2>&&>(rhs)));
    }
  } else {
    if (lhs.is_nar_ || rhs.is_nar_) return posit<N1, E1>::NaR();
    if (lhs.is_zero_) return rhs;
    if (rhs.is_zero_) return lhs;
    bool swap_order = false;
    if constexpr (PositTraits<N1, E1>::Storage::DoubleSizeAvailable) {
      swap_order = lhs.exponent_ < rhs.exponent_
                       || (lhs.exponent_ == rhs.exponent_
                           && lhs.significand_ < rhs.significand_);
    } else {
      swap_order =
          lhs.exponent_ < rhs.exponent_
              || (lhs.exponent_ == rhs.exponent_
                  && (lhs.significand_[1] < rhs.significand_[1]
                          || (lhs.significand_[1] == rhs.significand_[1]
                              && lhs.significand_[0] < rhs.significand_[0])));
    }
    if (!swap_order) {
      if (lhs.is_negative_ == rhs.is_negative_) {
        lhs.Add(static_cast<posit_mult_intermediate<N1, E1>&&>(rhs));
      } else {
        lhs.Sub(static_cast<posit_mult_intermediate<N1, E1>&&>(rhs));
      }
      return lhs;
    } else {
      if (lhs.is_negative_ == rhs.is_negative_) {
        rhs.Add(static_cast<posit_mult_intermediate<N1, E1>&&>(lhs));
      } else {
        rhs.Sub(static_cast<posit_mult_intermediate<N1, E1>&&>(lhs));
      }
      return rhs;
    }
  }
}
template <int N1, int E1, int N2, int E2>
constexpr fused_add_result<N1, E1, N2, E2> fused_add(
    posit<N1, E1> lhs, posit_mult_intermediate<N2, E2> rhs) noexcept {
  if constexpr (std::is_convertible_v<posit<N1, E1>, posit<N2, E2>>) {
    return fused_add(posit_mult_intermediate<N2, E2>(lhs),
                     static_cast<posit_mult_intermediate<N2, E2>&&>(rhs));
  } else {
    return fused_add(posit_mult_intermediate<N1, E1>(lhs),
                     posit_mult_intermediate<N1, E1>(
                         static_cast<posit_mult_intermediate<N2, E2>&&>(rhs)));
  }
}
template <int N1, int E1, int N2, int E2>
constexpr fused_add_result<N1, E1, N2, E2> fused_add(
    posit_mult_intermediate<N1, E1> lhs, posit<N2, E2> rhs) noexcept {
  // Just use the normal addition operator for two posits.
  if constexpr (std::is_convertible_v<posit<N1, E1>, posit<N2, E2>>) {
    return posit<N2, E2>(lhs) + rhs;
  } else {
    return lhs + posit<N2, E2>(rhs);
  }
}
template <int N1, int E1, int N2, int E2>
constexpr fused_add_result<N1, E1, N2, E2> fused_add(
    posit<N1, E1> lhs, posit<N2, E2> rhs) noexcept {
  if constexpr (std::is_convertible_v<posit<N1, E1>, posit<N2, E2>>) {
    return fused_add(posit_mult_intermediate<N2, E2>(lhs),
                     posit_mult_intermediate<N2, E2>(rhs));
  } else {
    return fused_add(posit_mult_intermediate<N1, E1>(lhs),
                     posit_mult_intermediate<N1, E1>(rhs));
  }
}

// For combination with other posit types or non-posit numeric types, use
// explicit conversions as needed. Implementing other overloads would make the
// rules around return types complicated.
template <int N, int E>
constexpr posit<N, E> nextafter(posit<N, E> from, posit<N, E> to) noexcept {
  if (from == posit<N, E>::NaR()) return from;
  if (to == posit<N, E>::NaR()) return to;
  if (from.bits_ == to.bits_) {
    return to;
  } else if (from.bits_ < to.bits_) {
    return posit<N, E>::WithBits(from.bits_ + 1);
  } else {
    return posit<N, E>::WithBits(from.bits_ - 1);
  }
}

template <int N, int E>
constexpr posit<N, E> nexttoward(posit<N, E> from, long double to) noexcept {
  using pos = posit<N, E>;
  if (to == 0.0L) {
    return nextafter(from, pos::Zero());
  }
  if (from == pos::NaR() || isnan(to)) {
    return pos::NaR();
  }
  if (isinf(to)) {
    return nextafter(from, to > 0.0L ? pos::Max() : -pos::Max());
  }
  if (from == pos::Zero()) {
    return to > 0.0L ? pos::Min() : -pos::Min();
  }
  if ((from > pos::Zero()) != (to > 0.0L)) {
    return nextafter(from, pos::Zero());
  }
  if (to < 0.0L) {
    to = -to;
  }
  decoded_posit<pos::Traits::SBits> to_dec{};
  // Returns with to in [0.5, 1), meaning exponent is 1 too high.
  to = frexpl(to, &to_dec.exponent);
  --to_dec.exponent;
  if (to_dec.exponent >= pos::Traits::MaxExp) {
    return nextafter(from, from >= pos::Zero() ? pos::Max() : -pos::Max());
  }
  if (to_dec.exponent < pos::Traits::MinExp) {
    return nextafter(from, pos::Zero());
  }
  // This gives SBits of precision, which is always more than the posit has.
  to = (to - 0.5L) * exp2l(1 + pos::Traits::SBits);
  long double truncated = truncl(to);
  to_dec.fraction = static_cast<typename pos::Traits::Unsigned>(truncated);
  // Avoid comparing equal when `to` is larger in magnitude by <1 ULP.
  if (to > truncated) to_dec.fraction |= 1;
  decoded_posit from_dec = decode_posit<N, E>(from.bits_);
  if (from_dec.exponent > to_dec.exponent ||
      (from_dec.exponent == to_dec.exponent &&
       from_dec.fraction > to_dec.fraction)) {
    return nextafter(from, pos::Zero());
  } else if (from_dec.exponent == to_dec.exponent &&
             from_dec.fraction == to_dec.fraction) {
    return from;
  } else if (from > pos::Zero()) {
    return nextafter(from, pos::Max());
  } else {
    return nextafter(from, -pos::Max());
  }
}

template <int N1, int E1, int N2, int E2>
constexpr posit<N1, E1> nexttoward(posit<N1, E1> from,
                                   posit<N2, E2> to) noexcept {
  using p1 = posit<N1, E1>;
  using p2 = posit<N2, E2>;
  if (from == p1::NaR() || to == p2::NaR()) {
    return p1::NaR();
  }
  if constexpr (std::is_convertible_v<p1, p2>) {
    p2 converted = from;
    if (converted.bits_ == to.bits_) {
      return from;
    } else if (converted.bits_ < to.bits_) {
      if (from == p1::Max()) return from;
      return p1::WithBits(from.bits_ + 1);
    } else {
      if (from == -p1::Max()) return from;
      return p1::WithBits(from.bits_ - 1);
    }
  } else if constexpr (std::is_convertible_v<p2, p1>) {
    return nextafter(from, p1(to));
  } else {
    if (to == p2::Zero()) {
      return nextafter(from, p1::Zero());
    }
    if (from == p1::Zero()) {
      return to > p2::Zero() ? p1::Min() : -p1::Min();
    }
    if ((from > p1::Zero()) != (to > p2::Zero())) {
      // Neither is zero and signs differ, so move toward zero.
      return nextafter(from, p1::Zero());
    }
    decoded_posit to_dec = decode_posit<N2, E2>(to.bits_);
    if (to_dec.exponent >= p1::Traits::MaxExp) {
      return nextafter(from, to_dec.sign >= 0 ? p1::Max() : -p1::Max());
    }
    if (to_dec.exponent < p1::Traits::MinExp) {
      return nextafter(from, p1::Zero());
    }
    decoded_posit from_dec = decode_posit<N1, E1>(from.bits_);
    // Signs must be the same, differing signs were handled before decoding.
    using BiggerUnsigned =
        typename cond<p1::Traits::SBits < p2::Traits::SBits>
            ::template then<typename p2::Traits::Unsigned>
            ::template otherwise<typename p1::Traits::Unsigned>;
    BiggerUnsigned from_frac = from_dec.fraction;
    BiggerUnsigned to_frac = to_dec.fraction;
    if constexpr (p1::Traits::SBits < p2::Traits::SBits) {
      from_frac <<= p2::Traits::SBits - p1::Traits::SBits;
    } else {
      to_frac <<= p1::Traits::SBits - p2::Traits::SBits;
    }
    if (from_dec.exponent > to_dec.exponent ||
        (from_dec.exponent == to_dec.exponent && from_frac > to_frac)) {
      return nextafter(from, p1::Zero());
    } else if (from_dec.exponent == to_dec.exponent && from_frac == to_frac) {
      return from;
    } else if (from > p1::Zero()) {
      return nextafter(from, p1::Max());
    } else {
      return nextafter(from, -p1::Max());
    }
  }
}

/**** Implementation details below ****/

template <int N, int E>
template <int N2, int E2>
constexpr typename posit<N, E>::Traits::Signed posit<N, E>::ReencodePosit(
    posit<N2, E2> p) noexcept {
  using PT2 = PositTraits<N2, E2>;
  using U = typename Traits::Unsigned;
  using U2 = typename PT2::Unsigned;
  if constexpr (E == E2) {
    // The encoding for two posits with the same number of exponent bits only
    // differs in the number of fraction bits, so this is simply a shift and
    // possibly a round.
    if constexpr (Traits::SBits >= PT2::SBits) {
      return static_cast<U>(p.bits_) << (Traits::SBits - PT2::SBits);
    } else {
      constexpr U2 cut_point = U2{1} << (PT2::SBits - Traits::SBits);
      U bits = static_cast<U2>(p.bits_) >> (PT2::SBits - Traits::SBits);
      bool negative = (bits & Traits::kHighBit) != 0;
      U2 dropped =
          static_cast<U2>(negative ? -p.bits : p.bits_) & (cut_point - 1);
      if (dropped >= cut_point / 2 && (dropped > cut_point / 2 ||
                                       (bits & 1) != 0)) {
        if (bits != (negative ? -Traits::kMax : Traits::kMax)) ++bits;
      }
      if (__builtin_expect(bits == Traits::kNaR && p.bits_ != PT2::kNaR, 0)) {
        ++bits;
      }
      return bits;
    }
  } else {
    if (p.bits_ == PT2::kZero) return Traits::kZero;
    if (p.bits_ == PT2::kNaR) return Traits::kNaR;
    decoded_posit<PT2::SBits> dec2 = decode_posit<N2, E2>(p.bits_);
    decoded_posit<Traits::SBits> dec{};
    dec.sign = dec2.sign;
    dec.exponent = dec2.exponent;
    if constexpr (Traits::SBits >= PT2::SBits) {
      dec.fraction =
          static_cast<U>(dec2.fraction) << (Traits::SBits - PT2::SBits);
    } else {
      constexpr U2 cut_point = U2{1} << (PT2::SBits - Traits::SBits);
      dec.fraction =
          static_cast<U>(dec2.fraction >> (PT2::SBits - Traits::SBits))
              | ((dec2.fraction & (cut_point - 1)) != 0);
    }
    return encode_regular_posit<N, E>(dec);
  }
}

template <int S>
template <typename F>
constexpr typename PositByStorage<S>::FromFloatPrecheckResult
PositByStorage<S>::FromFloatPrecheck(F floatval) noexcept {
  if (floatval == F{0}) {
    return {kZero, true};
  }
  if (isnan(floatval) || isinf(floatval)) {
    return {kNaR, true};
  }
  return {kNaR, false};
}

template <int S>
template <typename F>
constexpr decoded_posit<S> PositByStorage<S>::FromFloat(F floatval) noexcept {
  decoded_posit<SBits> dec{};
  if constexpr (std::is_same_v<double, F> &&
                std::numeric_limits<F>::is_iec559 &&
                sizeof(double) == sizeof(uint64_t)) {
    uint64_t dbl_bits = 0;
    memcpy(&dbl_bits, &floatval, sizeof(double));
    dec.sign = (dbl_bits & (uint64_t{1} << 63)) ? -1 : 1;
    dec.exponent = static_cast<int>((dbl_bits >> 52) & 0x7FF) - 1023;
    uint64_t fraction = dbl_bits & 0xFFFFFFFFFFFFFU;
    if constexpr (SBits >= 52) {
      dec.fraction = static_cast<Unsigned>(fraction) << (SBits - 52);
    } else {
      dec.fraction = fraction >> (52 - SBits);
      dec.fraction |= (fraction & ((uint64_t{1} << (52 - SBits)) - 1)) != 0;
    }
  } else if constexpr (std::is_same_v<float, F> &&
                       std::numeric_limits<F>::is_iec559 &&
                       sizeof(float) == sizeof(uint32_t)) {
    uint32_t flt_bits = 0;
    memcpy(&flt_bits, &floatval, sizeof(float));
    dec.sign = (flt_bits & (uint32_t{1} << 31)) ? -1 : 1;
    dec.exponent = static_cast<int>((flt_bits >> 23) & 0xFF) - 127;
    uint32_t fraction = flt_bits & 0x7FFFFFU;
    if constexpr (SBits >= 23) {
      dec.fraction = static_cast<Unsigned>(fraction) << (SBits - 23);
    } else {
      dec.fraction = fraction >> (23 - SBits);
      dec.fraction |= (fraction & ((uint32_t{1} << (23 - SBits)) - 1)) != 0;
    } 
  } else {
    if (floatval >= F{0}) {
      dec.sign = 1;
    } else {
      dec.sign = -1;
      floatval = -floatval;
    }
    // Returns a value in [0.5, 1), meaning exponent is 1 too high.
    floatval = frexp(floatval, &dec.exponent);
    --dec.exponent;
    // This gives SBits of precision left of the binary point, more than enough
    // for any posit stored in SBits.
    floatval = (floatval - F{0.5}) * exp2(1 + SBits);
    F truncated = trunc(floatval);
    dec.fraction = static_cast<Unsigned>(truncated);
    // Ensure proper rounding if floatval is between posit values.
    if (floatval > truncated) dec.fraction |= 1;
  }
  return dec;
}

template <int S>
template <typename F>
constexpr F PositByStorage<S>::ToFloat(decoded_posit<SBits> dec) noexcept {
  if constexpr (std::is_same_v<double, F> &&
                std::numeric_limits<F>::is_iec559 &&
                sizeof(double) == sizeof(uint64_t)) {
    uint64_t dbl_bits = 0;
    if (dec.sign < 0) dbl_bits |= uint64_t{1} << 63;
    if constexpr (SBits <= 52) {
      dbl_bits |= static_cast<uint64_t>(dec.fraction) << (52 - SBits);
    } else {
      uint64_t frac = static_cast<uint64_t>(dec.fraction >> (SBits - 52));
      Unsigned cut_bit = Unsigned{1} << (SBits - 52);
      dec.fraction &= cut_bit - 1;
      if (dec.fraction >= cut_bit / 2 &&
          (dec.fraction > cut_bit / 2 || (frac & 1) == 1)) {
        ++frac;
        if (frac == uint64_t{1} << 52) {
          frac = 0;
          ++dec.exponent;
        }
      }
      dbl_bits |= frac;
    }
    if (dec.exponent > 1023) {
      return dec.sign >= 0 ? HUGE_VAL : -HUGE_VAL;
    }
    if (dec.exponent < -1022) {
      // Return the smallest normalized double.
      double min = std::numeric_limits<double>::min();
      return dec.sign >= 0 ? min : -min;
    }
    dbl_bits |= static_cast<uint64_t>(dec.exponent + 1023) << 52;
    double dbl = 0.0;
    memcpy(&dbl, &dbl_bits, sizeof(double));
    return dbl;
  } else if constexpr (std::is_same_v<float, F> &&
                       std::numeric_limits<F>::is_iec559 &&
                       sizeof(float) == sizeof(uint32_t)) {
    uint32_t flt_bits = 0;
    if (dec.sign < 0) flt_bits |= uint32_t{1} << 31;
    if constexpr (SBits <= 23) {
      flt_bits |= static_cast<uint32_t>(dec.fraction) << (23 - SBits);
    } else {
      uint32_t frac = static_cast<uint32_t>(dec.fraction >> (SBits - 23));
      Unsigned cut_bit = Unsigned{1} << (SBits - 23);
      dec.fraction &= cut_bit - 1;
      if (dec.fraction >= cut_bit / 2 &&
          (dec.fraction > cut_bit / 2 || (frac & 1) == 1)) {
        ++frac;
        if (frac == uint32_t{1} << 23) {
          frac = 0;
          ++dec.exponent;
        }
      }
      flt_bits |= frac;
    }
    if (dec.exponent > 127) {
      return dec.sign >= 0 ? HUGE_VALF : -HUGE_VALF;
    }
    if (dec.exponent < -126) {
      // Return the smallest normalized float.
      float min = std::numeric_limits<float>::min();
      return dec.sign >= 0 ? min : -min;
    }
    flt_bits |= static_cast<uint32_t>(dec.exponent + 127) << 23;
    float flt = 0.0F;
    memcpy(&flt, &flt_bits, sizeof(float));
    return flt;
  } else {
    dec.fraction = (dec.fraction >> 1) | Traits::kHighBit;
    F flt = static_cast<F>(dec.fraction) *
            exp2(static_cast<F>(dec.exponent - (SBits - 1)));
    return dec.sign >= 0 ? flt : -flt;
  }
}

template <int S>
template <typename I>
constexpr decoded_posit<S> PositByStorage<S>::FromInt(I intval) noexcept {
  using U = std::make_unsigned_t<I>;
  constexpr int UBits = std::numeric_limits<U>::digits;

  decoded_posit<SBits> dec{};
  U absval = 0;
  if (intval >= 0) {
    absval = intval;
    dec.sign = 1;
  } else {
    absval = -intval;
    dec.sign = -1;
  }
  int lz = lzcnt(absval);
  absval <<= (lz + 1);
  dec.exponent = UBits - (lz + 1);
  if constexpr (UBits > SBits) {
    dec.fraction = absval >> (UBits - SBits);
    if (absval & ((U{1} << (UBits - SBits)) - 1)) {
      dec.fraction |= 1;
    }
  } else {
    dec.fraction = static_cast<Unsigned>(absval) << (SBits - UBits);
  }
  return dec;
}

template <int S>
template <typename I>
constexpr I PositByStorage<S>::ToInt(decoded_posit<SBits> dec) noexcept {
  using U = std::make_unsigned_t<I>;
  constexpr int UBits = std::numeric_limits<U>::digits;

  if (dec.exponent - SBits >= UBits) return 0;
  if (dec.exponent < 0) return 0;

  U absval = 0;
  if (dec.exponent < UBits) {
    absval |= U{1} << dec.exponent;
  }
  if (dec.exponent > 0) {
    if (dec.exponent <= SBits) {
      absval |= static_cast<U>(dec.fraction >> (SBits - dec.exponent));
    } else {
      absval |= static_cast<U>(dec.fraction) << (dec.exponent - SBits);
    }
  }
  if (dec.sign < 0) {
    absval = -absval;
  }
  return static_cast<I>(absval);
}

template <int NQ, int C>
template <typename... Q>
constexpr void quire<NQ, C>::SumRealQuires(
    ArrayType* a, const ArrayType* b, const ArrayType* c, const ArrayType* d,
    const Q*... e) noexcept {
  using v4u32 __attribute__((__vector_size__(16))) = uint32_t;
  using v4u64 __attribute__((__vector_size__(32))) = uint64_t;
  constexpr int kNumVecs = (NBits + 127) / 128;
  constexpr int kSignEntry = (NBits % 128) == 0 ? 3
                                 : (NBits % 128) < 32 ? 0
                                 : (NBits % 128) < 64 ? 1
                                 : (NBits % 128) < 92 ? 2
                                 : 3;

  constexpr uint32_t kSign = uint32_t{1} << 31;
  // Avoid carries ever having the high bit set, for overflow detection.
  static_assert(sizeof...(e) + 4 < kSign,
                "Adding too many items at once.");

  constexpr auto load = [](const ArrayType* arr, auto handler) {
    if constexpr (ArrayEntryBits == 32) {
      for (int i = 0; i < kNumVecs - 1; ++i) {
        handler(i,
                __builtin_convertvector(
                    (v4u32){arr[4*i+0], arr[4*i+1], arr[4*i+2], arr[4*i+3]},
                    v4u64));
      }
      handler(kNumVecs - 1,
              __builtin_convertvector(
                  (v4u32){
                      arr[4*kNumVecs-4],
                      kSignEntry >= 1 ? arr[4*kNumVecs-3] : 0,
                      kSignEntry >= 2 ? arr[4*kNumVecs-2] : 0,
                      kSignEntry >= 3 ? arr[4*kNumVecs-1] : 0,
                  },
                  v4u64));
    } else {
      static_assert(ArrayEntryBits == 64, "Unimplemented quire backing type");
      for (int i = 0; i < kNumVecs - 1; ++i) {
        handler(i, __builtin_convertvector(
                       (v4u32){
                           static_cast<uint32_t>(arr[2*i+0]),
                           static_cast<uint32_t>(arr[2*i+0] >> 32),
                           static_cast<uint32_t>(arr[2*i+1]),
                           static_cast<uint32_t>(arr[2*i+1] >> 32),
                       },
                       v4u64));
      }
      handler(kNumVecs - 1,
              __builtin_convertvector(
                  (v4u32){
                      static_cast<uint32_t>(arr[2*kNumVecs-2]),
                      kSignEntry >= 1
                          ? static_cast<uint32_t>(arr[2*kNumVecs-2] >> 32)
                          : 0,
                      kSignEntry >= 2
                          ? static_cast<uint32_t>(arr[2*kNumVecs-1])
                          : 0,
                      kSignEntry >= 3
                          ? static_cast<uint32_t>(arr[2*kNumVecs-1] >> 32)
                          : 0,
                  },
                  v4u64));
    }
  };
  constexpr auto sum = [load](v4u64* d, const ArrayType* s) {
    load(s, [d](int i, v4u64 x) { d[i] += x; });
  };

  v4u64 va[kNumVecs], vb[kNumVecs];
  load(a, [&va](int i, v4u64 x) { va[i] = x; });
  uint32_t a_sign = (a[ArrayEntries - 1] & kHighBit) ? kSign : 0;
  sum(va, c);
  uint32_t a_sign_new = va[kNumVecs-1][kSignEntry] & kSign;
  if (uint32_t c_sign = (c[ArrayEntries - 1] & kHighBit) ? kSign : 0;
      __builtin_expect(a_sign == c_sign && a_sign != a_sign_new, 0)) {
    if (c_sign) MakeMaxNeg(a);
    else MakeMaxPos(a);
    return;
  }
  a_sign = a_sign_new;

  load(b, [&vb](int i, v4u64 x) { vb[i] = x; });
  uint32_t b_sign = (b[ArrayEntries - 1] & kHighBit) ? kSign : 0;
  sum(vb, d);
  uint32_t b_sign_new = vb[kNumVecs-1][kSignEntry] & kSign;
  if (uint32_t d_sign = (d[ArrayEntries - 1] & kHighBit) ? kSign : 0;
      __builtin_expect(b_sign == d_sign && b_sign != b_sign_new, 0)) {
    if (b_sign) MakeMaxNeg(a);
    else MakeMaxPos(a);
    return;
  }
  b_sign = b_sign_new;

  if constexpr (sizeof...(e) > 0) {
    const ArrayType* prev = nullptr;
    for (const ArrayType* curr : {e...}) {
      if (!prev) {
        prev = curr;
        continue;
      }

      sum(va, prev);
      sum(vb, curr);

      a_sign_new = va[kNumVecs-1][kSignEntry] & kSign;
      b_sign_new = vb[kNumVecs-1][kSignEntry] & kSign;
      if (uint32_t prev_sign = (prev[ArrayEntries-1] & kHighBit) ? kSign : 0;
          __builtin_expect(a_sign == prev_sign && a_sign != a_sign_new, 0)) {
        if (a_sign) MakeMaxNeg(a);
        else MakeMaxPos(a);
        return;
      }
      if (uint32_t curr_sign = (curr[ArrayEntries-1] & kHighBit) ? kSign : 0;
          __builtin_expect(b_sign == curr_sign && b_sign != b_sign_new, 0)) {
        if (b_sign) MakeMaxNeg(a);
        else MakeMaxPos(a);
        return;
      }
      a_sign = a_sign_new;
      b_sign = b_sign_new;

      prev = nullptr;
    }
    if (prev) {
      sum(va, prev);
      a_sign_new = va[kNumVecs-1][kSignEntry] & kSign;
      if (uint32_t prev_sign = (prev[ArrayEntries-1] & kHighBit) ? kSign : 0;
          __builtin_expect(a_sign == prev_sign && a_sign != a_sign_new, 0)) {
        if (a_sign) MakeMaxNeg(a);
        else MakeMaxPos(a);
        return;
      }
      a_sign = a_sign_new;
    }
  }

  for (int i = 0; i < kNumVecs; ++i) {
    va[i] += vb[i];
  }
  a_sign_new = va[kNumVecs-1][kSignEntry] & kSign;
  if (__builtin_expect(a_sign == b_sign && a_sign != a_sign_new, 0)) {
    if (a_sign) MakeMaxNeg(a);
    else MakeMaxPos(a);
    return;
  }
  a_sign = a_sign_new;

  v4u32 vcarry[kNumVecs], res[kNumVecs];
  for (int i = 0; i < kNumVecs; ++i) {
    vcarry[i] = __builtin_convertvector(va[i] >> 32, v4u32);
    res[i] = __builtin_convertvector(va[i] & uint64_t{0xFFFFFFFFU}, v4u32);
  }

  uint32_t carry = 0;
  if constexpr (ArrayEntryBits == 32) {
    for (int i = 0; i < kNumVecs - 1; ++i) {
      a[4*i+0] = builtin_addc(res[i][0],
                              i == 0 ? 0 : vcarry[i-1][3],
                              i == 0 ? 0 : carry,
                              &carry);
      a[4*i+1] = builtin_addc(res[i][1],
                              vcarry[i][0],
                              i == 0 ? 0 : carry,
                              &carry);
      a[4*i+2] = builtin_addc(res[i][2], vcarry[i][1], carry, &carry);
      a[4*i+3] = builtin_addc(res[i][3], vcarry[i][2], carry, &carry);
    }
    a[4*kNumVecs-4] = builtin_addc(res[kNumVecs-1][0],
                                   kNumVecs == 1 ? 0 : vcarry[kNumVecs-2][3],
                                   kNumVecs == 1 ? 0 : carry,
                                   &carry);
    if constexpr (kSignEntry >= 1) {
      a[4*kNumVecs-3] = builtin_addc(res[kNumVecs-1][1],
                                     vcarry[kNumVecs-1][0],
                                     kNumVecs == 1 ? 0 : carry,
                                     &carry);
    }
    if constexpr (kSignEntry >= 2) {
      a[4*kNumVecs-2] = builtin_addc(
          res[kNumVecs-1][2], vcarry[kNumVecs-1][1], carry, &carry);
    }
    if constexpr (kSignEntry >= 3) {
      a[4*kNumVecs-1] = builtin_addc(
          res[kNumVecs-1][3], vcarry[kNumVecs-1][2], carry, &carry);
    }
  } else {
    static_assert(ArrayEntryBits == 64, "Unimplemented quire backing type.");
    for (int i = 0; i < kNumVecs - 1; ++i) {
      a[2*i+0] = builtin_addc(res[i][0],
                              i == 0 ? 0 : vcarry[i-1][3],
                              i == 0 ? 0 : carry,
                              &carry);
      a[2*i+0] |= static_cast<uint64_t>(builtin_addc(res[i][1],
                                                     vcarry[i][0],
                                                     i == 0 ? 0 : carry,
                                                     &carry)) << 32;
      a[2*i+1] = builtin_addc(res[i][2], vcarry[i][1], carry, &carry);
      a[2*i+1] |= static_cast<uint64_t>(
                      builtin_addc(res[i][3], vcarry[i][2], carry, &carry))
                  << 32;
    }
    a[2*kNumVecs-2] = builtin_addc(res[kNumVecs-1][0],
                                   kNumVecs == 1 ? 0 : vcarry[kNumVecs-2][3],
                                   kNumVecs == 1 ? 0 : carry,
                                   &carry);
    if constexpr (kSignEntry >= 1) {
      a[2*kNumVecs-2] |= static_cast<uint64_t>(
                             builtin_addc(res[kNumVecs-1][1],
                                          vcarry[kNumVecs-1][0],
                                          kNumVecs == 1 ? 0 : carry,
                                          &carry))
                         << 32;
    } else {
      if (a[2*kNumVecs-2] & kSign) {
        a[2*kNumVecs-2] |= uint64_t{0xFFFFFFFFU} << 32;
      }
    }
    if constexpr (kSignEntry >= 2) {
      a[2*kNumVecs-1] = builtin_addc(
          res[kNumVecs-1][2], vcarry[kNumVecs-1][1], carry, &carry);
    }
    if constexpr (kSignEntry >= 3) {
      a[2*kNumVecs-1] |= static_cast<uint64_t>(
                             builtin_addc(res[kNumVecs-1][3],
                                          vcarry[kNumVecs-1][2],
                                          carry,
                                          &carry))
                         << 32;
    } else if constexpr (kSignEntry >= 2) {
      if (a[2*kNumVecs-1] & kSign) {
        a[2*kNumVecs-2] |= uint64_t{0xFFFFFFFFU} << 32;
      }
    }
  }
  if (__builtin_expect(!a_sign && (a[ArrayEntries-1] & kHighBit), 0)) {
    MakeMaxPos(a);
  }
}

template <int S>
struct PositByStorage<S>::mult_intermediate {
 protected:
  using Traits = PositByStorage::Traits;

  friend constexpr mult_intermediate PositByStorage::Multiply(
      decoded_posit<S> l_dec, decoded_posit<S> r_dec) noexcept;

  constexpr decoded_posit<SBits> MakeDecoded() const && noexcept {
    decoded_posit<SBits> dec{};
    dec.sign = is_negative_ ? -1 : 1;
    dec.exponent = exponent_;
    if constexpr (Traits::DoubleSizeAvailable) {
      decltype(significand_) frac = significand_ << 1;
      dec.fraction = frac >> SBits;
      if (frac & ~typename Traits::Unsigned{0}) dec.fraction |= 1;
    } else {
      dec.fraction =
          (significand_[1] << 1) | (significand_[0] >> (SBits - 1));
      if (significand_[0] << 1) dec.fraction |= 1;
    }
    return dec;
  }

  constexpr mult_intermediate() noexcept = default;
  constexpr mult_intermediate(mult_intermediate&&) noexcept = default;
  mult_intermediate& operator=(mult_intermediate&&) = delete;

  static constexpr mult_intermediate Zero() noexcept {
    mult_intermediate r;
    r.is_negative_ = false;
    r.is_zero_ = true;
    r.is_nar_ = false;
    r.exponent_ = 0;
    if constexpr (Traits::DoubleSizeAvailable) {
      r.significand_ = 0;
    } else {
      r.significand_[0] = 0;
      r.significand_[1] = 0;
    }
    return r;
  }

  static constexpr mult_intermediate NaR() noexcept {
    mult_intermediate r;
    r.is_negative_ = false;
    r.is_zero_ = false;
    r.is_nar_ = true;
    r.exponent_ = 0;
    if constexpr (Traits::DoubleSizeAvailable) {
      r.significand_ = 0;
    } else {
      r.significand_[0] = 0;
      r.significand_[1] = 0;
    }
    return r;
  }

  static constexpr mult_intermediate Finite(
      bool negative, int exponent,
      PositDoubleUnsigned<Traits::SBits, true> significand) noexcept {
    mult_intermediate r;
    r.is_negative_ = negative;
    r.is_zero_ = false;
    r.is_nar_ = false;
    r.exponent_ = exponent;
    if constexpr (Traits::DoubleSizeAvailable) {
      r.significand_ = significand;
    } else {
      r.significand_[0] = significand[0];
      r.significand_[1] = significand[1];
    }
    return r;
  }

  constexpr void FillFromDecoded(decoded_posit<Traits::SBits> dec) noexcept {
    is_negative_ = dec.sign < 0;
    is_zero_ = false;
    is_nar_ = false;
    exponent_ = dec.exponent;
    if constexpr (Traits::DoubleSizeAvailable) {
      significand_ =
          (static_cast<PositDoubleUnsigned<Traits::SBits>>(dec.fraction)
               << (Traits::SBits - 1))
          | (PositDoubleUnsigned<Traits::SBits>{1} << (2 * Traits::SBits - 1));
    } else {
      significand_[0] = 0;  // The fraction can't take all of the bits.
      significand_[1] = (dec.fraction >> 1) | Traits::kHighBit;
    }
  }

  // Adds the other intermediate into this. This may be significantly rounded
  // afterwards, near the size of a posit. The sign of p is assumed to match
  // this.
  // Requires: Neither this nor p may be NaR or zero, and the exponent of this
  // must be greater or equal to the exponent of p.
  constexpr void Add(mult_intermediate&& p) noexcept {
    if constexpr (Traits::DoubleSizeAvailable) {
      // Use the addition implementation for a doubly-large posit.
      decoded_posit<Traits::SBits * 2> dec{};
      dec.sign = is_negative_ ? -1 : 1;
      dec.exponent = exponent_;
      dec.fraction = significand_ << 1;
      dec = PositByStorage<Traits::SBits * 2>::Add(
          dec, p.exponent_, p.significand_ << 1);
      is_negative_ = dec.sign < 0;
      exponent_ = dec.exponent;
      significand_ =
          (dec.fraction >> 1)
              | PositStorageTraits<Traits::SBits * 2>::kHighBit
              | (dec.fraction & 1);
    } else {
      using U = typename Traits::Unsigned;
      U add_low = 0, add_high = 0;
      bool dropped = false;
      if (exponent_ > p.exponent_) {
        int shift = exponent_ - p.exponent_;
        if (shift >= Traits::SBits * 2) {
          // The significand of p is entirely shifted off. At least the high
          // bit must have been set.
          dropped = true;
        } else if (shift >= Traits::SBits) {
          // The significand of p is shifted into the low entry.
          U drop_mask = (U{1} << (shift - Traits::SBits)) - 1;
          dropped =
              p.significand_[0] != 0 || (p.significand_[1] & drop_mask) != 0;
          add_low = p.significand_[1] >> (shift - Traits::SBits);
        } else {
          U drop_mask = (U{1} << shift) - 1;
          dropped = (p.significand_[0] & drop_mask) != 0;
          add_low = p.significand_[0] >> shift;
          add_low |=
              (p.significand_[1] & drop_mask) << (Traits::SBits - shift);
          add_high = p.significand_[1] >> shift;
        }
      } else {
        add_low = significand_[0];
        add_high = significand_[1];
      }
      U carry = 0;
      significand_[0] = builtin_addc(significand_[0], add_low, 0, &carry);
      significand_[1] = builtin_addc(significand_[1], add_high, carry, &carry);
      if (carry) {
        // Carried through the top bit. Shift in and set an extra bit, and
        // increment the exponent.
        U shifted_out = (significand_[1] & 1) << (Traits::SBits - 1);
        significand_[1] = (significand_[1] >> 1) | Traits::kHighBit;
        dropped = (significand_[0] & 1) != 0 || dropped;
        significand_[0] = (significand_[0] >> 1) | shifted_out;
        ++exponent_;
      }
      if (dropped) {
        // Set the low bit if any dropped bits were set, to ensure proper
        // rounding.
        significand_[0] |= 1;
      }
    }
  }

  // Subtracts the other intermediate from this. This may be significantly
  // rounded afterwards, near the size of a posit. The sign of p is assumed to
  // match this.
  // Requires: Neither this nor p may be NaR or zero, this must be greater than
  // or equal to p (i.e. this has a greater exponent, or equal exponent and
  // greater or equal significand).
  constexpr void Sub(mult_intermediate&& p) noexcept {
    if constexpr (Traits::DoubleSizeAvailable) {
      // Use the subtraction implementation for a doubly-large posit.
      decoded_posit<Traits::SBits * 2> dec{};
      dec.sign = is_negative_ ? -1 : 1;
      dec.exponent = exponent_;
      dec.fraction = significand_ << 1;
      dec = PositByStorage<Traits::SBits * 2>::Subtract(
          dec, p.exponent_, p.significand_ << 1);
      is_negative_ = dec.sign < 0;
      exponent_ = dec.exponent;
      significand_ =
          (dec.fraction >> 1)
              | PositStorageTraits<Traits::SBits * 2>::kHighBit
              | (dec.fraction & 1);
    } else {
      using U = typename Traits::Unsigned;
      bool dropped = false;
      U sub_low = 0, sub_high = 0;
      if (exponent_ > p.exponent_) {
        int shift = exponent_ - p.exponent_;
        if (shift >= 2 * Traits::SBits) {
          // The significand of p is entirely shifted off.
          dropped = true;
        } else if (shift >= Traits::SBits) {
          // The significand of p is shifted into the low entry.
          U drop_mask = (U{1} << (shift - Traits::SBits)) - 1;
          dropped =
              p.significand_[0] != 0 || (p.significand_[1] & drop_mask) != 0;
          sub_low = (p.significand_[1] >> (shift - Traits::SBits));
        } else {
          U drop_mask = (U{1} << shift) - 1;
          dropped = (p.significand_[0] & drop_mask) != 0;
          sub_low = p.significand_[0] >> shift;
          sub_low |=
              (p.significand_[1] & drop_mask) << (Traits::SBits - shift);
          sub_high = p.significand_[1] >> shift;
        }
      } else {
        sub_low = p.significand_[0];
        sub_high = p.significand_[1];
      }
      U carry = 0;
      significand_[0] =
          builtin_subc(significand_[0], sub_low, U{dropped}, &carry);
      significand_[1] = builtin_subc(significand_[1], sub_high, carry, &carry);
      if ((significand_[1] & Traits::kHighBit) == 0) {
        // Borrowed from the high bit. Shift out however many bits until the
        // next set bit, and update the exponent.
        // Note: If the exponent difference >= 2, then the borrow must have
        // left the next bit set; only one bit will be shifted and so none of
        // the dropped bits would make it into the encoded result. Otherwise,
        // for a small exponent offset, none of the fraction bits that get
        // shifted off could have been set. In either case, the existing
        // fraction precision is sufficient even with a large change in
        // exponent/regime.
        if (significand_[1] != 0) {
          int shift = lzcnt(significand_[1]);
          U shifted = significand_[0] >> (Traits::SBits - shift);
          significand_[0] <<= shift;
          significand_[1] = (significand_[1] << shift) | shifted;
          exponent_ -= shift;
        } else if (significand_[0] == 0) {
          is_zero_ = true;
        } else {
          int shift = lzcnt(significand_[0]);
          significand_[1] = significand_[0] << shift;
          significand_[0] = 0;
          exponent_ -= shift + Traits::SBits;
        }
      }
      if (dropped) {
        significand_[0] |= 1;
      }
    }
  }

  template <int N, int E>
  friend constexpr posit_mult_intermediate<N, E> adjust_mult_exponent(
      posit_mult_intermediate<N, E> p, int adjust) noexcept;

  bool is_negative_ = false;
  bool is_zero_ = false;
  bool is_nar_ = false;
  int exponent_ = false;  // Includes regime.
  // Fixed point 1.N, where N is SBits*2-1, high bit must be 1. If this is an
  // array type, the low bits go in index 0 and high bits in index 1.
  PositDoubleUnsigned<Traits::SBits, true> significand_ = {0};
};

template <int N, int E>
class posit_mult_intermediate :
    private PositByStorage<PositTraits<N, E>::SBits>::mult_intermediate {
 private:
  using Base =
      typename PositByStorage<PositTraits<N, E>::SBits>::mult_intermediate;

 public:
  constexpr operator posit<N, E>() const noexcept {
    if (this->is_zero_) return posit<N, E>::Zero();
    if (this->is_nar_) return posit<N, E>::NaR();
    return posit<N, E>::WithBits(encode_regular_posit<N, E>(
               static_cast<const posit_mult_intermediate&&>(*this)
                   .MakeDecoded()));
  }

  constexpr posit_mult_intermediate operator-() const && noexcept {
    posit_mult_intermediate r;
    r.is_negative_ = !this->is_negative_;
    r.is_zero_ = this->is_zero_;
    r.is_nar_ = this->is_nar_;
    r.exponent_ = this->exponent_;
    if constexpr (Base::Traits::DoubleSizeAvailable) {
      r.significand_ = this->significand_;
    } else {
      r.significand_[0] = this->significand_[0];
      r.significand_[1] = this->significand_[1];
    }
    return r;
  }

  constexpr explicit posit_mult_intermediate(posit<N, E> p) noexcept {
    if (p == posit<N, E>::Zero()) {
      new ((void*)this) posit_mult_intermediate(Zero());
    } else if (p == posit<N, E>::NaR()) {
      new ((void*)this) posit_mult_intermediate(NaR());
    } else {
      this->FillFromDecoded(decode_posit<N, E>(p.bits_));
    }
  }

  template <
      int N2, int E2,
      enable_if_t<std::is_convertible_v<posit<N2, E2>, posit<N, E>> &&
                  Base::Traits::SBits == PositTraits<N2, E2>::SBits>* = nullptr>
  constexpr explicit posit_mult_intermediate(
      posit_mult_intermediate<N2, E2> p) noexcept
      : Base(static_cast<Base&&>(p)) {}

  template <
      int N2, int E2,
      enable_if_t<std::is_convertible_v<posit<N2, E2>, posit<N, E>> &&
                  Base::Traits::SBits != PositTraits<N2, E2>::SBits>* = nullptr>
  constexpr explicit posit_mult_intermediate(
      posit_mult_intermediate<N2, E2> p) noexcept {
    using Traits = typename Base::Traits;
    this->is_negative_ = p.is_negative_;
    this->is_zero_ = p.is_zero_;
    this->is_nar_ = p.is_nar_;
    this->exponent_ = p.exponent_;
    if constexpr (Traits::SBits == PositTraits<N2, E2>::SBits) {
      if constexpr (Traits::DoubleSizeAvailable) {
        this->significand_ = p.significand_;
      } else {
        this->significand_[0] = p.significand_[0];
        this->significand_[1] = p.significand_[1];
      }
    } else {
      // Since p is convertible to this, but has different storage, it must be
      // smaller. We expect that either both types have double-sized storage,
      // or the other does and it fits into a single entry of this. This is
      // based on the assumption that, for any implementation with a biggest
      // integer type, that type is twice the size of the next biggest.
      static_assert(PositTraits<N2, E2>::Storage::DoubleSizeAvailable);
      if constexpr (Traits::DoubleSizeAvailable) {
        this->significand_ =
            static_cast<PositDoubleUnsigned<Traits::SBits>>(p.significand_)
                << (Traits::SBits * 2 - PositTraits<N, E>::SBits * 2);
      } else {
        static_assert(PositTraits<N2, E2>::SBits * 2 <= Traits::SBits);
        this->significand_[0] = 0;
        this->significand_[1] =
            static_cast<typename Traits::Unsigned>(p.significand_)
                << (Traits::SBits - PositTraits<N2, E2>::SBits * 2);
      }
    }
  }

  constexpr posit_mult_intermediate(posit_mult_intermediate&&) = default;

 private:
  template <int NQ, int C>
  friend class quire;
  friend constexpr posit_mult_intermediate operator* <N, E>(
      posit<N, E> lhs, posit<N, E> rhs) noexcept;
  friend constexpr fused_add_result<N, E, N, E> fused_add<N, E, N, E>(
      posit_mult_intermediate lhs, posit_mult_intermediate rhs) noexcept;

  template <int N_, int E_>
  friend constexpr posit_mult_intermediate<N_, E_> adjust_mult_exponent(
      posit_mult_intermediate<N_, E_> p, int adjust) noexcept;

  constexpr posit_mult_intermediate() = default;
  constexpr posit_mult_intermediate& operator=(posit_mult_intermediate&&) =
      delete;

  constexpr posit_mult_intermediate(Base&& base) noexcept
      : Base(static_cast<Base&&>(base)) {}

  static constexpr posit_mult_intermediate Zero() noexcept {
    return Base::Zero();
  }
  static constexpr posit_mult_intermediate NaR() noexcept {
    return Base::NaR();
  }

  constexpr void Add(posit_mult_intermediate p) noexcept {
    Base::Add(static_cast<Base&&>(p));
  }
  constexpr void Sub(posit_mult_intermediate p) noexcept {
    Base::Sub(static_cast<Base&&>(p));
  }
};

template <int S>
constexpr typename PositByStorage<S>::mult_intermediate
PositByStorage<S>::Multiply(decoded_posit<S> l_dec,
                            decoded_posit<S> r_dec) noexcept {
  bool negative = l_dec.sign != r_dec.sign;
  int exponent = l_dec.exponent + r_dec.exponent;

  using U = typename Traits::Unsigned;
  using DU = PositDoubleUnsigned<SBits, true>;
  constexpr U high_bit = Traits::kHighBit;

  // It's impossible to have all fraction bits, so make the leading one
  // explicit. The multiplication is done in fixed point 1.S * 1.S => 2.{2S}.
  U l_bits = (l_dec.fraction >> 1) | high_bit;
  U r_bits = (r_dec.fraction >> 1) | high_bit;
  DU product = {0};
  if constexpr (Traits::DoubleSizeAvailable) {
    constexpr DU high_bit_double = DU{1} << (SBits * 2 - 1);
    product = DU{l_bits} * DU{r_bits};
    // Switch to 1.{2S+1}, either by shifting or adjusting the exponent. At
    // least one of the two high bits must be set, since the high bit was set
    // in both factors.
    if (product & high_bit_double) {
      ++exponent;
    } else {
      product <<= 1;
    }
  } else {
    // No double-wide math available. Split each factor into two:
    // AB * CD = BD + AD << 1 + BC << 1 + AC << 2.
    static_assert((SBits & 1) == 0);
    constexpr int HS = SBits / 2;
    constexpr U low_mask = (U{1} << HS) - 1;
    U a = l_bits >> HS, b = l_bits & low_mask;
    U c = r_bits >> HS, d = r_bits & low_mask;
    U ac = a * c, bc = b * c, ad = a * d, bd = b * d;

    product[0] = bd;
    product[1] = ac;
    U carry = 0;
    product[0] = builtin_addc(product[0], static_cast<U>(ad << HS), 0, &carry);
    product[1] += (ad >> HS) + carry;
    product[0] = builtin_addc(product[0], static_cast<U>(bc << HS), 0, &carry);
    product[1] += (bc >> HS) + carry;
    // Switch to 1.{2S+1}, either by shifting or adjusting the exponent. At
    // least one of the two high bits must be set, since the high bit was set
    // in both factors.
    if (product[1] & high_bit) {
      ++exponent;
    } else {
      bool save = (product[0] & high_bit);
      product[0] <<= 1;
      product[1] = (product[1] << 1) | save;
    }
  }
  return mult_intermediate::Finite(negative, exponent, product);
}

template <int N, int E>
constexpr posit_mult_intermediate<N, E> operator*(
    posit<N, E> lhs, posit<N, E> rhs) noexcept {
  using pos = posit<N, E>;
  if (lhs == pos::NaR() || rhs == pos::NaR()) {
    return pos::mult_intermediate::NaR();
  }
  if (lhs == pos::Zero() || rhs == pos::Zero()) {
    return pos::mult_intermediate::Zero();
  }
  decoded_posit l_dec = decode_posit<N, E>(lhs.bits_);
  decoded_posit r_dec = decode_posit<N, E>(rhs.bits_);
  return PositByStorage<pos::Traits::SBits>::Multiply(l_dec, r_dec);
}

template <int S>
constexpr typename PositByStorage<S>::DividePrecheckResult
PositByStorage<S>::DividePrecheck(Signed n, Signed d) noexcept {
  if (n == kNaR || d == kNaR || d == kZero) {
    return {kNaR, true};
  }
  if (n == kZero || d == kOne) {
    return {n, true};
  }
  return {n, false};
}

template <int S>
template <int MaxFractionBits>
constexpr decoded_posit<S> PositByStorage<S>::DivideImpl(
    decoded_posit<SBits> n_dec, decoded_posit<SBits> d_dec) noexcept {
  // Note: MaxFractionBits is likely 0 if Traits::DoubleSizeAvailable is true.

  int sign = d_dec.sign < 0 ? -n_dec.sign : n_dec.sign;
  int exponent = n_dec.exponent - d_dec.exponent;

  using U = typename Traits::Unsigned;
  constexpr U high_bit = Traits::kHighBit;

  U q_fraction = 0;
  bool truncated = false;
  if constexpr (Traits::DoubleSizeAvailable) {
    using DU = PositDoubleUnsigned<SBits>;
    constexpr DU high_bit_double = DU{1} << (S * 2 - 1);
    // It's impossible to have all fraction bits, so make the leading one
    // explicit. The division is done in fixed point 1.{2S-1} / 1.{S-1} => 1.S.
    DU n_bits = (DU{n_dec.fraction} << 31) | high_bit_double;
    DU d_bits = (d_dec.fraction >> 1) | high_bit;
    DU q = n_bits / d_bits;
    truncated = (n_bits % d_bits) != 0;
    q_fraction = static_cast<U>(q);
  } else if constexpr (MaxFractionBits > 0) {
    // No double-wide math available, so the division needs to be done in
    // multiple rounds. The denominator is shifted right to maximize the number
    // of bits per round; at least 3+ExpBits-1 low bits are clear.
    constexpr int MinBitsPerRound = SBits - MaxFractionBits - 1;
    // One extra for the implicit bit, one for rounding, and one in case the
    // denominator has a larger fraction, meaning the result is in [0.5, 1).
    constexpr int TotalBitsNeeded = MaxFractionBits + 3;
    constexpr int MaxRounds =
        (TotalBitsNeeded + MinBitsPerRound - 1) / MinBitsPerRound;
    U n_bits = (n_dec.fraction >> 1) | high_bit;
    U d_bits = (d_dec.fraction >> 1) | high_bit;
    {
      // Shift the denominator as far right as possible, to maximize the number
      // of bits returned per round.
      int tz = tzcnt(d_bits);
      d_bits >>= tz;
    }
    q_fraction = 0;
    int needed = TotalBitsNeeded;
    // An extra offset of 1 to shift off the implicit bit. MinBitsPerRound must
    // be at least two so the shift amount will always be less than SBits.
    int offset = S + 1;
    {
      // Round 0 is special, because the numerator is left-aligned and the
      // number of output bits is unknown, but it is known that all leading
      // zero bits of the output are unnecessary.
      U q = n_bits / d_bits;
      int round_bits = SBits - lzcnt(q);
      n_bits = n_bits % d_bits;
      needed -= round_bits;
      offset -= round_bits;
      if (offset > 0) {
        q_fraction += q << offset;
      } else {
        q_fraction += q >> -offset;
      }
    }
    for (int i = 1; i < MaxRounds && n_bits != 0 && needed > 0; ++i) {
      int round_bits = lzcnt(n_bits);
      n_bits <<= round_bits;
      U q = n_bits / d_bits;
      n_bits = n_bits % d_bits;
      needed -= round_bits;
      offset -= round_bits;
      if (offset > 0) {
        q_fraction += q << offset;
      } else {
        q_fraction += q >> -offset;
      }
    }
    truncated = n_bits != 0;
  } else {
    // There are never any fraction bits, so the division must yield 1.0.
    q_fraction = 0;
    truncated = false;
  }
  // If the denominator had a larger fraction, the result is less than 1 and so
  // the exponent needs to be adjusted.
  if (n_dec.fraction < d_dec.fraction) {
    if constexpr (Traits::DoubleSizeAvailable) {
      q_fraction <<= 1;
    }  // In other cases, the actual highest set bit was shifted off already.
    --exponent;
  }
  // Use the low bit of the result to mark if any truncated bits were set.
  if (truncated) q_fraction |= 1;
  decoded_posit<SBits> q_dec{};
  q_dec.sign = sign;
  q_dec.exponent = exponent;
  q_dec.fraction = q_fraction;
  return q_dec;
}

template <int S>
template <typename PosTraits>
constexpr typename PosTraits::Signed PositByStorage<S>::Divide(
    typename PosTraits::Signed n, typename PosTraits::Signed d) noexcept {
  DividePrecheckResult precheck = DividePrecheck(n, d);
  if (__builtin_expect(precheck.has_value, 0)) return precheck.value;

  // Only used if DoubleSizeAvailable is false. When true, always pass the same
  // value to minimize unique instantiations.
  constexpr int MaxFractionBits =
      Traits::DoubleSizeAvailable ? 0 : PosTraits::MaxFractionBits;
  constexpr int N = PosTraits::NBits;
  constexpr int E = PosTraits::ExpBits;
  decoded_posit<S> q_dec = DivideImpl<MaxFractionBits>(
      decode_posit<N, E>(n), decode_posit<N, E>(d));
  return encode_regular_posit<N, E>(q_dec);
}

template <int N, int E>
constexpr posit<N, E> operator/(posit<N, E> n, posit<N, E> d) noexcept {
  using pos = posit<N, E>;
  return pos::WithBits(
      PositByStorage<pos::Traits::SBits>
          ::template Divide<typename pos::Traits>(n.bits_, d.bits_));
}

template <int S>
constexpr typename PositByStorage<S>::AddSubPrecheckResult
PositByStorage<S>::AddSubPrecheck(Signed l, Signed r) noexcept {
  if (l == kNaR || r == kNaR) {
    return {kNaR, 0, true, false, false};
  }
  bool diff_sign = (l < 0) != (r < 0);
  Signed abs_l = l >= 0 ? l : -l;
  Signed abs_r = r >= 0 ? r : -r;
  bool switch_order = abs_l < abs_r;
  Signed a = !switch_order ? l : r;
  Signed b = !switch_order ? r : l;
  return {a, b, b == kZero, switch_order, diff_sign};
}

template <int S>
constexpr decoded_posit<S> PositByStorage<S>::Add(
    decoded_posit<S> a_dec, int b_exp, Unsigned b_fraction) noexcept {
  // a_exp >= b_exp, since we ensured a >= b.
  if (a_dec.exponent > b_exp) {
    int shift = a_dec.exponent - b_exp;
    if (shift >= SBits) {
      // The fraction of b is entirely shifted off. If the exponent difference
      // is exactly SBits, the hidden bit will hit the low bit, but that can't
      // be set since there can't be that many fraction bits. Thus, simply set
      // the low fraction bit of a to allow proper rounding, since at least the
      // hidden bit has been truncated or added.
      a_dec.fraction |= 1;
    } else {
      Unsigned drop_mask = (Unsigned{1} << shift) - 1;
      bool dropped = (b_fraction & drop_mask) != 0;
      Unsigned add = (b_fraction >> shift) | (Unsigned{1} << (SBits - shift));
      Unsigned carry = 0;
      a_dec.fraction = builtin_addc(a_dec.fraction, add, 0, &carry);
      if (carry) {
        // Carried into the hidden bit. Shift in the new high bit, which is now
        // zero, and increment the exponent.
        dropped = (a_dec.fraction & 1) != 0 || dropped;
        a_dec.fraction >>= 1;
        ++a_dec.exponent;
      }
      if (dropped) {
        // Set the low bit if any dropped bits were set, to ensure proper
        // rounding.
        a_dec.fraction |= 1;
      }
    }
  } else {
    // Both have equal exponents, so the hidden bits add together and carry.
    // Thus, an extra fraction bit is always needed. Since the fraction can't
    // possibly have 32 bits of data, it is claimed before adding.
    a_dec.fraction = (a_dec.fraction >> 1) + (b_fraction >> 1);
    ++a_dec.exponent;
  }
  return a_dec;
}

template <int S>
constexpr decoded_posit<S> PositByStorage<S>::Subtract(
    decoded_posit<S> a_dec, int b_exp, Unsigned b_fraction) noexcept {
  // a_exp >= b_exp, since we ensured a >= b.
  bool lost_hidden = false;
  bool dropped = false;
  if (a_dec.exponent > b_exp) {
    int shift = a_dec.exponent - b_exp;
    Unsigned sub = 0;
    if (shift >= SBits) {
      // The fraction of b is entirely shifted off; the hidden bit may hit the
      // low. Thus, the true amount to be subtracted, including borrow, could
      // be either one or two. But, since the low two bits can never fit into
      // the encoded posit, subtracting either of these values is identical.
      sub = 1;
      dropped = true;
    } else {
      Unsigned drop_mask = (Unsigned{1} << shift) - 1;
      dropped = (b_fraction & drop_mask) != 0;
      sub = (b_fraction >> shift) | (Unsigned{1} << (SBits - shift));
      if (dropped) ++sub;
    }
    Unsigned carry = 0;
    a_dec.fraction = builtin_subc(a_dec.fraction, sub, 0, &carry);
    lost_hidden = carry;
  } else {
    // Both have equal exponents, so the hidden bit will always be lost. Since
    // there is an early return for lhs == rhs, and it is ensured that a >= b,
    // the actual subtraction must have a positive result.
    a_dec.fraction -= b_fraction;
    lost_hidden = true;
    dropped = false;
  }
  if (lost_hidden) {
    // Borrowed from the hidden bit. Shift out however many bits until a new
    // hidden bit is available, and update the exponent.
    // Note: If a_exp - b_exp >= 2, then the borrow must have left the high bit
    // set; only one bit will be shifted and so none of the dropped bits would
    // make it into the encoded result. Otherwise, for a small exponent offset,
    // none of the fraction bits that get shifted off could have been set. In
    // either case, the existing fraction precision is sufficient even with
    // a large change in exponent/regime.
    int shift = lzcnt(a_dec.fraction) + 1;
    a_dec.fraction <<= shift;
    a_dec.exponent -= shift;
  }
  if (dropped) {
    a_dec.fraction |= 1;
  }
  return a_dec;
}

template <int N, int E>
constexpr posit<N, E> operator+(posit<N, E> lhs, posit<N, E> rhs) noexcept {
  using Traits = typename posit<N, E>::Traits;
  using BS = PositByStorage<Traits::SBits>;
  auto precheck = BS::AddSubPrecheck(lhs.bits_, rhs.bits_);
  if (__builtin_expect(precheck.pre_result, 0)) {
    return posit<N, E>::WithBits(precheck.a);
  }

  decoded_posit<Traits::SBits> a_dec = decode_posit<N, E>(precheck.a);
  decoded_posit<Traits::SBits> b_dec = decode_posit<N, E>(precheck.b);
  decoded_posit<Traits::SBits> r_dec{};
  if (!precheck.differing_signs) {
    r_dec = BS::Add(a_dec, b_dec.exponent, b_dec.fraction);
  } else {
    // Performing `l - -r`, which switches the sign of rhs. If rhs ended up
    // in b, its sign is ignored; if it ended up in a, the actual operation is
    // `-(-r - l)`, so the sign gets changed back and lhs's sign is ignored.
    // In either case, no sign changes need actually be performed.
    r_dec = BS::Subtract(a_dec, b_dec.exponent, b_dec.fraction);
  }
  return posit<N, E>::WithBits(encode_regular_posit<N, E>(r_dec));
}

template <int N, int E>
constexpr posit<N, E> operator-(posit<N, E> lhs, posit<N, E> rhs) noexcept {
  using Traits = typename posit<N, E>::Traits;
  using BS = PositByStorage<Traits::SBits>;
  auto precheck = BS::AddSubPrecheck(lhs.bits_, rhs.bits_);
  if (__builtin_expect(precheck.pre_result, 0)) {
    if (precheck.switched_order) precheck.a = -precheck.a;
    return posit<N, E>::WithBits(precheck.a);
  }
  if (__builtin_expect(lhs.bits_ == rhs.bits_, 0)) return posit<N, E>::Zero();

  decoded_posit<Traits::SBits> a_dec = decode_posit<N, E>(precheck.a);
  decoded_posit<Traits::SBits> b_dec = decode_posit<N, E>(precheck.b);
  decoded_posit<Traits::SBits> r_dec{};
  if (precheck.switched_order) {
    // Performing `-(r - l)`, so a's sign needs to change. b's sign is unused.
    a_dec.sign = -a_dec.sign;
  }
  if (!precheck.differing_signs) {
    r_dec = BS::Subtract(a_dec, b_dec.exponent, b_dec.fraction);
  } else {
    // Performing `l + -r` or '-r + l`. In either case the sign change above
    // is correct.
    r_dec = BS::Add(a_dec, b_dec.exponent, b_dec.fraction);
  }
  return posit<N, E>::WithBits(encode_regular_posit<N, E>(r_dec));
}

template <int N, int E>
constexpr posit<N, E>& operator*=(posit<N, E>& lhs, posit<N, E> rhs) noexcept {
  return lhs = lhs * rhs; }
template <int N, int E>
constexpr posit<N, E>& operator/=(posit<N, E>& lhs, posit<N, E> rhs) noexcept {
  return lhs = lhs / rhs; }
template <int N, int E>
constexpr posit<N, E>& operator+=(posit<N, E>& lhs, posit<N, E> rhs) noexcept {
  return lhs = lhs + rhs; }
template <int N, int E>
constexpr posit<N, E>& operator-=(posit<N, E>& lhs, posit<N, E> rhs) noexcept {
  return lhs = lhs - rhs; }

template <int NQ, int C>
constexpr quire<NQ, C> quire<NQ, C>::operator-() const noexcept {
  quire r = *this;
  auto* it = &r.bits_[0], *end = &r.bits_[ArrayEntries];
  while (it != end && *it == 0) ++it;
  if (it != end) {
    *it = -*it;
    ++it;
  }
  for (; it != end; ++it) *it = ~*it;
  return r;
}

template <int NQ, int C>
constexpr void quire<NQ, C>::SumRealQuires(ArrayType *lhs,
                                           const ArrayType* rhs) noexcept {
  constexpr ArrayType kSign = kHighBit;
  const bool can_overflow =
      (lhs[ArrayEntries - 1] & kSign) == (rhs[ArrayEntries - 1] & kSign);
  ArrayType carry = 0;
  auto* d = lhs;
  for (const auto* s = rhs, *end = &lhs[ArrayEntries]; d != end; ++d, ++s) {
    *d = builtin_addc(*d, *s, carry, &carry);
  }
  if (__builtin_expect(carry == !(lhs[ArrayEntries - 1] & kSign), 0)
          && can_overflow) {
    if (carry) {
      // Overflowed negative.
      MakeMaxNeg(lhs);
    } else {
      // Overflowed positive.
      MakeMaxPos(lhs);
    }
  }
}

template <int NQ, int C>
constexpr quire<NQ, C>& quire<NQ, C>::operator+=(const quire& q) noexcept {
  if (__builtin_expect(IsNaR(), 0)) return *this;
  if (__builtin_expect(q.IsNaR(), 0)) {
    MakeNaR();
    return *this;
  }
  SumRealQuires(bits_, q.bits_);
  return *this;
}

template <int NQ, int C>
constexpr quire<NQ, C>& quire<NQ, C>::operator-=(const quire& q) noexcept {
  constexpr ArrayType kSign = kHighBit;
  if (__builtin_expect(IsNaR(), 0)) return *this;
  if (__builtin_expect(q.IsNaR(), 0)) {
    MakeNaR();
    return *this;
  }

  const bool can_overflow =
      (bits_[ArrayEntries - 1] & kSign) != (q.bits_[ArrayEntries - 1] & kSign);
  ArrayType carry = 0;
  auto* d = &bits_[0];
  for (const auto* s = &q.bits_[0], *end = &bits_[ArrayEntries]; d != end;
       ++d, ++s) {
    *d = builtin_subc(*d, *s, carry, &carry);
  }
  if (__builtin_expect(carry != !(bits_[ArrayEntries - 1] & kSign), 0)
          && can_overflow) {
    if (carry) {
      // Overflowed positive.
      MakeMaxPos(bits_);
    } else {
      // Overflowed negative.
      MakeMaxNeg(bits_);
    }
  }
  return *this;
}

template <int NQ, int C>
template <typename UInt>
constexpr void quire<NQ, C>::Add(int min_bit_pos, UInt significand) noexcept {
  static_assert(sizeof(UInt) >= sizeof(ArrayType),
                "Up-convert to ArrayType before calling Add().");
  constexpr ArrayType kSign = kHighBit;
  constexpr int kPieces =
      (sizeof(UInt) + sizeof(ArrayType) - 1) / sizeof(ArrayType) + 1;
  const bool can_overflow = (bits_[ArrayEntries - 1] & kSign) == 0;
  int bit_offset = min_bit_pos % ArrayEntryBits;
  ArrayType pieces[kPieces] = {};
  pieces[0] =
      bit_offset > 0
          ? static_cast<ArrayType>(
                significand
                    & ((ArrayType{1} << (ArrayEntryBits - bit_offset)) - 1))
                << bit_offset
          : static_cast<ArrayType>(significand);
  for (int i = 1; i < kPieces - 1; ++i) {
    pieces[i] = static_cast<ArrayType>(
        significand >> (i * ArrayEntryBits - bit_offset));
  }
  pieces[kPieces - 1] =
      (bit_offset > 0 || (sizeof(UInt) % sizeof(ArrayType)) != 0)
          ? static_cast<ArrayType>(
                significand >> ((kPieces - 1) * ArrayEntryBits - bit_offset))
          : 0;
  int i = min_bit_pos / ArrayEntryBits;
  ArrayType carry = 0;
  bits_[i] = builtin_addc(bits_[i], pieces[0], 0, &carry);
  for (int j = 1; j < kPieces - 1; ++j) {
    bits_[i + j] = builtin_addc(bits_[i + j], pieces[j], carry, &carry);
  }
  // Due to size restrictions on the operators, there are always at least C
  // bits after the highest bit of the input. However, it's possible that the
  // input was smaller than an array entry, in which case it will have leading
  // zeros, possibly >= C of them. Therefore, it's possible that there are
  // exactly two pieces, the second of which is zero and would write past the
  // end of the array.
  bool skip_last_piece = false;
  if constexpr (std::is_same_v<ArrayType, UInt>) {
    skip_last_piece =
        pieces[kPieces - 1] == 0 && i + kPieces - 1 >= ArrayEntries;
  }
  if (!skip_last_piece) {
    bits_[i + kPieces - 1] = builtin_addc(bits_[i + kPieces - 1],
                                          pieces[kPieces - 1],
                                          carry, &carry);
  }
  for (i += kPieces; i < ArrayEntries; ++i) {
    if (__builtin_expect(!carry, 1)) return;
    bits_[i] = builtin_addc(bits_[i], 0, carry, &carry);
  }
  if (__builtin_expect(can_overflow && (bits_[ArrayEntries - 1] & kSign) != 0,
                       0)) {
      // Overflowed positive.
    MakeMaxPos(bits_);
  }
}

template <int NQ, int C>
template <typename UInt>
constexpr void quire<NQ, C>::Sub(int min_bit_pos, UInt significand) noexcept {
  static_assert(sizeof(UInt) >= sizeof(ArrayType),
                "Up-convert to ArrayType before calling Sub().");
  constexpr ArrayType kSign = kHighBit;
  constexpr int kPieces =
      (sizeof(UInt) + 2*sizeof(ArrayType) - 1) / sizeof(ArrayType);
  const bool can_overflow = (bits_[ArrayEntries - 1] & kSign) != 0;
  int bit_offset = min_bit_pos % ArrayEntryBits;
  ArrayType pieces[kPieces] = {};
  pieces[0] =
      bit_offset > 0
          ? static_cast<ArrayType>(
                significand
                    & ((ArrayType{1} << (ArrayEntryBits - bit_offset)) - 1))
                << bit_offset
          : static_cast<ArrayType>(significand);
  for (int i = 1; i < kPieces - 1; ++i) {
    pieces[i] = static_cast<ArrayType>(
        significand >> (i * ArrayEntryBits - bit_offset));
  }
  pieces[kPieces - 1] =
      (bit_offset > 0 || (sizeof(UInt) % sizeof(ArrayType)) != 0)
          ? static_cast<ArrayType>(
                significand >> ((kPieces - 1) * ArrayEntryBits - bit_offset))
          : 0;
  int i = min_bit_pos / ArrayEntryBits;
  ArrayType carry = 0;
  bits_[i] = builtin_subc(bits_[i], pieces[0], 0, &carry);
  for (int j = 1; j < kPieces; ++j) {
    bits_[i + j] = builtin_subc(bits_[i + j], pieces[j], carry, &carry);
  }
  for (i += kPieces; i < ArrayEntries; ++i) {
    if (__builtin_expect(!carry, 1)) return;
    bits_[i] = builtin_subc(bits_[i], 0, carry, &carry);
  }
  if (__builtin_expect(can_overflow && (bits_[ArrayEntries - 1] & kSign) == 0,
                       0)) {
      // Overflowed negative.
    MakeMaxNeg(bits_);
  }
}

template <int NQ, int C>
template <int N, int E>
constexpr auto quire<NQ, C>::operator+=(posit<N, E> p) noexcept
    -> enable_if_t<kPositFits<N, E>, quire&> {
  using PT = typename posit<N, E>::Traits;
  if (__builtin_expect(IsNaR(), 0)) return *this;
  if (__builtin_expect(p == posit<N, E>::NaR(), 0)) {
    MakeNaR();
    return *this;
  }
  if (__builtin_expect(p == posit<N, E>::Zero(), 0)) {
    return *this;
  }
  decoded_posit dec = decode_posit<N, E>(p.bits_);
  // Get the array bit position for the exponent of bit 0, after the
  // shift below.
  int min_bit_pos = dec.exponent - (PT::SBits - 1) - MinExp;
  // Set the implicit 1 bit.
  dec.fraction >>= 1;
  dec.fraction |= typename PT::Unsigned{1} << (PT::SBits - 1);
  if constexpr (PT::MinExp - (PT::SBits - 1) < MinExp) {
    if (__builtin_expect(min_bit_pos < 0, 0)) {
      if (-min_bit_pos < PT::SBits) {
        typename PT::Unsigned cut_point =
            typename PT::Unsigned{1} << -min_bit_pos;
        typename PT::Unsigned dropped = dec.fraction & (cut_point - 1);
        dec.fraction >>= -min_bit_pos;
        min_bit_pos = 0;
        if (dropped >= cut_point / 2 && (dropped > cut_point / 2 ||
                                         (dec.fraction & 1) != 0)) {
          ++dec.fraction;
        }
      } else {
        if (-min_bit_pos == PT::SBits &&
            dec.fraction > (typename PT::Unsigned{1} << (PT::SBits - 1))) {
          dec.fraction = 1;
        } else {
          dec.fraction = 0;
        }
        min_bit_pos = 0;
      }
    }
  }
  using T = typename cond<sizeof(ArrayType) < sizeof(typename PT::Unsigned)>
                ::template then<typename PT::Unsigned>
                ::template otherwise<ArrayType>;
  if (dec.sign >= 0) {
    Add(min_bit_pos, T{dec.fraction});
  } else {
    Sub(min_bit_pos, T{dec.fraction});
  }
  return *this;
}

template <int NQ, int C>
template <int N, int E>
constexpr auto quire<NQ, C>::operator-=(posit<N, E> p) noexcept
    -> enable_if_t<kPositFits<N, E>, quire&> {
  using PT = typename posit<N, E>::Traits;
  if (__builtin_expect(IsNaR(), 0)) return *this;
  if (__builtin_expect(p == posit<N, E>::NaR(), 0)) {
    MakeNaR();
    return *this;
  }
  if (__builtin_expect(p == posit<N, E>::Zero(), 0)) {
    return *this;
  }
  decoded_posit dec = decode_posit<N, E>(p.bits_);
  // Get the array bit position for the exponent of bit 0, after the
  // shift below.
  int min_bit_pos = dec.exponent - (PT::SBits - 1) - MinExp;
  // Set the implicit 1 bit.
  dec.fraction >>= 1;
  dec.fraction |= typename PT::Unsigned{1} << (PT::SBits - 1);
  if constexpr (PT::MinExp < MinExp + PT::SBits - 1) {
    if (__builtin_expect(min_bit_pos < 0, 0)) {
      if (-min_bit_pos < PT::SBits) {
        typename PT::Unsigned cut_point =
            typename PT::Unsigned{1} << -min_bit_pos;
        typename PT::Unsigned dropped = dec.fraction & (cut_point - 1);
        dec.fraction >>= -min_bit_pos;
        min_bit_pos = 0;
        if (dropped >= cut_point / 2 && (dropped > cut_point / 2 ||
                                         (dec.fraction & 1) != 0)) {
          ++dec.fraction;
        }
      } else {
        if (-min_bit_pos == PT::SBits &&
            dec.fraction > (typename PT::Unsigned{1} << (PT::SBits - 1))) {
          dec.fraction = 1;
        } else {
          dec.fraction = 0;
        }
        min_bit_pos = 0;
      }
    }
  }
  using T = typename cond<sizeof(ArrayType) < sizeof(typename PT::Unsigned)>
                ::template then<typename PT::Unsigned>
                ::template otherwise<ArrayType>;
  if (dec.sign >= 0) {
    Sub(min_bit_pos, T{dec.fraction});
  } else {
    Add(min_bit_pos, T{dec.fraction});
  }
  return *this;
}

template <int NQ, int C>
template <int N, int E>
constexpr auto quire<NQ, C>::operator+=(
    posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<kProductFits<N, E>, quire&> {
  using PT = PositTraits<N, E>;
  constexpr bool IsArr = !PT::Storage::DoubleSizeAvailable;
  if (__builtin_expect(IsNaR(), 0)) return *this;
  if (__builtin_expect(p.is_nar_, 0)) {
    MakeNaR();
    return *this;
  }
  if (__builtin_expect(p.is_zero_, 0)) {
    return *this;
  }
  int min_bit_pos = p.exponent_ - (PT::SBits*2 - 1) - MinExp;
  auto sig = p.significand_;  // May be a pointer to an array of 2.
  if (__builtin_expect(min_bit_pos < 0, 0)) {
    if constexpr (IsArr) {
      if (-min_bit_pos < PT::SBits) {
        typename PT::Unsigned cut_pos =
            typename PT::Unsigned{1} << -min_bit_pos;
        typename PT::Unsigned dropped = sig[0] & (cut_pos - 1);
        sig[0] >>= -min_bit_pos;
        sig[0] |= (sig[1] & ((typename PT::Unsigned{1} << -min_bit_pos) - 1))
                      << (PT::SBits + min_bit_pos);
        sig[1] >>= -min_bit_pos;
        if (dropped >= cut_pos / 2 && (dropped > cut_pos / 2 ||
                                       (sig[0] & 1) != 0)) {
          if (++sig[0] == 0) ++sig[1];
        }
      } else if (-min_bit_pos < 2*PT::SBits) {
        typename PT::Unsigned cut_pos =
            typename PT::Unsigned{1} << (-min_bit_pos - PT::SBits);
        typename PT::Unsigned dropped = sig[1] & (cut_pos - 1);
        bool round = dropped >= cut_pos / 2 && (dropped > cut_pos / 2 ||
                                                sig[0] != 0 ||
                                                (sig[1] & cut_pos) != 0);
        sig[0] = sig[1] >> (-min_bit_pos - PT::SBits);
        sig[1] = 0;
        if (round) {
          if (++sig[0] == 0) ++sig[1];
        }
      } else {
        typename PT::Unsigned high =
            typename PT::Unsigned{1} << (PT::SBits - 1);
        if (-min_bit_pos == 2*PT::SBits && sig[1] >= high &&
            (sig[1] > high || sig[0] != 0)) {
          sig[0] = 1;
        } else {
          sig[0] = 0;
        }
        sig[1] = 0;
      }
    } else {
      if (-min_bit_pos < 2*PT::SBits) {
        PositDoubleUnsigned<PT::SBits> cut_point =
            PositDoubleUnsigned<PT::SBits>{1} << -min_bit_pos;
        PositDoubleUnsigned<PT::SBits> dropped = sig & (cut_point - 1);
        sig >>= -min_bit_pos;
        if (dropped >= cut_point / 2 && (dropped > cut_point / 2 ||
                                         (sig & 1) != 0)) {
          ++sig;
        }
      } else {
        if (-min_bit_pos == 2*PT::SBits &&
            sig > (PositDoubleUnsigned<PT::SBits>{1} << (2*PT::SBits - 1))) {
          sig = 1;
        } else {
          sig = 0;
        }
      }
    }
    min_bit_pos = 0;
  }
  if constexpr (IsArr) {
    using T = typename cond<sizeof(ArrayType) < sizeof(typename PT::Unsigned)>
                  ::template then<typename PT::Unsigned>
                  ::template otherwise<ArrayType>;
    if (p.is_negative_) {
      Sub(min_bit_pos, T{sig[0]});
      Sub(min_bit_pos + PT::SBits, T{sig[1]});
    } else {
      Add(min_bit_pos, T{sig[0]});
      Add(min_bit_pos + PT::SBits, T{sig[1]});
    }
  } else {
    using DU = PositDoubleUnsigned<PT::SBits>;
    using T = typename cond<sizeof(ArrayType) < sizeof(DU)>
                  ::template then<DU>
                  ::template otherwise<ArrayType>;
    if (p.is_negative_) {
      Sub(min_bit_pos, T{sig});
    } else {
      Add(min_bit_pos, T{sig});
    }
  }
  return *this;
}

template <int NQ, int C>
template <int N, int E>
constexpr auto quire<NQ, C>::operator-=(
    posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<kProductFits<N, E>, quire&> {
  using PT = PositTraits<N, E>;
  constexpr bool IsArr = !PT::Storage::DoubleSizeAvailable;
  if (__builtin_expect(IsNaR(), 0)) return *this;
  if (__builtin_expect(p.is_nar_, 0)) {
    MakeNaR();
    return *this;
  }
  if (__builtin_expect(p.is_zero_, 0)) {
    return *this;
  }
  int min_bit_pos = p.exponent_ - (PT::SBits*2 - 1) - MinExp;
  auto sig = p.significand_;  // May be a pointer to an array of 2.
  if (__builtin_expect(min_bit_pos < 0, 0)) {
    if constexpr (IsArr) {
      if (-min_bit_pos < PT::SBits) {
        typename PT::Unsigned cut_pos =
            typename PT::Unsigned{1} << -min_bit_pos;
        typename PT::Unsigned dropped = sig[0] & (cut_pos - 1);
        sig[0] >>= -min_bit_pos;
        sig[0] |= (sig[1] & ((typename PT::Unsigned{1} << -min_bit_pos) - 1))
                      << (PT::SBits + min_bit_pos);
        sig[1] >>= -min_bit_pos;
        if (dropped >= cut_pos / 2 && (dropped > cut_pos / 2 ||
                                       (sig[0] & 1) != 0)) {
          if (++sig[0] == 0) ++sig[1];
        }
      } else if (-min_bit_pos < 2*PT::SBits) {
        typename PT::Unsigned cut_pos =
            typename PT::Unsigned{1} << (-min_bit_pos - PT::SBits);
        typename PT::Unsigned dropped = sig[1] & (cut_pos - 1);
        bool round = dropped >= cut_pos / 2 && (dropped > cut_pos / 2 ||
                                                sig[0] != 0 ||
                                                (sig[1] & cut_pos) != 0);
        sig[0] = sig[1] >> (-min_bit_pos - PT::SBits);
        sig[1] = 0;
        if (round) {
          if (++sig[0] == 0) ++sig[1];
        }
      } else {
        typename PT::Unsigned high =
            typename PT::Unsigned{1} << (PT::SBits - 1);
        if (-min_bit_pos == 2*PT::SBits && sig[1] >= high &&
            (sig[1] > high || sig[0] != 0)) {
          sig[0] = 1;
        } else {
          sig[0] = 0;
        }
        sig[1] = 0;
      }
    } else {
      if (-min_bit_pos < 2*PT::SBits) {
        PositDoubleUnsigned<PT::SBits> cut_point =
            PositDoubleUnsigned<PT::SBits>{1} << -min_bit_pos;
        PositDoubleUnsigned<PT::SBits> dropped = sig & (cut_point - 1);
        sig >>= -min_bit_pos;
        if (dropped >= cut_point / 2 && (dropped > cut_point / 2 ||
                                         (sig & 1) != 0)) {
          ++sig;
        }
      } else {
        if (-min_bit_pos == 2*PT::SBits &&
            sig > (PositDoubleUnsigned<PT::SBits>{1} << (2*PT::SBits - 1))) {
          sig = 1;
        } else {
          sig = 0;
        }
      }
    }
    min_bit_pos = 0;
  }
  if constexpr (IsArr) {
    using T = typename cond<sizeof(ArrayType) < sizeof(typename PT::Unsigned)>
                  ::template then<typename PT::Unsigned>
                  ::template otherwise<ArrayType>;
    if (p.is_negative_) {
      Add(min_bit_pos, T{sig[0]});
      Add(min_bit_pos + PT::SBits, T{sig[1]});
    } else {
      Sub(min_bit_pos, T{sig[0]});
      Sub(min_bit_pos + PT::SBits, T{sig[1]});
    }
  } else {
    using DU = PositDoubleUnsigned<PT::SBits>;
    using T = typename cond<sizeof(ArrayType) < sizeof(DU)>
                  ::template then<DU>
                  ::template otherwise<ArrayType>;
    if (p.is_negative_) {
      Add(min_bit_pos, T{sig});
    } else {
      Sub(min_bit_pos, T{sig});
    }
  }
  return *this;
}

template <int NQ, int C>
template <int N, int E>
constexpr posit<N, E> quire<NQ, C>::to_posit() const noexcept {
  using pos = posit<N, E>;
  using PT = typename pos::Traits;
  const bool negative = (bits_[ArrayEntries - 1] & kHighBit) != 0;
  // Non-negative: Look for the highest non-empty entry.
  // Negative: Look for the highest not-all-1s entry.
  int i = 0;
  for (i = ArrayEntries - 1; i >= 0; --i) {
    if (!negative && bits_[i] != 0) break;
    if (negative && bits_[i] != ArrayType(~ArrayType{0})) break;
  }
  if (i < 0) {
    // No non-zero entry found, the entire thing is zero.
    if (!negative) return pos::Zero();
    // No not-all-1s entry found, the entire thing is 1s.
    if constexpr (MinExp <= PT::MinExp) {
      return -pos::Min();
    } else {
      decoded_posit<PT::SBits> dec{};
      dec.sign = -1;
      dec.exponent = MinExp;
      dec.fraction = 0;
      return pos::WithBits(encode_regular_posit<N, E>(dec));
    }
  }
  if (negative && __builtin_expect(i == ArrayEntries - 1, 0)) {
    if (__builtin_expect(IsNaR(), 1)) {
      return pos::NaR();
    }
    if constexpr (NBits - ArrayEntryBits > pos::Traits::MaxExp) {
      return -pos::Max();
    }
  }
  int lz = lzcnt(negative ? ArrayType(~bits_[i]) : bits_[i]);
  __builtin_assume(lz >= 0);
  decoded_posit<PT::SBits> dec{};
  dec.sign = negative ? -1 : 1;
  dec.exponent = MinExp + ArrayEntryBits + i * ArrayEntryBits - (lz + 1);
  // Protects against underflowing the buffer, except with large posits.
  if (dec.exponent < PT::MinExp) {
    if (negative) {
      return -pos::Min();
    } else {
      return pos::Min();
    }
  }
  __builtin_assume(i >= (PT::MinExp - MinExp) / ArrayEntryBits);
  bool extra_set_bits = false;
  if constexpr (ArrayEntryBits >= PT::SBits) {
    if (lz < ArrayEntryBits - 1) {
      int shift = (ArrayEntryBits - PT::SBits) - (lz + 1);
      if (shift >= 0) {
        dec.fraction = bits_[i] >> shift;
        if ((bits_[i] & ((ArrayType{1} << shift) - 1)) != 0 ||
            (i > 0 && bits_[i - 1] != 0)) {
          extra_set_bits = true;
        }
      } else {
        // Gives first `ArrayEntryBits - (lz + 1)` bits.
        dec.fraction = bits_[i] << -shift;
        if (i > 0) {
          // Gives last `SBits - ArrayEntryBits + (lz + 1)` more bits.
          dec.fraction |= bits_[i - 1] >> (ArrayEntryBits + shift);
          ArrayType mask = (ArrayType{1} << (ArrayEntryBits + shift)) - 1;
          if ((bits_[i - 1] & mask) != 0) {
            extra_set_bits = true;
          }
        }
      }
    } else {
      dec.fraction = 0;
      if (i > 0) {
        dec.fraction = bits_[i - 1] >> (ArrayEntryBits - PT::SBits);
        ArrayType mask = (ArrayType{1} << (ArrayEntryBits - PT::SBits)) - 1;
        if ((bits_[i - 1] & mask) != 0) {
          extra_set_bits = true;
        }
      }
    }
    i -= 2;
  } else {
    constexpr int kMinExtraEntries = PT::SBits / ArrayEntryBits;
    constexpr int kMaxExtraEntries =
        (PT::SBits + ArrayEntryBits - 1) / ArrayEntryBits;
    int needed = PT::SBits;
    dec.fraction = 0;
    if (bits_[i] > 1) {
      dec.fraction = static_cast<typename PT::Unsigned>(bits_[i])
                         << (lz + 1 + (PT::SBits - ArrayEntryBits));
      needed -= ArrayEntryBits - (lz + 1);
    }
    typename PT::Unsigned tmp = 0;
    for (int j = 0; j < kMinExtraEntries; ++j) {
      if (i <= j) break;
      tmp |= static_cast<typename PT::Unsigned>(bits_[i - 1 - j])
                 << ((kMinExtraEntries - 1 - j) * ArrayEntryBits);
    }
    needed -= ArrayEntryBits * kMinExtraEntries;
    if (needed <= 0) {
      dec.fraction |= tmp >> -needed;
      if ((tmp & ((typename PT::Unsigned{1} << -needed) - 1)) != 0) {
        extra_set_bits = true;
      }
    } else {
      dec.fraction |= tmp << needed;
    }
    if (kMaxExtraEntries > kMinExtraEntries && i >= kMaxExtraEntries) {
      if (needed <= 0) {
        if (bits_[i - kMaxExtraEntries] != 0) {
          extra_set_bits = true;
        }
      } else {
        needed -= ArrayEntryBits;
        dec.fraction |= bits_[i - kMaxExtraEntries] >> -needed;
        ArrayType mask = (ArrayType{1} << -needed) - 1;
        if ((bits_[i - kMaxExtraEntries] & mask) != 0) {
          extra_set_bits = true;
        }
      }
    }
    i -= kMaxExtraEntries + 1;
  }
  // If negative, the data needs to be negated before encoding. If there are
  // any bits set lower, the negation result is 1 too high, but also the low
  // bit should be set to affect rounding properly.
  if (negative) {
    dec.fraction = -dec.fraction;
    if (extra_set_bits) {
      dec.fraction -= 1;
      dec.fraction |= 1;
    }
  } else {
    if (extra_set_bits) {
      dec.fraction |= 1;
    }
  }
  if (dec.fraction & 1) {
    // No need to check further.
    // For non-negative, it would just set this already set bit.
    // For negative, it would simply subtract the low bit then set it.
  } else {
    // Look for lower set bits to affect rounding properly.
    for (; i >= 0; --i) {
      if (bits_[i] != 0) {
        if (negative) {
          dec.fraction -= 1;
          // Since the low bit was clear, it must be set now.
        } else {
          dec.fraction |= 1;
        }
        break;
      }
    }
  }
  // For negative, If the fraction is still zero, the array is a series of 1s
  // followed by a series of 0s, and the leftmost zero was shifted off. In the
  // absence of any other set bits, the hidden bit should actually be the 1
  // immediately before it, so the exponent is increased to account for that.
  if (negative && dec.fraction == 0) ++dec.exponent;
  return pos::WithBits(encode_regular_posit<N, E>(dec));
}

// Specializations for posit conversion-controlling types.

template <typename T>
struct IsPosit : public std::false_type {};
template <int N, int E>
struct IsPosit<posit<N, E>> : public std::true_type {};

template <typename T>
struct IsPositMultIntermediate : public std::false_type {};
template <int N, int E>
struct IsPositMultIntermediate<posit_mult_intermediate<N, E>>
    : public std::true_type {};

// Posit conversions have separate functions and should always be excluded.
template <int N, int E>
template <int N2, int E2>
struct posit<N, E>::FloatAlwaysFits<posit<N2, E2>> :
    public std::false_type {};
template <int N, int E>
template <int N2, int E2>
struct posit<N, E>::FitsIntoFloat<posit<N2, E2>, void> :
    public std::false_type {};

// Handle decimal types. This requires that the posit type be able to
// round-trip through the decimal type.
template <int N, int E>
template <typename F>
struct posit<N, E>::FitsIntoFloat<
    F, enable_if_t<std::numeric_limits<F>::radix == 10>> :
    public std::bool_constant<
               std::numeric_limits<posit>::max_digits10 <=
                   std::numeric_limits<F>::digits &&
               std::numeric_limits<posit>::max_exponent10 <
                   std::numeric_limits<F>::max_exponent - 1 &&
               std::numeric_limits<F>::min_exponent <=
                   std::numeric_limits<posit>::min_exponent10> {};

// Handle types with a non-constant number of digits for normal values, using
// the extra member added for posits.
template <int N, int E>
template <typename F>
struct posit<N, E>::FitsIntoFloat<
    F, enable_if_t<std::numeric_limits<F>::radix == 2 &&
                   0 <= std::numeric_limits<F>::digits_at_exponent(0) &&
                   !IsPosit<F>::value>> :
    public std::bool_constant<
               Traits::MaxFractionBits < std::numeric_limits<F>::digits &&
               Traits::MaxExp < std::numeric_limits<F>::max_exponent &&
               std::numeric_limits<F>::min_exponent <= 1+Traits::MinExp &&
               // Assume a fairly even roll-off. Check regime 1, max, and about
               // halfway in between, and if they all work assume anything will.
               Traits::FractionBitsAtExponent(1 << Traits::ExpBits) <
                   std::numeric_limits<F>::digits_at_exponent(
                       1 << Traits::ExpBits) &&
               Traits::FractionBitsAtExponent(
                   (Traits::NBits / 2) << Traits::ExpBits) <
                   std::numeric_limits<F>::digits_at_exponent(
                       (Traits::NBits / 2) << Traits::ExpBits) &&
               Traits::FractionBitsAtExponent(Traits::MaxExp) <
                   std::numeric_limits<F>::digits_at_exponent(
                       Traits::MaxExp)> {};

struct literal_helper {
  template <char> static constexpr bool is_hex() { return false; }
  template <char, char> static constexpr bool is_hex() { return false; }
  template <char A, char B, char, char...> static constexpr bool is_hex() {
    return A == '0' && (B == 'x' || B == 'X');
  }

  template <char> static constexpr bool is_bin() { return false; }
  template <char, char> static constexpr bool is_bin() { return false; }
  template <char A, char B, char, char...> static constexpr bool is_bin() {
    return A == '0' && (B == 'b' || B == 'B');
  }

  template <char A, char...> static constexpr bool maybe_oct() {
    return A == '0';
  }

  template <char... Chars>
  static constexpr int find_exponent(int per_pos) {
    enum State {
      kInteger = 0,
      kFraction = 1,
      kExponentSign = 2,
      kExponent = 3,
    };
    State state = kInteger;
    int implicit_exp = 0;
    bool nonzero = false;
    int explicit_sign = 0;
    int explicit_exp = 0;
    for (char c : {Chars...}) {
      switch (state) {
      case kInteger:
        if (c == 'p' || c == 'P') {
          state = kExponentSign;
          continue;
        }
        if (c == '.') { state = kFraction; continue; }
        if (nonzero) {
          implicit_exp += per_pos;
          continue;
        }
        if (c == '0') continue;
        nonzero = true;
        if (c >= '8') implicit_exp += 3;
        else if (c >= '4') implicit_exp += 2;
        else if (c >= '2') implicit_exp += 1;
        continue;
      case kFraction:
        if (c == 'p' || c == 'P') {
          state = kExponentSign;
          continue;
        }
        if (nonzero) continue;
        if (c == '0') {
          implicit_exp -= per_pos;
          continue;
        }
        nonzero = true;
        if (c >= '8') implicit_exp -= per_pos - 3;
        else if (c >= '4') implicit_exp -= per_pos - 2;
        else if (c >= '2') implicit_exp -= per_pos - 1;
        else implicit_exp -= per_pos;
        continue;
      case kExponentSign:
        state = kExponent;
        if (c == '-') { explicit_sign = -1; continue; }
        explicit_sign = 1;
        if (c == '+') continue;
        [[fallthrough]];
      case kExponent:
        explicit_exp = explicit_exp * 10 + c - '0';
        continue;
      }
    }
    if (!nonzero) return INT_MIN;
    return implicit_exp + explicit_sign * explicit_exp;
  }

  template <char, char, char... Chars>
  static constexpr int find_hex_exponent() {
    return find_exponent<Chars...>(4);
  }

  template <char, char... Chars>
  static constexpr int find_oct_exponent() {
    if constexpr (sizeof...(Chars) == 0) {  // Literal is just `0`.
      return INT_MIN;
    } else {
      return find_exponent<Chars...>(3);
    }
  }

  template <char, char, char... Chars>
  static constexpr int find_bin_exponent() {
    return find_exponent<Chars...>(1);
  }

  template <char... Chars>
  static constexpr uint32_t find_fraction(int per_pos) {
    uint32_t bits = 0;
    bool nonzero = false;
    int bits_left = 32;
    for (char c : {Chars...}) {
      if (c == 'p' || c == 'P') break;
      if (c == '.') continue;
      uint32_t char_bits = 0;
      if (nonzero) {
        if (c >= '0' && c <= '9') char_bits = c - '0';
        if (c >= 'A' && c <= 'Z') char_bits = c - 'A' + 10;
        if (c >= 'a' && c <= 'z') char_bits = c - 'a' + 10;
        bits_left -= per_pos;
      } else {
        if (c == '0') continue;
        nonzero = true;
        // The first set bit is discarded.
        if (c >= 'A' && c <= 'Z') {
          char_bits = c - 'A' + 10 - 8;
          bits_left -= 3;
        } else if (c >= 'a' && c <= 'z') {
          char_bits = c - 'a' + 10 - 8;
          bits_left -= 3;
        } else if (c == '8' || c == '9') {
          char_bits = c - '0' - 8;
          bits_left -= 3;
        } else if (c >= '4' && c <= '7') {
          char_bits = c - '0' - 4;
          bits_left -= 2;
        } else if (c == '2' || c == '3') {
          char_bits = c - '0' - 2;
          bits_left -= 1;
        } else if (c == '1') {
          char_bits = 0;
        }
      }
      if (bits_left >= 0) {
        if (char_bits != 0) bits |= char_bits << bits_left;
      } else {
        if (bits_left > -per_pos) {
          bits |= char_bits >> -bits_left;
          char_bits &= (1 << (per_pos + bits_left)) - 1;
        }
        if (char_bits != 0) {
          bits |= 1;
          break;
        }
      }
    }
    return bits;
  }

  template <char, char, char... Chars>
  static constexpr int find_hex_fraction() {
    return find_fraction<Chars...>(4);
  }

  template <char, char... Chars>
  static constexpr int find_oct_fraction() {
    if constexpr (sizeof...(Chars) == 0) {  // Literal is just `0`.
      return 0;
    } else {
      return find_fraction<Chars...>(3);
    }
  }

  template <char, char, char... Chars>
  static constexpr int find_bin_fraction() {
    return find_fraction<Chars...>(1);
  }

  struct DecimalPieces {
    int begin, point, end, exp;
  };

  static constexpr DecimalPieces decimal_pieces(const char* const arr,
                                                const char* const end) {
    enum State {
      kInteger = 0,
      kFraction = 1,
      kExponentSign = 2,
      kExponent = 3,
    };
    State state = kInteger;
    int exp_sign = 0;
    int exp = 0;
    bool zero = true;
    const char* begin = arr, *point = nullptr, *e = nullptr;
    for (const char* it = arr; it != end; ++it) {
      const char c = *it;
      switch (state) {
      case kInteger:
        if (c == 'e' || c == 'E') {
          state = kExponentSign;
          e = it;
          continue;
        }
        if (c == '.') {
          state = kFraction;
          point = it;
          continue;
        }
        if (zero && c != '0') {
          zero = false;
          begin = it;
        }
        continue;
      case kFraction:
        if (c == 'e' || c == 'E') {
          state = kExponentSign;
          e = it;
          continue;
        }
        if (zero && c != '0') {
          zero = false;
          begin = it;
        }
        continue;
      case kExponentSign:
        state = kExponent;
        if (c == '-') { exp_sign = -1; continue; }
        exp_sign = 1;
        if (c == '+') continue;
        [[fallthrough]];
      case kExponent:
        exp = exp * 10 + c - '0';
        continue;
      }
    }
    if (zero) return {0, 0, 0, 0};

    exp *= exp_sign;
    if (!e) e = end;
    if (point) {
      while (e[-1] == '0') --e;
      exp -= e - point - 1;
    } else {
      point = e;
    }

    return {static_cast<int>(begin - arr), static_cast<int>(point - arr),
            static_cast<int>(e - arr), exp};
  }

  // Parses the integer portion of a decimal number, for values less than
  // 10^27.
  //
  // The result is a bitfield. The highest set bit is shifted off. The next
  // up to 31 bits are stored in the high 31 bits, and the following bit is
  // set if there are any further non-zero bits in the integer portion. The
  // low 32 bits indicate the non-negative exponent of the highest set bit,
  // which was shifted off.
  //   [implicit 1] 64 [integer bits] 33 [rest-non-zero] 32 [exponent] 0
  static constexpr uint64_t parse_decimal_integer_part_small(
      const char* const arr, int digits, DecimalPieces pieces) {
    // Note: This function is actually more complicated than for bigger values,
    // but doesn't require extended integers.

    // 19 decimal digits can fit in a uint64 before overflowing. However,
    // 10 has the low bit clear, which means digit*10^X cannot affect any
    // of the low X bits. Shifting out those bits then makes room for a few
    // more digits, repeating until 10^27 covers the full span.
    constexpr int digits_per_stage[] = {19, 5, 2, 1};
    bool shifted_nonzero = false;
    uint64_t bits = 0;
    uint64_t multiplier = 1;
    int stage = 0, stage_progress = 0;
    int shifts = 0;
    // Deal with a positive exponent.
    for (int e = 0; e < pieces.exp; ++e) {
      multiplier *= 10;
      if (++stage_progress == digits_per_stage[stage]) {
        multiplier >>= digits_per_stage[stage];
        shifts += digits_per_stage[stage];
        ++stage;
        stage_progress = 0;
      }
    }
    int pos = pieces.end;
    // Skip digits for a negative exponent.
    for (int e = pieces.exp; e < 0; ++e) {
      if (--pos == pieces.point) --pos;
    }
    while (pos > pieces.begin) {
      if (--pos == pieces.point) --pos;
      bits += (arr[pos] - '0') * multiplier;
      multiplier *= 10;
      if (++stage_progress == digits_per_stage[stage]) {
        if (bits & ((uint32_t{1} << digits_per_stage[stage]) - 1)) {
          shifted_nonzero = true;
        }
        bits >>= digits_per_stage[stage];
        multiplier >>= digits_per_stage[stage];
        shifts += digits_per_stage[stage];
        ++stage;
        stage_progress = 0;
      }
    }
    int lz = lzcnt(bits);
    bits <<= lz;
    bits <<= 1;
    if (bits & 0xFFFFFFFFU) shifted_nonzero = true;
    bits &= ~uint64_t{0xFFFFFFFFU};
    bits |= uint64_t{shifted_nonzero} << 32;
    uint32_t exp = 64 - 1 - lz + shifts;
    return bits | exp;
  }

  // Parses the integer portion of a decimal number, for values less than
  // 10^38.
  //
  // The result is a bitfield. The highest set bit is shifted off. The next
  // up to 31 bits are stored in the high 31 bits, and the following bit is
  // set if there are any further non-zero bits in the integer portion. The
  // low 32 bits indicate the non-negative exponent of the highest set bit,
  // which was shifted off.
  //   [implicit 1] 64 [integer bits] 33 [rest-non-zero] 32 [exponent] 0
  static constexpr uint64_t parse_decimal_integer_part_big(
      const char* const arr, int digits, DecimalPieces pieces) {
    // 19 decimal digits can fit in a uint64 before overflowing.
    constexpr int digits_per_stage = 19;
    uint64_t low = 0;
    uint64_t multiplier = 1;
    int stage = 0, stage_progress = 0;
    // Deal with a positive exponent.
    for (int e = 0; e < pieces.exp; ++e) {
      multiplier *= 10;
      if (++stage_progress == digits_per_stage) {
        ++stage;
        stage_progress = 0;
      }
    }
    int pos = pieces.end;
    // Skip digits for a negative exponent.
    for (int e = pieces.exp; e < 0; ++e) {
      if (--pos == pieces.point) --pos;
    }
    if (stage == 0) {
      while (pos > pieces.begin) {
        if (--pos == pieces.point) --pos;
        digits += (arr[pos] - '0') * multiplier;
        multiplier *= 10;
        if (++stage_progress == digits_per_stage) {
          break;
        }
      }
    }
    uint64_t high = 0;
    multiplier = 1;
    stage_progress = 0;
    if (pos > pieces.begin) {
      while (pos > pieces.begin) {
        if (--pos == pieces.point) --pos;
        high += (arr[pos] - '0') * multiplier;
        multiplier *= 10;
      }
      unsigned __int128 product =
          static_cast<unsigned __int128>(high) *
          (unsigned __int128){10'000'000'000'000'000'000U};
      uint64_t carry = 0;
      low = builtin_addc(low, static_cast<uint64_t>(product), 0, &carry);
      high = static_cast<uint64_t>(product >> 64) + carry;
    }
    uint64_t bits = high | (low != 0);
    int highbit = 128 - 1;
    if (high == 0) {
      bits = low;
      highbit = 64 - 1;
    }
    int lz = lzcnt(bits);
    bits <<= lz;
    bits <<= 1;
    bool drop_nonzero = (bits & 0xFFFFFFFFU) != 0;
    bits &= ~uint64_t{0xFFFFFFFFU};
    bits |= uint64_t{drop_nonzero} << 32;
    uint32_t exp = highbit - lz;
    return bits | exp;
  }

  static constexpr int decimal_fraction_rounds(int fraction_digits) {
    return (fraction_digits + 11) / 12;
  }

  // Parses the fraction part of a decimal number with an integer part.
  // Returns at least the requested number of bits left-aligned, with the low
  // bit set if there are non-zero bits after the needed portion.
  template <int max_rounds>
  static constexpr uint32_t parse_decimal_fraction_part(
      const char* const arr, int needed_bits, int pos, int point, int end) {
    // 0.1 in binary has 3 leading zero bits, so each decimal digit gives 3
    // more bits that can't be directly touched by later digits. However, they
    // can be affected indirectly via carry, so a trailing series of one bits
    // could overflow into the preceeding zero. Thus, it is necessary to find
    // the first needed_bits bits, and then find a zero bit after that.
    //
    // 12 digits are processed at a time, producing up to 36 bits. To increase
    // the capacity of a uint64, a bit per digit is saved by shifting fewer
    // left and dividing by a power of 5 instead of 10. That is, the 2s from
    // the factorization of 10^12 are not shifted left, and so don't need to
    // be divided. This produces the same quotient, but the remainder will be
    // mod 5^12; shifting the remainder 12 to the left would produce the same
    // remainder as doing the math in base 10^12.
    constexpr uint32_t k5to12 = 244'140'625;
    constexpr uint64_t k10to12 = 1'000'000'000'000;
    uint32_t bits = 0;
    // At the beginning of round r, the first r remainder values could be
    // non-zero. remainder[i] contains a value that has been shifted i+1 times.
    uint64_t remainder[max_rounds] = {0};
    for (int round = 0; pos < end; ++round) {
      uint64_t dividend = 0;
      uint64_t multiplier = k10to12 / 10;
      for (; pos < end && multiplier > 0; ++pos, multiplier /= 10) {
        if (pos == point) { if (++pos == end) break; }
        dividend += static_cast<uint64_t>(arr[pos] - '0') * multiplier;
      }
      dividend <<= 24;
      uint64_t q = dividend / k5to12;
      uint64_t r = (dividend % k5to12) << 12;
      if (round == 0) {
        bits = q >> 4;  // 36 bits to 32
        bits |= (q & 0xF) != 0;
        uint64_t mask = (uint64_t{1} << (36 - needed_bits)) - 1;
        remainder[0] = r;
        if ((q & mask) != mask) break;  // Had a zero to catch carry.
      } else {
        for (int i = 0; i < round; ++i) {
          dividend = q + remainder[i];
          remainder[i] = r;
          if (dividend >= k10to12) {
            // Avoid overflow on the shift by skipping to the next division.
            remainder[i + 1] += uint64_t{1} << 36;
            dividend -= k10to12;
          }
          q <<= 24;
          q = dividend / k5to12;
          r = (dividend % k5to12) << 12;
        }
        // remainder[round] can only be non-zero if the dividend just
        // overflowed, in which case it is 1<<36 and therefore carries into the
        // upper bits.
        bool carry = remainder[round] > 0;
        remainder[round] = r;
        if (carry) {
          // Since the loop hasn't broken, all bits below the needed ones
          // were set. Thus, bits[0] is both set and will carry at least to
          // the lowest needed bit. This also clears the low bit, since the
          // carry has cleared every set bit outside the needed range.
          bits += 1;
          bits |= q != 0;
          // The carry created plenty of zero bits to catch future carries.
          break;
        }
        bits |= q != 0;
        if (q != (uint64_t{1} << 36) - 1) break;  // Had a zero to catch carry.
      }
    }
    if (pos < end) {
      // This indicates an early break due to having enough bits and knowing
      // the rest won't affect them. Since trailing zeroes were previously
      // dropped, it is known that there is at least one non-zero bit left,
      // so the last bit of the result should be set for rounding.
      bits |= 1;
    } else {
      // If any of the remainders are non-zero, then there are extra set bits
      // in unknown locations. Finding their exact locations is unimportant
      // because they cannot be in the first 32, and a remainder cannot carry
      // into upper bits without additional digits.
      for (int i = 0; i < max_rounds; ++i) {
        if (remainder[i] != 0) {
          bits |= 1;
          break;
        }
      }
    }
    return bits;
  }

  // Parses a decimal number with no integer part.
  //
  // The result is a bitfield. The highest set bit is shifted off. The next
  // up to 31 bits are stored in the high 31 bits, and the following bit is
  // set if there are any further non-zero bits. The low 32 bits indicate the
  // negation of the exponent of the highest set bit, which was shifted off.
  //   [implicit 1] 64 [fraction bits] 33 [rest-non-zero] 32 [-exponent] 0
  template <int max_rounds>
  static constexpr uint32_t parse_decimal_fraction_only(
      const char* const arr, int pos, int point, int end,
      int implicit_leading_zeroes) {
    // 0.1 in binary has 3 leading zero bits, so each decimal digit gives 3
    // more bits that can't be directly touched by later digits. However, they
    // can be affected indirectly via carry, so a trailing series of one bits
    // could overflow into the preceeding zero. Thus, it is necessary to find
    // the first needed_bits bits, and then find a zero bit after that.
    //
    // 12 digits are processed at a time, producing up to 36 bits. To increase
    // the capacity of a uint64, a bit per digit is saved by shifting fewer
    // left and dividing by a power of 5 instead of 10. That is, the 2s from
    // the factorization of 10^12 are not shifted left, and so don't need to
    // be divided. This produces the same quotient, but the remainder will be
    // mod 5^12; shifting the remainder 12 to the left would produce the same
    // remainder as doing the math in base 10^12.
    constexpr int kDigitsPerRound = 12;
    constexpr uint32_t k5to12 = 244'140'625;
    constexpr uint64_t k10to12 = 1'000'000'000'000;
    uint32_t bits = 0;
    int bits_needed = 32;
    int neg_exp = 0;
    // One extra round is added to ensure enough bits are available in the case
    // that few digits follow the first non-zero. In the worst case, where a
    // single 1 digit is the last in a round, it would produce no bits in the
    // first max_rounds rounds, but 33 bits in the extra remainder-only round.
    //
    // At the beginning of round r, the first r remainder values could be
    // non-zero. remainder[i] contains a value that has been shifted i+1 times.
    uint64_t remainder[max_rounds + 1] = {0};
    int round = implicit_leading_zeroes / kDigitsPerRound;
    implicit_leading_zeroes %= kDigitsPerRound;
    for (; pos < end || (bits_needed > 0 && round <= max_rounds); ++round) {
      uint64_t dividend = 0;
      uint64_t multiplier = k10to12 / 10;
      for (; implicit_leading_zeroes > 0; --implicit_leading_zeroes) {
        multiplier /= 10;
      }
      for (; pos < end && multiplier > 0; ++pos, multiplier /= 10) {
        if (pos == point) { if (++pos == end) break; }
        dividend += static_cast<uint64_t>(arr[pos] - '0') * multiplier;
      }
      dividend <<= 24;
      uint64_t q = dividend / k5to12;
      uint64_t r = (dividend % k5to12) << 12;
      bool carry = false;
      for (int i = 0; i < round; ++i) {
        dividend = q + remainder[i];
        remainder[i] = r;
        if (dividend >= k10to12) {
          // Avoid overflow on the shift by skipping to the next division.
          remainder[i + 1] += uint64_t{1} << 36;
          dividend -= k10to12;
        }
        dividend <<= 24;
        q = dividend / k5to12;
        r = (dividend % k5to12) << 12;
      }
      // remainder[round] can only be non-zero if the dividend just
      // overflowed, in which case it is 1<<36 and therefore carries into the
      // upper bits.
      carry = remainder[round] > 0;
      remainder[round] = r;

      if (bits_needed > 0) {
        if (q != 0) {
          int lz = lzcnt(q);
          int bits_avail = 64 - lz;
          if (bits == 0) {
            neg_exp = round * 36 + (lz - (64 - 36 - 1));
          }
          if (bits_avail >= bits_needed) {
            int extra = 36 - bits_needed;
            bits_needed = 0;
            bits |= static_cast<uint32_t>(q >> extra);
            // Shift off the implicit bit when the last bit is filled.
            bits <<= 1;
            uint64_t mask = (uint64_t{1} << extra) - 1;
            bits |= (q & mask) != 0;
            if ((q & mask) != mask) break;  // Had a zero to catch carry.
          } else {
            bits |= static_cast<uint32_t>(q << (bits_needed - bits_avail));
            bits_needed -= bits_avail;
          }
        }
      } else {
        if (carry) {
          // Since the loop hasn't broken, all bits below the needed ones
          // were set. Thus, either bits[0] is both set and will carry at
          // least to the lowest needed bit, or bits[0] is clear and bits[1] is
          // the lowest needed bit as the previous round produced exactly the
          // number of bits needed.
          if (bits & 1) {
            // This also clears the low bit, since the carry has cleared every
            // set bit outside the needed range.
            bits += 1;
            if (bits == 0) {
              // Carried all the way up to the implicit bit; shift the exponent.
              --neg_exp;
            }
            bits |= q != 0;
            // The carry created plenty of zero bits to catch future carries.
            break;
          } else {
            bits += 2;
            if (bits == 0) {
              // Carried all the way up to the implicit bit; shift the exponent.
              --neg_exp;
            }
            // The carry created no zeroes outside the non-needed bits, so
            // continue below with checking q for zeroes.
          }
        }
        bits |= q != 0;
        if (q != (uint64_t{1} << 36) - 1) break;  // Had a zero to catch carry.
      }
    }
    if (bits_needed > 0) {
      // Fewer bits than desired were available, so the implicit bit wasn't
      // shifted off in the loop.
      bits <<= 1;
    }
    if (pos < end) {
      // This indicates an early break due to having enough bits and knowing
      // the rest won't affect them. Since trailing zeroes were previously
      // dropped, it is known that there is at least one non-zero bit left,
      // so the last bit of the result should be set for rounding.
      bits |= 1;
    } else {
      // If any of the remainders are non-zero, then there are extra set bits
      // in unknown locations. Finding their exact locations is unimportant
      // because they cannot be in the first 32, and a remainder cannot carry
      // into upper bits without additional digits.
      for (int i = 0; i < max_rounds; ++i) {
        if (remainder[i] != 0) {
          bits |= 1;
          break;
        }
      }
    }
    return (static_cast<uint64_t>(bits) << 32) || neg_exp;
  }

  template <int MaxExp10, char... Chars>
  static constexpr decoded_posit<32> parse_decimal() {
    constexpr char arr[] = {Chars...};
    constexpr DecimalPieces pieces =
        decimal_pieces(&arr[0], &arr[sizeof...(Chars)]);
    constexpr int digits =
        pieces.end - pieces.begin - (pieces.begin <= pieces.point &&
                                     pieces.point < pieces.end);

    decoded_posit<32> dec{};
    dec.sign = 1;
    dec.fraction = 0;
    if constexpr (digits == 0) { dec.exponent = INT_MIN; return dec; }
    if constexpr (digits + pieces.exp - 1 > MaxExp10) {
      // Overflow.
      dec.exponent = PositTraits<32, 2>::MaxExp;
      return dec;
    }
    if constexpr (digits + pieces.exp > 0) {
      if constexpr (digits + pieces.exp <= 27) {
        constexpr uint64_t int_bits_result =
            parse_decimal_integer_part_small(arr, digits, pieces);
        dec.exponent = int_bits_result & 0xFFFFFFFFU;
        dec.fraction = int_bits_result >> 32;
      } else {
        constexpr uint64_t int_bits_result =
            parse_decimal_integer_part_big(arr, digits, pieces);
        dec.exponent = int_bits_result & 0xFFFFFFFFU;
        dec.fraction = int_bits_result >> 32;
      }
      if (pieces.exp >= 0 || (dec.fraction & 1)) {
        // The fraction can't modify any bits in the integer, so we already
        // have all the information we need.
        return dec;
      }
      // Since there is a fraction part this will end up within the array.
      int fraction_start = pieces.end + pieces.exp;
      if (fraction_start <= pieces.point && pieces.point < pieces.end) {
        --fraction_start;
      }
      if (dec.exponent >= 31) {
        // Just need to know if the fraction is non-zero.
        for (int i = fraction_start; i < pieces.end; ++i) {
          if (i == pieces.point) { if (++i == pieces.end) break; }
          if (arr[i] != '0') {
            dec.fraction |= 1;
            break;
          }
        }
        return dec;
      } else
          // This can only be reached if `pieces.exp < 0`, but will fail to
          // compile if >= 0. So the if-constexpr prevents it from being
          // instantiated at all in that case.
          if constexpr (pieces.exp < 0) {
        // At least one fraction bit needs to be returned.
        uint32_t frac_bits =
            parse_decimal_fraction_part<decimal_fraction_rounds(-pieces.exp)>(
                arr, 31 - dec.exponent, fraction_start, pieces.point,
                pieces.end);
        dec.fraction |= frac_bits >> dec.exponent;
        dec.fraction |= (frac_bits & ((uint32_t{1} << dec.exponent) - 1)) != 0;
        return dec;
      }
    } else {
      // There is no integer part.
      constexpr uint64_t bits =
          parse_decimal_fraction_only<decimal_fraction_rounds(-pieces.exp)>(
              arr, pieces.begin, pieces.point, pieces.end,
              -pieces.exp - digits);
      dec.exponent = -static_cast<int>(bits & 0xFFFFFFFFU);
      dec.fraction = bits >> 32;
      return dec;
    }
  }

  // Returns a decoded posit. `exponent` will be `INT_MIN` if the result should
  // be zero.
  template <typename Traits, char... Chars>
  static constexpr decoded_posit<Traits::SBits> parse_literal() noexcept {
    constexpr bool is_hex = literal_helper::is_hex<Chars...>();
    constexpr bool is_bin = literal_helper::is_bin<Chars...>();
    constexpr bool is_float =
        (... || (Chars == '.' ||
                 (!is_hex && (Chars == 'e' || Chars == 'E')) ||
                 (is_hex && (Chars == 'p' || Chars == 'P'))));
    constexpr bool is_oct =
        maybe_oct<Chars...>() && !is_hex && !is_bin && !is_float;
    decoded_posit<Traits::SBits> dec{};
    dec.sign = 1;
    if constexpr (is_hex) {
      dec.exponent = find_hex_exponent<Chars...>();
      dec.fraction = find_hex_fraction<Chars...>();
    } else if constexpr (is_bin) {
      dec.exponent = find_bin_exponent<Chars...>();
      dec.fraction = find_bin_fraction<Chars...>();
    } else if constexpr (is_oct) {
      dec.exponent = find_oct_exponent<Chars...>();
      dec.fraction = find_oct_fraction<Chars...>();
    } else {
      static_assert(Traits::NBits == 32 && Traits::ExpBits == 2,
                    "Decimal literals are only implemented for posit32.");
      return parse_decimal<Traits::ApproxMaxExp10, Chars...>();
    }
    return dec;
  }
};

template <char... Chars>
constexpr posit8 operator""_pos8() noexcept {
  // Built a 32-bit unrounded decoded posit, to reduce the amount of code, then
  // truncate the fraction.
  constexpr decoded_posit<32> dec32 =
      literal_helper::parse_literal<posit32::Traits, Chars...>();
  using Traits = posit8::Traits;
  constexpr decoded_posit<8> dec = {
      .sign = dec32.sign,
      .exponent = dec32.exponent,
      .fraction =
          static_cast<Traits::Unsigned>(dec32.fraction >> 24) |
          static_cast<Traits::Unsigned>((dec32.fraction & 0x00FFFFFFU) != 0),
  };
  constexpr typename Traits::Signed val =
      dec.exponent == INT_MIN
          ? Traits::kZero
          : encode_regular_posit<Traits::NBits, Traits::ExpBits>(dec);
  return posit8::WithBits(val);
}

template <char... Chars>
constexpr posit16 operator""_pos16() noexcept {
  // Built a 32-bit unrounded decoded posit, to reduce the amount of code, then
  // truncate the fraction.
  constexpr decoded_posit<32> dec32 =
      literal_helper::parse_literal<posit32::Traits, Chars...>();
  using Traits = posit16::Traits;
  constexpr decoded_posit<16> dec = {
      .sign = dec32.sign,
      .exponent = dec32.exponent,
      .fraction =
          static_cast<Traits::Unsigned>(dec32.fraction >> 16) |
          static_cast<Traits::Unsigned>((dec32.fraction & 0x0000FFFFU) != 0),
  };
  constexpr typename Traits::Signed val =
      dec.exponent == INT_MIN
          ? Traits::kZero
          : encode_regular_posit<Traits::NBits, Traits::ExpBits>(dec);
  return posit16::WithBits(val);
}

template <char... Chars>
constexpr posit32 operator""_pos32() noexcept {
  using Traits = posit32::Traits;
  constexpr decoded_posit<32> dec =
      literal_helper::parse_literal<Traits, Chars...>();
  constexpr typename Traits::Signed val =
      dec.exponent == INT_MIN
          ? Traits::kZero
          : encode_regular_posit<Traits::NBits, Traits::ExpBits>(dec);
  return posit32::WithBits(val);
}

// TODO: Larger literals.
template <char... Chars>
constexpr posit64 operator""_pos64() noexcept {
  using Traits32 = posit32::Traits;
  constexpr decoded_posit<32> dec32 =
      literal_helper::parse_literal<Traits32, Chars...>();
  using Traits = posit64::Traits;
  static_assert(dec32.exponent == INT_MIN ||
                (dec32.exponent < Traits32::MaxExp &&
                 dec32.exponent > Traits32::MinExp &&
                 (Traits::FractionBitsAtExponent(dec32.exponent) <= 30 ||
                  (dec32.fraction & 1) == 0)),
                "Posit literals larger than 32 bits are currently "
                "unimplemented, and will only work if decoding into 32 bits "
                "verifiably does not lose precision.");
  constexpr decoded_posit<64> dec = {
      .sign = dec32.sign,
      .exponent = dec32.exponent,
      .fraction = static_cast<Traits::Unsigned>(dec32.fraction) << 32,
  };
  using Traits = posit64::Traits;
  constexpr typename Traits::Signed val =
      dec.exponent == INT_MIN
          ? Traits::kZero
          : encode_regular_posit<Traits::NBits, Traits::ExpBits>(dec);
  return posit64::WithBits(val);
}

#if POSIT_HAS_INT128
template <char... Chars>
constexpr posit128 operator""_pos128() noexcept {
  using Traits32 = posit32::Traits;
  constexpr decoded_posit<32> dec32 =
      literal_helper::parse_literal<Traits32, Chars...>();
  using Traits = posit128::Traits;
  static_assert(dec32.exponent == INT_MIN ||
                (dec32.exponent < Traits32::MaxExp &&
                 dec32.exponent > Traits32::MinExp &&
                 (Traits::FractionBitsAtExponent(dec32.exponent) <= 30 ||
                  (dec32.fraction & 1) == 0)),
                "Posit literals larger than 32 bits are currently "
                "unimplemented, and will only work if decoding into 32 bits "
                "verifiably does not lose precision.");
  constexpr decoded_posit<128> dec = {
      .sign = dec32.sign,
      .exponent = dec32.exponent,
      .fraction = static_cast<Traits::Unsigned>(dec32.fraction) << 96,
  };
  constexpr typename Traits::Signed val =
      dec.exponent == INT_MIN
          ? Traits::kZero
          : encode_regular_posit<Traits::NBits, Traits::ExpBits>(dec);
  return posit128::WithBits(val);
}
#endif

// Heterogeneous operators, defined for types which are implicitly convertible
// to a posit. Without these, such operations would often be ambiguous between
// converting T to a posit and converting the posit to a fundamental type.

template <typename T, int N, int E>
inline constexpr bool PositConvertsFrom =
    conjunct<std::negation<std::is_same<posit<N, E>, T>>,
             std::is_convertible<T, posit<N, E>>>;

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator*(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) * p; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator*(posit<N, E> p, T t) noexcept {
    return p * posit<N, E>(t); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator/(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) / p; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator/(posit<N, E> p, T t) noexcept {
    return p / posit<N, E>(t); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator+(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) + p; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator+(posit<N, E> p, T t) noexcept {
    return p + posit<N, E>(t); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator-(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) - p; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr auto operator-(posit<N, E> p, T t) noexcept {
    return p - posit<N, E>(t); }

#if __has_feature(__cpp_impl_three_way_comparison)
// Only needs to be defined in one direction
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr std::strong_ordering operator<=>(posit<N, E> p, T t) noexcept {
    return p <=> posit<N, E>(t); }
#endif
#if !__has_feature(__cpp_impl_three_way_comparison) || !(__cpp_lib_three_way_comparison >= 201907L)
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator==(posit<N, E> p, T t) noexcept {
    return p == posit<N, E>(t); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator==(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) == p; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator!=(posit<N, E> p, T t) noexcept {
    return p != posit<N, E>(t); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator!=(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) != p; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator<(posit<N, E> p, T t) noexcept {
    return p < posit<N, E>(t); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator<(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) < p; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator>(posit<N, E> p, T t) noexcept {
    return p > posit<N, E>(t); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator>(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) > p; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator<=(posit<N, E> p, T t) noexcept {
    return p <= posit<N, E>(t); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator<=(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) <= p; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator>=(posit<N, E> p, T t) noexcept {
    return p >= posit<N, E>(t); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsFrom<T, N, E>>* = nullptr>
constexpr bool operator>=(T t, posit<N, E> p) noexcept {
    return posit<N, E>(t) >= p; }
#endif

// Heterogeneous operators, defined for types which a posit is implicitly
// convertible to (but which aren't convertible back). Without these, such
// operations would often be ambiguous as the posit could convert to the
// target, or some other fundamental type that can be operated on with the
// target.

template <typename T, int N, int E>
inline constexpr bool PositConvertsOnlyTo =
    conjunct<std::negation<IsPosit<T>>,
             std::negation<std::is_convertible<T, posit<N, E>>>,
             std::is_convertible<posit<N, E>, T>>;

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator*(T t, posit<N, E> p) noexcept {
    return t * T(p); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator*(posit<N, E> p, T t) noexcept {
    return T(p) * t; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator/(T t, posit<N, E> p) noexcept {
    return t / T(p); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator/(posit<N, E> p, T t) noexcept {
    return T(p) / t; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator+(T t, posit<N, E> p) noexcept {
    return t + T(p); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator+(posit<N, E> p, T t) noexcept {
    return T(p) + t; }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator-(T t, posit<N, E> p) noexcept {
    return t - T(p); }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr auto operator-(posit<N, E> p, T t) noexcept {
    return T(p) - t; }

#if __has_feature(__cpp_impl_three_way_comparison)
// Only needs to be defined in one direction
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr std::strong_ordering operator<=>(posit<N, E> p, T t) noexcept {
    return T(p) <=> t; }
#endif
#if !__has_feature(__cpp_impl_three_way_comparison) || !(__cpp_lib_three_way_comparison >= 201907L)
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator==(posit<N, E> p, T t) noexcept {
    return T(p) == t; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator==(T t, posit<N, E> p) noexcept {
    return t == T(p); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator!=(posit<N, E> p, T t) noexcept {
    return T(p) != t; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator!=(T t, posit<N, E> p) noexcept {
    return t != T(p); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator<(posit<N, E> p, T t) noexcept {
    return T(p) < t; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator<(T t, posit<N, E> p) noexcept {
    return t < T(p); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator>(posit<N, E> p, T t) noexcept {
    return T(p) > t; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator>(T t, posit<N, E> p) noexcept {
    return t > T(p); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator<=(posit<N, E> p, T t) noexcept {
    return T(p) <= t; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator<=(T t, posit<N, E> p) noexcept {
    return t <= T(p); }

template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator>=(posit<N, E> p, T t) noexcept {
    return T(p) >= t; }
template <typename T, int N, int E,
          enable_if_t<PositConvertsOnlyTo<T, N, E>>* = nullptr>
constexpr bool operator>=(T t, posit<N, E> p) noexcept {
    return t >= T(p); }
#endif

// Heterogeneous operators, to force conversion of mult_intermediates to
// posits. The above operators will already handle cases where one of the
// operands is the mult_intermediate's corresponding posit type, so only other
// cases are handled here. If both parameters are mult_intermediates, the
// second one is converted to a posit first.

template <typename T, int N, int E>
constexpr auto operator*(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) * posit<N, E>())> {
    return static_cast<T&&>(t) *
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator*(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() * static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) *
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator/(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) / posit<N, E>())> {
    return static_cast<T&&>(t) /
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator/(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() / static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) /
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator+(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) + posit<N, E>())> {
    return static_cast<T&&>(t) +
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator+(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() + static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) +
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator-(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) - posit<N, E>())> {
    return static_cast<T&&>(t) -
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator-(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() - static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) -
        static_cast<T&&>(t); }

#if __has_feature(__cpp_impl_three_way_comparison)
// Only needs to be defined in one direction
template <typename T, int N, int E>
constexpr auto operator<=>(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) <=> posit<N, E>())> {
    return static_cast<T&&>(t) <=>
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
#endif
#if !__has_feature(__cpp_impl_three_way_comparison) || !(__cpp_lib_three_way_comparison >= 201907L)
template <typename T, int N, int E>
constexpr auto operator==(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) == posit<N, E>())> {
    return static_cast<T&&>(t) ==
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator==(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() == static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) ==
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator!=(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) != posit<N, E>())> {
    return static_cast<T&&>(t) !=
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator!=(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() != static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) !=
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator<(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) < posit<N, E>())> {
    return static_cast<T&&>(t) <
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator<(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() < static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) <
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator>(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) > posit<N, E>())> {
    return static_cast<T&&>(t) >
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator>(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() > static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) >
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator<=(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) <= posit<N, E>())> {
    return static_cast<T&&>(t) <=
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator<=(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() <= static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) <=
        static_cast<T&&>(t); }

template <typename T, int N, int E>
constexpr auto operator>=(T t, posit_mult_intermediate<N, E> p) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T>,
                   decltype(static_cast<T&&>(t) >= posit<N, E>())> {
    return static_cast<T&&>(t) >=
        posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)); }
template <typename T, int N, int E>
constexpr auto operator>=(posit_mult_intermediate<N, E> p, T t) noexcept
    -> enable_if_t<!std::is_same_v<posit<N, E>, T> &&
                       !IsPositMultIntermediate<T>::value,
                   decltype(posit<N, E>() >= static_cast<T&&>(t))> {
    return posit<N, E>(static_cast<posit_mult_intermediate<N, E>&&>(p)) >=
        static_cast<T&&>(t); }
#endif

template <int N, int E>
class std::numeric_limits<posit<N, E>> {
 private:
  using Traits = PositTraits<N, E>;

  static constexpr long double log10_2 =
      0x0.4D104D427DE7FBCC47C4ACD605BE48BCp0L;

  // Because the standard library's version isn't constexpr
  static constexpr int ceil(long double v) noexcept {
    int x = v;
    if (static_cast<long double>(x) < v) ++x;
    return x;
  }

 public:
  static constexpr bool is_specialized = true;
  static constexpr bool is_signed = true;
  static constexpr bool is_integer = false;
  static constexpr bool is_exact = false;
  static constexpr bool has_infinity = false;
  static constexpr bool has_quiet_NaN = true;
  static constexpr bool has_signaling_NaN = false;
  static constexpr std::float_denorm_style has_denorm = std::denorm_absent;
  static constexpr bool has_denorm_loss = false;
  static constexpr std::float_round_style round_style = std::round_to_nearest;
  static constexpr bool is_iec559 = false;
  static constexpr bool is_bounded = true;
  static constexpr bool is_modulo = false;
  static constexpr bool traps = false;
  // Nothing should ever round to zero.
  static constexpr bool tinyness_before = true;

  static constexpr int radix = 2;
  static constexpr int digits = Traits::MaxFractionBits + 1;
  static constexpr int min_exponent = Traits::MinExp + 1;
  static constexpr int max_exponent = Traits::MaxExp + 1;
  static constexpr int digits_at_exponent(int exponent) noexcept {
    return Traits::FractionBitsAtExponent(exponent) + 1;
  }
  // `digits10` is defined by the ability to round-trip from text->type->text.
  // Near ±1.0, values with `(digits - 1) * log10(2)` decimal digits will
  // round-trip successfully, but this degrades to less than a digit near the
  // limits of the representable values.
  static constexpr int digits10 = 0;
  // `max_digits10` is defined by the ability to round-trip from
  // type->text->type.
  static constexpr int max_digits10 = ceil(digits * log10_2) + 1;
  // Assuming long double has at least 64 bits of precision, this should
  // produce the correct result for any signed 32-bit integer MaxExp.
  static constexpr int max_exponent10 = Traits::MaxExp * log10_2;
  static constexpr int min_exponent10 = -max_exponent10;

  static constexpr posit<N, E> max() noexcept { return posit<N, E>::Max(); }
  static constexpr posit<N, E> min() noexcept { return posit<N, E>::Min(); }
  static constexpr posit<N, E> denorm_min() noexcept { return min(); }
  static constexpr posit<N, E> lowest() noexcept { return -max(); }
  static constexpr posit<N, E> epsilon() noexcept {
    if constexpr (Traits::UncappedMaxFractionBits >= 0) {
      // The posit 1 has the maximum fraction bits, so the next posit after it
      // is 1 + 2^-MaxFractionBits and epsilon is 2^-MaxFractionBits.
      // imprecise_inverse() is always exact for (representable) powers of 2.
      return posit<N, E>(
          typename Traits::Unsigned{1} << Traits::MaxFractionBits)
          .imprecise_inverse();
    } else {
      // At least one exponent bit is truncated even for the representation of
      // 1. This means the next posit after 1 is 2^(2^LostBits), and the
      // difference will round back to that value.
      return nextafter(posit<N, E>::One(), posit<N, E>::Max());
    }
  }
  static constexpr posit<N, E> round_error() noexcept {
    if constexpr (Traits::MaxFractionBits > 0) {
      // One half.
      return posit<N, E>{2}.imprecise_inverse();
    } else {
      // The smallest non-zero posit.
      return posit<N, E>::One();
    }
  }
  static constexpr posit<N, E> infinity() noexcept {
    // Officially this function is not meaningful since has_infinity = false.
    // Returning a real value allows e.g. `nextafter(x, infinity())` to work,
    // and many operations on the max would return the max, so it's not the
    // worst approximation.
    return posit<N, E>::Max();
  }
  static constexpr posit<N, E> quiet_NaN() noexcept {
    return posit<N, E>::NaR();
  }
  static constexpr posit<N, E> signaling_NaN() noexcept {
    return posit<N, E>::NaR();
  }
};

#ifndef POSIT_HEADER_ONLY
extern template struct PositByStorage<8>;
extern template struct PositByStorage<16>;
extern template struct PositByStorage<32>;
extern template struct PositByStorage<64>;

extern template PositByStorage<8>::FromFloatPrecheckResult
PositByStorage<8>::FromFloatPrecheck(float) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromFloat(float) noexcept;
extern template float PositByStorage<8>::ToFloat(decoded_posit<8>) noexcept;
extern template PositByStorage<8>::FromFloatPrecheckResult
PositByStorage<8>::FromFloatPrecheck(double) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromFloat(double) noexcept;
extern template double PositByStorage<8>::ToFloat(decoded_posit<8>) noexcept;
extern template PositByStorage<8>::FromFloatPrecheckResult
PositByStorage<8>::FromFloatPrecheck(long double) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromFloat(long double)
    noexcept;
extern template long double PositByStorage<8>::ToFloat(decoded_posit<8>)
    noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromInt(int) noexcept;
extern template int PositByStorage<8>::ToInt(decoded_posit<8> dec) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromInt(long) noexcept;
extern template long PositByStorage<8>::ToInt(decoded_posit<8> dec) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromInt(long long) noexcept;
extern template long long PositByStorage<8>::ToInt(decoded_posit<8> dec)
    noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromInt(
    unsigned int) noexcept;
extern template unsigned int PositByStorage<8>::ToInt(
    decoded_posit<8> dec) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromInt(
    unsigned long) noexcept;
extern template unsigned long PositByStorage<8>::ToInt(
    decoded_posit<8> dec) noexcept;
extern template decoded_posit<8> PositByStorage<8>::FromInt(
    unsigned long long) noexcept;
extern template unsigned long long PositByStorage<8>::ToInt(
    decoded_posit<8> dec) noexcept;
extern template decoded_posit<8> PositByStorage<8>::DivideImpl<0>(
    decoded_posit<8> n, decoded_posit<8> d) noexcept;
// Not instantiating Divide(), as it's a fairly small wrapper depending on an
// exact posit, and so will likely be inlined into positN's operator/().

extern template PositByStorage<16>::FromFloatPrecheckResult
PositByStorage<16>::FromFloatPrecheck(float) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromFloat(float) noexcept;
extern template float PositByStorage<16>::ToFloat(decoded_posit<16>) noexcept;
extern template PositByStorage<16>::FromFloatPrecheckResult
PositByStorage<16>::FromFloatPrecheck(double) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromFloat(double)
    noexcept;
extern template double PositByStorage<16>::ToFloat(decoded_posit<16>) noexcept;
extern template PositByStorage<16>::FromFloatPrecheckResult
PositByStorage<16>::FromFloatPrecheck(long double) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromFloat(long double)
    noexcept;
extern template long double PositByStorage<16>::ToFloat(decoded_posit<16>)
    noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromInt(int) noexcept;
extern template int PositByStorage<16>::ToInt(decoded_posit<16> dec) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromInt(long) noexcept;
extern template long PositByStorage<16>::ToInt(decoded_posit<16> dec) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromInt(long long)
    noexcept;
extern template long long PositByStorage<16>::ToInt(decoded_posit<16> dec)
    noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromInt(
    unsigned int) noexcept;
extern template unsigned int PositByStorage<16>::ToInt(
    decoded_posit<16> dec) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromInt(
    unsigned long) noexcept;
extern template unsigned long PositByStorage<16>::ToInt(
    decoded_posit<16> dec) noexcept;
extern template decoded_posit<16> PositByStorage<16>::FromInt(
    unsigned long long) noexcept;
extern template unsigned long long PositByStorage<16>::ToInt(
    decoded_posit<16> dec) noexcept;
extern template decoded_posit<16> PositByStorage<16>::DivideImpl<0>(
    decoded_posit<16> n, decoded_posit<16> d) noexcept;

extern template PositByStorage<32>::FromFloatPrecheckResult
PositByStorage<32>::FromFloatPrecheck(float) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromFloat(float) noexcept;
extern template float PositByStorage<32>::ToFloat(decoded_posit<32>) noexcept;
extern template PositByStorage<32>::FromFloatPrecheckResult
PositByStorage<32>::FromFloatPrecheck(double) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromFloat(double)
    noexcept;
extern template double PositByStorage<32>::ToFloat(decoded_posit<32>) noexcept;
extern template PositByStorage<32>::FromFloatPrecheckResult
PositByStorage<32>::FromFloatPrecheck(long double) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromFloat(long double)
    noexcept;
extern template long double PositByStorage<32>::ToFloat(decoded_posit<32>)
    noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromInt(int) noexcept;
extern template int PositByStorage<32>::ToInt(decoded_posit<32> dec) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromInt(long) noexcept;
extern template long PositByStorage<32>::ToInt(decoded_posit<32> dec) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromInt(long long)
    noexcept;
extern template long long PositByStorage<32>::ToInt(decoded_posit<32> dec)
    noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromInt(
    unsigned int) noexcept;
extern template unsigned int PositByStorage<32>::ToInt(
    decoded_posit<32> dec) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromInt(
    unsigned long) noexcept;
extern template unsigned long PositByStorage<32>::ToInt(
    decoded_posit<32> dec) noexcept;
extern template decoded_posit<32> PositByStorage<32>::FromInt(
    unsigned long long) noexcept;
extern template unsigned long long PositByStorage<32>::ToInt(
    decoded_posit<32> dec) noexcept;
extern template decoded_posit<32> PositByStorage<32>::DivideImpl<0>(
    decoded_posit<32> n, decoded_posit<32> d) noexcept;

extern template PositByStorage<64>::FromFloatPrecheckResult
PositByStorage<64>::FromFloatPrecheck(float) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromFloat(float) noexcept;
extern template float PositByStorage<64>::ToFloat(decoded_posit<64>) noexcept;
extern template PositByStorage<64>::FromFloatPrecheckResult
PositByStorage<64>::FromFloatPrecheck(double) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromFloat(double)
    noexcept;
extern template double PositByStorage<64>::ToFloat(decoded_posit<64>) noexcept;
extern template PositByStorage<64>::FromFloatPrecheckResult
PositByStorage<64>::FromFloatPrecheck(long double) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromFloat(long double)
    noexcept;
extern template long double PositByStorage<64>::ToFloat(decoded_posit<64>)
    noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromInt(int) noexcept;
extern template int PositByStorage<64>::ToInt(decoded_posit<64> dec) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromInt(long) noexcept;
extern template long PositByStorage<64>::ToInt(decoded_posit<64> dec) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromInt(long long)
    noexcept;
extern template long long PositByStorage<64>::ToInt(decoded_posit<64> dec)
    noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromInt(
    unsigned int) noexcept;
extern template unsigned int PositByStorage<64>::ToInt(
    decoded_posit<64> dec) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromInt(
    unsigned long) noexcept;
extern template unsigned long PositByStorage<64>::ToInt(
    decoded_posit<64> dec) noexcept;
extern template decoded_posit<64> PositByStorage<64>::FromInt(
    unsigned long long) noexcept;
extern template unsigned long long PositByStorage<64>::ToInt(
    decoded_posit<64> dec) noexcept;
#if POSIT_HAS_INT128
extern template decoded_posit<64> PositByStorage<64>::DivideImpl<0>(
    decoded_posit<64> n, decoded_posit<64> d) noexcept;
#else
extern template decoded_posit<64> PositByStorage<64>::DivideImpl<58>(
    decoded_posit<64> n, decoded_posit<64> d) noexcept;
#endif
#if POSIT_HAS_INT128
extern template PositByStorage<128>::FromFloatPrecheckResult
PositByStorage<128>::FromFloatPrecheck(float) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromFloat(float)
    noexcept;
extern template float PositByStorage<128>::ToFloat(decoded_posit<128>) noexcept;
extern template PositByStorage<128>::FromFloatPrecheckResult
PositByStorage<128>::FromFloatPrecheck(double) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromFloat(double)
    noexcept;
extern template double PositByStorage<128>::ToFloat(decoded_posit<128>)
    noexcept;
extern template PositByStorage<128>::FromFloatPrecheckResult
PositByStorage<128>::FromFloatPrecheck(long double) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromFloat(long double)
    noexcept;
extern template long double PositByStorage<128>::ToFloat(decoded_posit<128>)
    noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(int) noexcept;
extern template int PositByStorage<128>::ToInt(decoded_posit<128> dec) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(long) noexcept;
extern template long PositByStorage<128>::ToInt(decoded_posit<128> dec)
    noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(long long)
    noexcept;
extern template long long PositByStorage<128>::ToInt(decoded_posit<128> dec)
    noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(__int128)
    noexcept;
extern template __int128 PositByStorage<128>::ToInt(decoded_posit<128> dec)
    noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(
    unsigned int) noexcept;
extern template unsigned int PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(
    unsigned long) noexcept;
extern template unsigned long PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(
    unsigned long long) noexcept;
extern template unsigned long long PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
extern template decoded_posit<128> PositByStorage<128>::FromInt(unsigned __int128)
    noexcept;
extern template unsigned __int128 PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
extern template decoded_posit<128> PositByStorage<128>::DivideImpl<121>(
    decoded_posit<128> n, decoded_posit<128> d) noexcept;
#endif

extern template class posit<8, 0>;
extern template class posit<16, 1>;
extern template class posit<32, 2>;
extern template class posit<64, 3>;
extern template class quire<12, 7>;
extern template class quire<56, 15>;
extern template class quire<240, 31>;
extern template class quire<992, 63>;
extern template class posit_mult_intermediate<8, 0>;
extern template class posit_mult_intermediate<16, 1>;
extern template class posit_mult_intermediate<32, 2>;
extern template class posit_mult_intermediate<64, 3>;
#if POSIT_HAS_INT128
extern template class posit<128, 4>;
extern template class quire<4032, 127>;
extern template class posit_mult_intermediate<128, 4>;
#endif

extern template posit<8, 0>::posit(float) noexcept;
extern template posit<8, 0>::posit(double) noexcept;
extern template posit<8, 0>::posit(long double) noexcept;
extern template posit<8, 0>::posit(int) noexcept;
extern template posit<8, 0>::posit(long) noexcept;
extern template posit<8, 0>::posit(long long) noexcept;
extern template posit<8, 0>::posit(unsigned) noexcept;
extern template posit<8, 0>::posit(unsigned long) noexcept;
extern template posit<8, 0>::posit(unsigned long long) noexcept;
extern template posit<8, 0>::operator float() const noexcept;
extern template posit<8, 0>::operator double() const noexcept;
extern template posit<8, 0>::operator long double() const noexcept;
extern template posit<8, 0>::operator int() const noexcept;
extern template posit<8, 0>::operator long() const noexcept;
extern template posit<8, 0>::operator long long() const noexcept;
extern template posit<8, 0>::operator unsigned() const noexcept;
extern template posit<8, 0>::operator unsigned long() const noexcept;
extern template posit<8, 0>::operator unsigned long long() const noexcept;
extern template posit<8, 0>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
extern template posit<16, 1>::posit(posit<8, 0>) noexcept;
extern template posit<16, 1>::posit(float) noexcept;
extern template posit<16, 1>::posit(double) noexcept;
extern template posit<16, 1>::posit(long double) noexcept;
extern template posit<16, 1>::posit(int) noexcept;
extern template posit<16, 1>::posit(long) noexcept;
extern template posit<16, 1>::posit(long long) noexcept;
extern template posit<16, 1>::posit(unsigned) noexcept;
extern template posit<16, 1>::posit(unsigned long) noexcept;
extern template posit<16, 1>::posit(unsigned long long) noexcept;
extern template posit<16, 1>::operator float() const noexcept;
extern template posit<16, 1>::operator double() const noexcept;
extern template posit<16, 1>::operator long double() const noexcept;
extern template posit<16, 1>::operator int() const noexcept;
extern template posit<16, 1>::operator long() const noexcept;
extern template posit<16, 1>::operator long long() const noexcept;
extern template posit<16, 1>::operator unsigned() const noexcept;
extern template posit<16, 1>::operator unsigned long() const noexcept;
extern template posit<16, 1>::operator unsigned long long() const noexcept;
extern template posit<16, 1>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
extern template posit<32, 2>::posit(posit<8, 0>) noexcept;
extern template posit<32, 2>::posit(posit<16, 1>) noexcept;
extern template posit<32, 2>::posit(float) noexcept;
extern template posit<32, 2>::posit(double) noexcept;
extern template posit<32, 2>::posit(long double) noexcept;
extern template posit<32, 2>::posit(int) noexcept;
extern template posit<32, 2>::posit(long) noexcept;
extern template posit<32, 2>::posit(long long) noexcept;
extern template posit<32, 2>::posit(unsigned) noexcept;
extern template posit<32, 2>::posit(unsigned long) noexcept;
extern template posit<32, 2>::posit(unsigned long long) noexcept;
extern template posit<32, 2>::operator float() const noexcept;
extern template posit<32, 2>::operator double() const noexcept;
extern template posit<32, 2>::operator long double() const noexcept;
extern template posit<32, 2>::operator int() const noexcept;
extern template posit<32, 2>::operator long() const noexcept;
extern template posit<32, 2>::operator long long() const noexcept;
extern template posit<32, 2>::operator unsigned() const noexcept;
extern template posit<32, 2>::operator unsigned long() const noexcept;
extern template posit<32, 2>::operator unsigned long long() const noexcept;
extern template posit<32, 2>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
extern template posit<64, 3>::posit(posit<8, 0>) noexcept;
extern template posit<64, 3>::posit(posit<16, 1>) noexcept;
extern template posit<64, 3>::posit(posit<32, 2>) noexcept;
extern template posit<64, 3>::posit(float) noexcept;
extern template posit<64, 3>::posit(double) noexcept;
extern template posit<64, 3>::posit(long double) noexcept;
extern template posit<64, 3>::posit(int) noexcept;
extern template posit<64, 3>::posit(long) noexcept;
extern template posit<64, 3>::posit(long long) noexcept;
extern template posit<64, 3>::posit(unsigned) noexcept;
extern template posit<64, 3>::posit(unsigned long) noexcept;
extern template posit<64, 3>::posit(unsigned long long) noexcept;
extern template posit<64, 3>::operator float() const noexcept;
extern template posit<64, 3>::operator double() const noexcept;
extern template posit<64, 3>::operator long double() const noexcept;
extern template posit<64, 3>::operator int() const noexcept;
extern template posit<64, 3>::operator long() const noexcept;
extern template posit<64, 3>::operator long long() const noexcept;
extern template posit<64, 3>::operator unsigned() const noexcept;
extern template posit<64, 3>::operator unsigned long() const noexcept;
extern template posit<64, 3>::operator unsigned long long() const noexcept;
extern template posit<64, 3>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
#if POSIT_HAS_INT128
extern template posit<128, 4>::posit(posit<8, 0>) noexcept;
extern template posit<128, 4>::posit(posit<16, 1>) noexcept;
extern template posit<128, 4>::posit(posit<32, 2>) noexcept;
extern template posit<128, 4>::posit(posit<64, 3>) noexcept;
extern template posit<128, 4>::posit(float) noexcept;
extern template posit<128, 4>::posit(double) noexcept;
extern template posit<128, 4>::posit(long double) noexcept;
extern template posit<128, 4>::posit(int) noexcept;
extern template posit<128, 4>::posit(long) noexcept;
extern template posit<128, 4>::posit(long long) noexcept;
extern template posit<128, 4>::posit(__int128) noexcept;
extern template posit<128, 4>::posit(unsigned) noexcept;
extern template posit<128, 4>::posit(unsigned long) noexcept;
extern template posit<128, 4>::posit(unsigned long long) noexcept;
extern template posit<128, 4>::posit(unsigned __int128) noexcept;
extern template posit<128, 4>::operator float() const noexcept;
extern template posit<128, 4>::operator double() const noexcept;
extern template posit<128, 4>::operator long double() const noexcept;
extern template posit<128, 4>::operator int() const noexcept;
extern template posit<128, 4>::operator long() const noexcept;
extern template posit<128, 4>::operator long long() const noexcept;
extern template posit<128, 4>::operator __int128() const noexcept;
extern template posit<128, 4>::operator unsigned() const noexcept;
extern template posit<128, 4>::operator unsigned long() const noexcept;
extern template posit<128, 4>::operator unsigned long long() const noexcept;
extern template posit<128, 4>::operator unsigned __int128() const noexcept;
extern template posit<128, 4>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
#endif

extern template posit_mult_intermediate<8, 0> operator*(
    posit<8, 0> lhs, posit<8, 0> rhs) noexcept;
extern template posit<8, 0> operator/(
    posit<8, 0> n, posit<8, 0> d) noexcept;
extern template posit<8, 0> operator+(
    posit<8, 0> lhs, posit<8, 0> rhs) noexcept;
extern template posit<8, 0> operator-(
    posit<8, 0> lhs, posit<8, 0> rhs) noexcept;
extern template posit_mult_intermediate<16, 1> operator*(
    posit<16, 1> lhs, posit<16, 1> rhs) noexcept;
extern template posit<16, 1> operator/(
    posit<16, 1> n, posit<16, 1> d) noexcept;
extern template posit<16, 1> operator+(
    posit<16, 1> lhs, posit<16, 1> rhs) noexcept;
extern template posit<16, 1> operator-(
    posit<16, 1> lhs, posit<16, 1> rhs) noexcept;
extern template posit_mult_intermediate<32, 2> operator*(
    posit<32, 2> lhs, posit<32, 2> rhs) noexcept;
extern template posit<32, 2> operator/(
    posit<32, 2> n, posit<32, 2> d) noexcept;
extern template posit<32, 2> operator+(
    posit<32, 2> lhs, posit<32, 2> rhs) noexcept;
extern template posit<32, 2> operator-(
    posit<32, 2> lhs, posit<32, 2> rhs) noexcept;
extern template posit_mult_intermediate<64, 3> operator*(
    posit<64, 3> lhs, posit<64, 3> rhs) noexcept;
extern template posit<64, 3> operator/(
    posit<64, 3> n, posit<64, 3> d) noexcept;
extern template posit<64, 3> operator+(
    posit<64, 3> lhs, posit<64, 3> rhs) noexcept;
extern template posit<64, 3> operator-(
    posit<64, 3> lhs, posit<64, 3> rhs) noexcept;
#if POSIT_HAS_INT128
extern template posit_mult_intermediate<128, 4> operator*(
    posit<128, 4> lhs, posit<128, 4> rhs) noexcept;
extern template posit<128, 4> operator/(
    posit<128, 4> n, posit<128, 4> d) noexcept;
extern template posit<128, 4> operator+(
    posit<128, 4> lhs, posit<128, 4> rhs) noexcept;
extern template posit<128, 4> operator-(
    posit<128, 4> lhs, posit<128, 4> rhs) noexcept;
#endif

extern template posit<8, 0> nextafter(
    posit<8, 0> from, posit<8, 0> to) noexcept;
extern template posit<8, 0> nexttoward(
    posit<8, 0> from, long double to) noexcept;
extern template posit<8, 0> nexttoward(
    posit<8, 0> from, posit<64, 3> to) noexcept;
extern template posit<16, 1> nextafter(
    posit<16, 1> from, posit<16, 1> to) noexcept;
extern template posit<16, 1> nexttoward(
    posit<16, 1> from, long double to) noexcept;
extern template posit<16, 1> nexttoward(
    posit<16, 1> from, posit<64, 3> to) noexcept;
extern template posit<32, 2> nextafter(
    posit<32, 2> from, posit<32, 2> to) noexcept;
extern template posit<32, 2> nexttoward(
    posit<32, 2> from, long double to) noexcept;
extern template posit<32, 2> nexttoward(
    posit<32, 2> from, posit<64, 3> to) noexcept;
extern template posit<64, 3> nextafter(
    posit<64, 3> from, posit<64, 3> to) noexcept;
extern template posit<64, 3> nexttoward(
    posit<64, 3> from, long double to) noexcept;
extern template posit<64, 3> nexttoward(
    posit<64, 3> from, posit<64, 3> to) noexcept;
#if POSIT_HAS_INT128
extern template posit<8, 0> nexttoward(
    posit<8, 0> from, posit<128, 4> to) noexcept;
extern template posit<16, 1> nexttoward(
    posit<16, 1> from, posit<128, 4> to) noexcept;
extern template posit<32, 2> nexttoward(
    posit<32, 2> from, posit<128, 4> to) noexcept;
extern template posit<64, 3> nexttoward(
    posit<64, 3> from, posit<128, 4> to) noexcept;

extern template posit<128, 4> nextafter(
    posit<128, 4> from, posit<128, 4> to) noexcept;
extern template posit<128, 4> nexttoward(
    posit<128, 4> from, long double to) noexcept;
extern template posit<128, 4> nexttoward(
    posit<128, 4> from, posit<128, 4> to) noexcept;
#endif

// Many of these are only instantiated for the mult_intermediate, because there
// are non-template functions for the default posit to allow conversions,
// which will be instantiated with the class.
extern template quire<12, 7>::quire(posit_mult_intermediate<8, 0>) noexcept;
extern template quire<12, 7>& quire<12, 7>::operator=(
    posit_mult_intermediate<8, 0> p) noexcept;
extern template posit<8, 0> quire<12, 7>::to_posit<8, 0>() const noexcept;
extern template quire<12, 7>::operator quire<12, 7>::default_posit()
    const noexcept;
extern template quire<12, 7>& quire<12, 7>::operator+=(
    posit_mult_intermediate<8, 0> p) noexcept;
extern template quire<12, 7>& quire<12, 7>::operator-=(
    posit_mult_intermediate<8, 0> p) noexcept;
extern template void quire<12, 7>::Add(
    int min_bit_pos, quire<12, 7>::ArrayType significand) noexcept;
extern template void quire<12, 7>::Sub(
    int min_bit_pos, quire<12, 7>::ArrayType significand) noexcept;

extern template quire<56, 15>::quire(posit_mult_intermediate<16, 1>) noexcept;
extern template quire<56, 15>& quire<56, 15>::operator=(
    posit_mult_intermediate<16, 1> p) noexcept;
extern template posit<16, 1> quire<56, 15>::to_posit<16, 1>() const noexcept;
extern template quire<56, 15>::operator quire<56, 15>::default_posit()
    const noexcept;
extern template quire<56, 15>& quire<56, 15>::operator+=(
    posit_mult_intermediate<16, 1> p) noexcept;
extern template quire<56, 15>& quire<56, 15>::operator-=(
    posit_mult_intermediate<16, 1> p) noexcept;
extern template void quire<56, 15>::Add(
    int min_bit_pos, quire<56, 15>::ArrayType significand) noexcept;
extern template void quire<56, 15>::Sub(
    int min_bit_pos, quire<56, 15>::ArrayType significand) noexcept;

extern template quire<240, 31>::quire(posit_mult_intermediate<32, 2>) noexcept;
extern template quire<240, 31>& quire<240, 31>::operator=(
    posit_mult_intermediate<32, 2> p) noexcept;
extern template posit<32, 2> quire<240, 31>::to_posit<32, 2>() const noexcept;
extern template quire<240, 31>::operator quire<240, 31>::default_posit()
    const noexcept;
extern template quire<240, 31>& quire<240, 31>::operator+=(
    posit_mult_intermediate<32, 2> p) noexcept;
extern template quire<240, 31>& quire<240, 31>::operator-=(
    posit_mult_intermediate<32, 2> p) noexcept;
extern template void quire<240, 31>::Add(
    int min_bit_pos, quire<240, 31>::ArrayType significand) noexcept;
extern template void quire<240, 31>::Sub(
    int min_bit_pos, quire<240, 31>::ArrayType significand) noexcept;

extern template quire<992, 63>::quire(posit_mult_intermediate<64, 3>) noexcept;
extern template quire<992, 63>& quire<992, 63>::operator=(
    posit_mult_intermediate<64, 3> p) noexcept;
extern template posit<64, 3> quire<992, 63>::to_posit<64, 3>() const noexcept;
extern template quire<992, 63>::operator quire<992, 63>::default_posit()
    const noexcept;
extern template quire<992, 63>& quire<992, 63>::operator+=(
    posit_mult_intermediate<64, 3> p) noexcept;
extern template quire<992, 63>& quire<992, 63>::operator-=(
    posit_mult_intermediate<64, 3> p) noexcept;
extern template void quire<992, 63>::Add(
    int min_bit_pos, quire<992, 63>::ArrayType significand) noexcept;
extern template void quire<992, 63>::Sub(
    int min_bit_pos, quire<992, 63>::ArrayType significand) noexcept;

#if POSIT_HAS_INT128
extern template quire<4032, 127>::quire(posit_mult_intermediate<128, 4>)
    noexcept;
extern template quire<4032, 127>& quire<4032, 127>::operator=(
    posit_mult_intermediate<128, 4> p) noexcept;
extern template posit<128, 4> quire<4032, 127>::to_posit<128, 4>()
    const noexcept;
extern template quire<4032, 127>::operator quire<4032, 127>::default_posit()
    const noexcept;
extern template quire<4032, 127>& quire<4032, 127>::operator+=(
    posit_mult_intermediate<128, 4> p) noexcept;
extern template quire<4032, 127>& quire<4032, 127>::operator-=(
    posit_mult_intermediate<128, 4> p) noexcept;
extern template void quire<4032, 127>::Add(
    int min_bit_pos, quire<4032, 127>::ArrayType significand) noexcept;
extern template void quire<4032, 127>::Sub(
    int min_bit_pos, quire<4032, 127>::ArrayType significand) noexcept;
#endif
#endif  // !POSIT_HEADER_ONLY

#endif  // UGHOAVGFHW_POSIT_H_
