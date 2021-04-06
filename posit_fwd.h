#ifndef UGHOAVGFHW_POSIT_FWD_H_
#define UGHOAVGFHW_POSIT_FWD_H_

#include "posit_config.h"

template <int N, int E> class posit;
template <int NQ, int C> class quire;
using posit8 = posit<8, 0>;
using posit16 = posit<16, 1>;
using posit32 = posit<32, 2>;
using posit64 = posit<64, 3>;

using quire8 = quire<12, 7>;
using quire16 = quire<56, 15>;
using quire32 = quire<240, 31>;
using quire64 = quire<992, 63>;

#if POSIT_HAS_INT128
using posit128 = posit<128, 4>;
using quire128 = quire<4032, 127>;
#endif

template <int N, int E> class posit_mult_intermediate;

template <int N, int E>
using PreferredQuire = quire<(N - 2) << (E + 1), N - 1>;

template <typename PositOrTraits>
using QuireForPosit = typename PositOrTraits::quire_type;

template <int N, int E>
constexpr posit_mult_intermediate<N, E> operator*(posit<N, E> lhs,
                                                  posit<N, E> rhs) noexcept;
template <int N, int E>
constexpr posit<N, E> operator/(posit<N, E> n, posit<N, E> d) noexcept;
template <int N, int E>
constexpr posit<N, E> operator+(posit<N, E> lhs, posit<N, E> rhs) noexcept;
template <int N, int E>
constexpr posit<N, E> operator-(posit<N, E> lhs, posit<N, E> rhs) noexcept;

template <int N, int E>
constexpr posit<N, E> nextafter(posit<N, E> from, posit<N, E> to) noexcept;
template <int N, int E>
constexpr posit<N, E> nexttoward(posit<N, E> from, long double to) noexcept;
template <int N1, int E1, int N2, int E2>
constexpr posit<N1, E1> nexttoward(posit<N1, E1> from,
                                   posit<N2, E2> to) noexcept;

template <int S> struct decoded_posit;

#endif  // UGHOAVGFHW_POSIT_FWD_H_
