#include "posit.h"

#ifndef POSIT_HEADER_ONLY

template struct PositByStorage<8>;
template struct PositByStorage<16>;
template struct PositByStorage<32>;
template struct PositByStorage<64>;

template PositByStorage<8>::FromFloatPrecheckResult
PositByStorage<8>::FromFloatPrecheck(float) noexcept;
template decoded_posit<8> PositByStorage<8>::FromFloat(float) noexcept;
template float PositByStorage<8>::ToFloat(decoded_posit<8>) noexcept;
template PositByStorage<8>::FromFloatPrecheckResult
PositByStorage<8>::FromFloatPrecheck(double) noexcept;
template decoded_posit<8> PositByStorage<8>::FromFloat(double) noexcept;
template double PositByStorage<8>::ToFloat(decoded_posit<8>) noexcept;
template PositByStorage<8>::FromFloatPrecheckResult
PositByStorage<8>::FromFloatPrecheck(long double) noexcept;
template decoded_posit<8> PositByStorage<8>::FromFloat(long double)
    noexcept;
template long double PositByStorage<8>::ToFloat(decoded_posit<8>)
    noexcept;
template decoded_posit<8> PositByStorage<8>::FromInt(int) noexcept;
template int PositByStorage<8>::ToInt(decoded_posit<8> dec) noexcept;
template decoded_posit<8> PositByStorage<8>::FromInt(long) noexcept;
template long PositByStorage<8>::ToInt(decoded_posit<8> dec) noexcept;
template decoded_posit<8> PositByStorage<8>::FromInt(long long) noexcept;
template long long PositByStorage<8>::ToInt(decoded_posit<8> dec)
    noexcept;
template decoded_posit<8> PositByStorage<8>::FromInt(
    unsigned int) noexcept;
template unsigned int PositByStorage<8>::ToInt(
    decoded_posit<8> dec) noexcept;
template decoded_posit<8> PositByStorage<8>::FromInt(
    unsigned long) noexcept;
template unsigned long PositByStorage<8>::ToInt(
    decoded_posit<8> dec) noexcept;
template decoded_posit<8> PositByStorage<8>::FromInt(
    unsigned long long) noexcept;
template unsigned long long PositByStorage<8>::ToInt(
    decoded_posit<8> dec) noexcept;
template decoded_posit<8> PositByStorage<8>::DivideImpl<0>(
    decoded_posit<8> n, decoded_posit<8> d) noexcept;
// Not instantiating Divide(), as it's a fairly small wrapper depending on an
// exact posit, and so will likely be inlined into positN's operator/().

template PositByStorage<16>::FromFloatPrecheckResult
PositByStorage<16>::FromFloatPrecheck(float) noexcept;
template decoded_posit<16> PositByStorage<16>::FromFloat(float) noexcept;
template float PositByStorage<16>::ToFloat(decoded_posit<16>) noexcept;
template PositByStorage<16>::FromFloatPrecheckResult
PositByStorage<16>::FromFloatPrecheck(double) noexcept;
template decoded_posit<16> PositByStorage<16>::FromFloat(double)
    noexcept;
template double PositByStorage<16>::ToFloat(decoded_posit<16>) noexcept;
template PositByStorage<16>::FromFloatPrecheckResult
PositByStorage<16>::FromFloatPrecheck(long double) noexcept;
template decoded_posit<16> PositByStorage<16>::FromFloat(long double)
    noexcept;
template long double PositByStorage<16>::ToFloat(decoded_posit<16>)
    noexcept;
template decoded_posit<16> PositByStorage<16>::FromInt(int) noexcept;
template int PositByStorage<16>::ToInt(decoded_posit<16> dec) noexcept;
template decoded_posit<16> PositByStorage<16>::FromInt(long) noexcept;
template long PositByStorage<16>::ToInt(decoded_posit<16> dec) noexcept;
template decoded_posit<16> PositByStorage<16>::FromInt(long long)
    noexcept;
template long long PositByStorage<16>::ToInt(decoded_posit<16> dec)
    noexcept;
template decoded_posit<16> PositByStorage<16>::FromInt(
    unsigned int) noexcept;
template unsigned int PositByStorage<16>::ToInt(
    decoded_posit<16> dec) noexcept;
template decoded_posit<16> PositByStorage<16>::FromInt(
    unsigned long) noexcept;
template unsigned long PositByStorage<16>::ToInt(
    decoded_posit<16> dec) noexcept;
template decoded_posit<16> PositByStorage<16>::FromInt(
    unsigned long long) noexcept;
template unsigned long long PositByStorage<16>::ToInt(
    decoded_posit<16> dec) noexcept;
template decoded_posit<16> PositByStorage<16>::DivideImpl<0>(
    decoded_posit<16> n, decoded_posit<16> d) noexcept;

template PositByStorage<32>::FromFloatPrecheckResult
PositByStorage<32>::FromFloatPrecheck(float) noexcept;
template decoded_posit<32> PositByStorage<32>::FromFloat(float) noexcept;
template float PositByStorage<32>::ToFloat(decoded_posit<32>) noexcept;
template PositByStorage<32>::FromFloatPrecheckResult
PositByStorage<32>::FromFloatPrecheck(double) noexcept;
template decoded_posit<32> PositByStorage<32>::FromFloat(double)
    noexcept;
template double PositByStorage<32>::ToFloat(decoded_posit<32>) noexcept;
template PositByStorage<32>::FromFloatPrecheckResult
PositByStorage<32>::FromFloatPrecheck(long double) noexcept;
template decoded_posit<32> PositByStorage<32>::FromFloat(long double)
    noexcept;
template long double PositByStorage<32>::ToFloat(decoded_posit<32>)
    noexcept;
template decoded_posit<32> PositByStorage<32>::FromInt(int) noexcept;
template int PositByStorage<32>::ToInt(decoded_posit<32> dec) noexcept;
template decoded_posit<32> PositByStorage<32>::FromInt(long) noexcept;
template long PositByStorage<32>::ToInt(decoded_posit<32> dec) noexcept;
template decoded_posit<32> PositByStorage<32>::FromInt(long long)
    noexcept;
template long long PositByStorage<32>::ToInt(decoded_posit<32> dec)
    noexcept;
template decoded_posit<32> PositByStorage<32>::FromInt(
    unsigned int) noexcept;
template unsigned int PositByStorage<32>::ToInt(
    decoded_posit<32> dec) noexcept;
template decoded_posit<32> PositByStorage<32>::FromInt(
    unsigned long) noexcept;
template unsigned long PositByStorage<32>::ToInt(
    decoded_posit<32> dec) noexcept;
template decoded_posit<32> PositByStorage<32>::FromInt(
    unsigned long long) noexcept;
template unsigned long long PositByStorage<32>::ToInt(
    decoded_posit<32> dec) noexcept;
template decoded_posit<32> PositByStorage<32>::DivideImpl<0>(
    decoded_posit<32> n, decoded_posit<32> d) noexcept;

template PositByStorage<64>::FromFloatPrecheckResult
PositByStorage<64>::FromFloatPrecheck(float) noexcept;
template decoded_posit<64> PositByStorage<64>::FromFloat(float) noexcept;
template float PositByStorage<64>::ToFloat(decoded_posit<64>) noexcept;
template PositByStorage<64>::FromFloatPrecheckResult
PositByStorage<64>::FromFloatPrecheck(double) noexcept;
template decoded_posit<64> PositByStorage<64>::FromFloat(double)
    noexcept;
template double PositByStorage<64>::ToFloat(decoded_posit<64>) noexcept;
template PositByStorage<64>::FromFloatPrecheckResult
PositByStorage<64>::FromFloatPrecheck(long double) noexcept;
template decoded_posit<64> PositByStorage<64>::FromFloat(long double)
    noexcept;
template long double PositByStorage<64>::ToFloat(decoded_posit<64>)
    noexcept;
template decoded_posit<64> PositByStorage<64>::FromInt(int) noexcept;
template int PositByStorage<64>::ToInt(decoded_posit<64> dec) noexcept;
template decoded_posit<64> PositByStorage<64>::FromInt(long) noexcept;
template long PositByStorage<64>::ToInt(decoded_posit<64> dec) noexcept;
template decoded_posit<64> PositByStorage<64>::FromInt(long long)
    noexcept;
template long long PositByStorage<64>::ToInt(decoded_posit<64> dec)
    noexcept;
template decoded_posit<64> PositByStorage<64>::FromInt(
    unsigned int) noexcept;
template unsigned int PositByStorage<64>::ToInt(
    decoded_posit<64> dec) noexcept;
template decoded_posit<64> PositByStorage<64>::FromInt(
    unsigned long) noexcept;
template unsigned long PositByStorage<64>::ToInt(
    decoded_posit<64> dec) noexcept;
template decoded_posit<64> PositByStorage<64>::FromInt(
    unsigned long long) noexcept;
template unsigned long long PositByStorage<64>::ToInt(
    decoded_posit<64> dec) noexcept;
#if POSIT_HAS_INT128
template decoded_posit<64> PositByStorage<64>::DivideImpl<0>(
    decoded_posit<64> n, decoded_posit<64> d) noexcept;
#else
template decoded_posit<64> PositByStorage<64>::DivideImpl<58>(
    decoded_posit<64> n, decoded_posit<64> d) noexcept;
#endif
#if POSIT_HAS_INT128
template PositByStorage<128>::FromFloatPrecheckResult
PositByStorage<128>::FromFloatPrecheck(float) noexcept;
template decoded_posit<128> PositByStorage<128>::FromFloat(float)
    noexcept;
template float PositByStorage<128>::ToFloat(decoded_posit<128>) noexcept;
template PositByStorage<128>::FromFloatPrecheckResult
PositByStorage<128>::FromFloatPrecheck(double) noexcept;
template decoded_posit<128> PositByStorage<128>::FromFloat(double)
    noexcept;
template double PositByStorage<128>::ToFloat(decoded_posit<128>)
    noexcept;
template PositByStorage<128>::FromFloatPrecheckResult
PositByStorage<128>::FromFloatPrecheck(long double) noexcept;
template decoded_posit<128> PositByStorage<128>::FromFloat(long double)
    noexcept;
template long double PositByStorage<128>::ToFloat(decoded_posit<128>)
    noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(int) noexcept;
template int PositByStorage<128>::ToInt(decoded_posit<128> dec) noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(long) noexcept;
template long PositByStorage<128>::ToInt(decoded_posit<128> dec)
    noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(long long)
    noexcept;
template long long PositByStorage<128>::ToInt(decoded_posit<128> dec)
    noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(__int128)
    noexcept;
template __int128 PositByStorage<128>::ToInt(decoded_posit<128> dec)
    noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(
    unsigned int) noexcept;
template unsigned int PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(
    unsigned long) noexcept;
template unsigned long PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(
    unsigned long long) noexcept;
template unsigned long long PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
template decoded_posit<128> PositByStorage<128>::FromInt(unsigned __int128)
    noexcept;
template unsigned __int128 PositByStorage<128>::ToInt(
    decoded_posit<128> dec) noexcept;
template decoded_posit<128> PositByStorage<128>::DivideImpl<121>(
    decoded_posit<128> n, decoded_posit<128> d) noexcept;
#endif

template class posit<8, 0>;
template class posit<16, 1>;
template class posit<32, 2>;
template class posit<64, 3>;
template class quire<12, 7>;
template class quire<56, 15>;
template class quire<240, 31>;
template class quire<992, 63>;
template class posit_mult_intermediate<8, 0>;
template class posit_mult_intermediate<16, 1>;
template class posit_mult_intermediate<32, 2>;
template class posit_mult_intermediate<64, 3>;
#if POSIT_HAS_INT128
template class posit<128, 4>;
template class quire<4032, 127>;
template class posit_mult_intermediate<128, 4>;
#endif

template posit<8, 0>::posit(float) noexcept;
template posit<8, 0>::posit(double) noexcept;
template posit<8, 0>::posit(long double) noexcept;
template posit<8, 0>::posit(int) noexcept;
template posit<8, 0>::posit(long) noexcept;
template posit<8, 0>::posit(long long) noexcept;
template posit<8, 0>::posit(unsigned) noexcept;
template posit<8, 0>::posit(unsigned long) noexcept;
template posit<8, 0>::posit(unsigned long long) noexcept;
template posit<8, 0>::operator float() const noexcept;
template posit<8, 0>::operator double() const noexcept;
template posit<8, 0>::operator long double() const noexcept;
template posit<8, 0>::operator int() const noexcept;
template posit<8, 0>::operator long() const noexcept;
template posit<8, 0>::operator long long() const noexcept;
template posit<8, 0>::operator unsigned() const noexcept;
template posit<8, 0>::operator unsigned long() const noexcept;
template posit<8, 0>::operator unsigned long long() const noexcept;
template posit<8, 0>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
template posit<16, 1>::posit(posit<8, 0>) noexcept;
template posit<16, 1>::posit(float) noexcept;
template posit<16, 1>::posit(double) noexcept;
template posit<16, 1>::posit(long double) noexcept;
template posit<16, 1>::posit(int) noexcept;
template posit<16, 1>::posit(long) noexcept;
template posit<16, 1>::posit(long long) noexcept;
template posit<16, 1>::posit(unsigned) noexcept;
template posit<16, 1>::posit(unsigned long) noexcept;
template posit<16, 1>::posit(unsigned long long) noexcept;
template posit<16, 1>::operator float() const noexcept;
template posit<16, 1>::operator double() const noexcept;
template posit<16, 1>::operator long double() const noexcept;
template posit<16, 1>::operator int() const noexcept;
template posit<16, 1>::operator long() const noexcept;
template posit<16, 1>::operator long long() const noexcept;
template posit<16, 1>::operator unsigned() const noexcept;
template posit<16, 1>::operator unsigned long() const noexcept;
template posit<16, 1>::operator unsigned long long() const noexcept;
template posit<16, 1>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
template posit<32, 2>::posit(posit<8, 0>) noexcept;
template posit<32, 2>::posit(posit<16, 1>) noexcept;
template posit<32, 2>::posit(float) noexcept;
template posit<32, 2>::posit(double) noexcept;
template posit<32, 2>::posit(long double) noexcept;
template posit<32, 2>::posit(int) noexcept;
template posit<32, 2>::posit(long) noexcept;
template posit<32, 2>::posit(long long) noexcept;
template posit<32, 2>::posit(unsigned) noexcept;
template posit<32, 2>::posit(unsigned long) noexcept;
template posit<32, 2>::posit(unsigned long long) noexcept;
template posit<32, 2>::operator float() const noexcept;
template posit<32, 2>::operator double() const noexcept;
template posit<32, 2>::operator long double() const noexcept;
template posit<32, 2>::operator int() const noexcept;
template posit<32, 2>::operator long() const noexcept;
template posit<32, 2>::operator long long() const noexcept;
template posit<32, 2>::operator unsigned() const noexcept;
template posit<32, 2>::operator unsigned long() const noexcept;
template posit<32, 2>::operator unsigned long long() const noexcept;
template posit<32, 2>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
template posit<64, 3>::posit(posit<8, 0>) noexcept;
template posit<64, 3>::posit(posit<16, 1>) noexcept;
template posit<64, 3>::posit(posit<32, 2>) noexcept;
template posit<64, 3>::posit(float) noexcept;
template posit<64, 3>::posit(double) noexcept;
template posit<64, 3>::posit(long double) noexcept;
template posit<64, 3>::posit(int) noexcept;
template posit<64, 3>::posit(long) noexcept;
template posit<64, 3>::posit(long long) noexcept;
template posit<64, 3>::posit(unsigned) noexcept;
template posit<64, 3>::posit(unsigned long) noexcept;
template posit<64, 3>::posit(unsigned long long) noexcept;
template posit<64, 3>::operator float() const noexcept;
template posit<64, 3>::operator double() const noexcept;
template posit<64, 3>::operator long double() const noexcept;
template posit<64, 3>::operator int() const noexcept;
template posit<64, 3>::operator long() const noexcept;
template posit<64, 3>::operator long long() const noexcept;
template posit<64, 3>::operator unsigned() const noexcept;
template posit<64, 3>::operator unsigned long() const noexcept;
template posit<64, 3>::operator unsigned long long() const noexcept;
template posit<64, 3>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
#if POSIT_HAS_INT128
template posit<128, 4>::posit(posit<8, 0>) noexcept;
template posit<128, 4>::posit(posit<16, 1>) noexcept;
template posit<128, 4>::posit(posit<32, 2>) noexcept;
template posit<128, 4>::posit(posit<64, 3>) noexcept;
template posit<128, 4>::posit(float) noexcept;
template posit<128, 4>::posit(double) noexcept;
template posit<128, 4>::posit(long double) noexcept;
template posit<128, 4>::posit(int) noexcept;
template posit<128, 4>::posit(long) noexcept;
template posit<128, 4>::posit(long long) noexcept;
template posit<128, 4>::posit(__int128) noexcept;
template posit<128, 4>::posit(unsigned) noexcept;
template posit<128, 4>::posit(unsigned long) noexcept;
template posit<128, 4>::posit(unsigned long long) noexcept;
template posit<128, 4>::posit(unsigned __int128) noexcept;
template posit<128, 4>::operator float() const noexcept;
template posit<128, 4>::operator double() const noexcept;
template posit<128, 4>::operator long double() const noexcept;
template posit<128, 4>::operator int() const noexcept;
template posit<128, 4>::operator long() const noexcept;
template posit<128, 4>::operator long long() const noexcept;
template posit<128, 4>::operator __int128() const noexcept;
template posit<128, 4>::operator unsigned() const noexcept;
template posit<128, 4>::operator unsigned long() const noexcept;
template posit<128, 4>::operator unsigned long long() const noexcept;
template posit<128, 4>::operator unsigned __int128() const noexcept;
template posit<128, 4>::posit(bool) noexcept;
// Conversion to bool is not a template, so is already instantiated with the
// rest of the class.
#endif

template posit_mult_intermediate<8, 0> operator*(
    posit<8, 0> lhs, posit<8, 0> rhs) noexcept;
template posit<8, 0> operator/(
    posit<8, 0> n, posit<8, 0> d) noexcept;
template posit<8, 0> operator+(
    posit<8, 0> lhs, posit<8, 0> rhs) noexcept;
template posit<8, 0> operator-(
    posit<8, 0> lhs, posit<8, 0> rhs) noexcept;
template posit_mult_intermediate<16, 1> operator*(
    posit<16, 1> lhs, posit<16, 1> rhs) noexcept;
template posit<16, 1> operator/(
    posit<16, 1> n, posit<16, 1> d) noexcept;
template posit<16, 1> operator+(
    posit<16, 1> lhs, posit<16, 1> rhs) noexcept;
template posit<16, 1> operator-(
    posit<16, 1> lhs, posit<16, 1> rhs) noexcept;
template posit_mult_intermediate<32, 2> operator*(
    posit<32, 2> lhs, posit<32, 2> rhs) noexcept;
template posit<32, 2> operator/(
    posit<32, 2> n, posit<32, 2> d) noexcept;
template posit<32, 2> operator+(
    posit<32, 2> lhs, posit<32, 2> rhs) noexcept;
template posit<32, 2> operator-(
    posit<32, 2> lhs, posit<32, 2> rhs) noexcept;
template posit_mult_intermediate<64, 3> operator*(
    posit<64, 3> lhs, posit<64, 3> rhs) noexcept;
template posit<64, 3> operator/(
    posit<64, 3> n, posit<64, 3> d) noexcept;
template posit<64, 3> operator+(
    posit<64, 3> lhs, posit<64, 3> rhs) noexcept;
template posit<64, 3> operator-(
    posit<64, 3> lhs, posit<64, 3> rhs) noexcept;
#if POSIT_HAS_INT128
template posit_mult_intermediate<128, 4> operator*(
    posit<128, 4> lhs, posit<128, 4> rhs) noexcept;
template posit<128, 4> operator/(
    posit<128, 4> n, posit<128, 4> d) noexcept;
template posit<128, 4> operator+(
    posit<128, 4> lhs, posit<128, 4> rhs) noexcept;
template posit<128, 4> operator-(
    posit<128, 4> lhs, posit<128, 4> rhs) noexcept;
#endif

template posit<8, 0> nextafter(
    posit<8, 0> from, posit<8, 0> to) noexcept;
template posit<8, 0> nexttoward(
    posit<8, 0> from, long double to) noexcept;
template posit<8, 0> nexttoward(
    posit<8, 0> from, posit<64, 3> to) noexcept;
template posit<16, 1> nextafter(
    posit<16, 1> from, posit<16, 1> to) noexcept;
template posit<16, 1> nexttoward(
    posit<16, 1> from, long double to) noexcept;
template posit<16, 1> nexttoward(
    posit<16, 1> from, posit<64, 3> to) noexcept;
template posit<32, 2> nextafter(
    posit<32, 2> from, posit<32, 2> to) noexcept;
template posit<32, 2> nexttoward(
    posit<32, 2> from, long double to) noexcept;
template posit<32, 2> nexttoward(
    posit<32, 2> from, posit<64, 3> to) noexcept;
template posit<64, 3> nextafter(
    posit<64, 3> from, posit<64, 3> to) noexcept;
template posit<64, 3> nexttoward(
    posit<64, 3> from, long double to) noexcept;
template posit<64, 3> nexttoward(
    posit<64, 3> from, posit<64, 3> to) noexcept;
#if POSIT_HAS_INT128
template posit<8, 0> nexttoward(
    posit<8, 0> from, posit<128, 4> to) noexcept;
template posit<16, 1> nexttoward(
    posit<16, 1> from, posit<128, 4> to) noexcept;
template posit<32, 2> nexttoward(
    posit<32, 2> from, posit<128, 4> to) noexcept;
template posit<64, 3> nexttoward(
    posit<64, 3> from, posit<128, 4> to) noexcept;

template posit<128, 4> nextafter(
    posit<128, 4> from, posit<128, 4> to) noexcept;
template posit<128, 4> nexttoward(
    posit<128, 4> from, long double to) noexcept;
template posit<128, 4> nexttoward(
    posit<128, 4> from, posit<128, 4> to) noexcept;
#endif

// Many of these are only instantiated for the mult_intermediate, because there
// are non-template functions for the default posit to allow conversions,
// which will be instantiated with the class.
template quire<12, 7>::quire(posit_mult_intermediate<8, 0>) noexcept;
template quire<12, 7>& quire<12, 7>::operator=(
    posit_mult_intermediate<8, 0> p) noexcept;
template posit<8, 0> quire<12, 7>::to_posit<8, 0>() const noexcept;
template quire<12, 7>::operator quire<12, 7>::default_posit()
    const noexcept;
template quire<12, 7>& quire<12, 7>::operator+=(
    posit_mult_intermediate<8, 0> p) noexcept;
template quire<12, 7>& quire<12, 7>::operator-=(
    posit_mult_intermediate<8, 0> p) noexcept;
template void quire<12, 7>::Add(
    int min_bit_pos, quire<12, 7>::ArrayType significand) noexcept;
template void quire<12, 7>::Sub(
    int min_bit_pos, quire<12, 7>::ArrayType significand) noexcept;

template quire<56, 15>::quire(posit_mult_intermediate<16, 1>) noexcept;
template quire<56, 15>& quire<56, 15>::operator=(
    posit_mult_intermediate<16, 1> p) noexcept;
template posit<16, 1> quire<56, 15>::to_posit<16, 1>() const noexcept;
template quire<56, 15>::operator quire<56, 15>::default_posit()
    const noexcept;
template quire<56, 15>& quire<56, 15>::operator+=(
    posit_mult_intermediate<16, 1> p) noexcept;
template quire<56, 15>& quire<56, 15>::operator-=(
    posit_mult_intermediate<16, 1> p) noexcept;
template void quire<56, 15>::Add(
    int min_bit_pos, quire<56, 15>::ArrayType significand) noexcept;
template void quire<56, 15>::Sub(
    int min_bit_pos, quire<56, 15>::ArrayType significand) noexcept;

template quire<240, 31>::quire(posit_mult_intermediate<32, 2>) noexcept;
template quire<240, 31>& quire<240, 31>::operator=(
    posit_mult_intermediate<32, 2> p) noexcept;
template posit<32, 2> quire<240, 31>::to_posit<32, 2>() const noexcept;
template quire<240, 31>::operator quire<240, 31>::default_posit()
    const noexcept;
template quire<240, 31>& quire<240, 31>::operator+=(
    posit_mult_intermediate<32, 2> p) noexcept;
template quire<240, 31>& quire<240, 31>::operator-=(
    posit_mult_intermediate<32, 2> p) noexcept;
template void quire<240, 31>::Add(
    int min_bit_pos, quire<240, 31>::ArrayType significand) noexcept;
template void quire<240, 31>::Sub(
    int min_bit_pos, quire<240, 31>::ArrayType significand) noexcept;

template quire<992, 63>::quire(posit_mult_intermediate<64, 3>) noexcept;
template quire<992, 63>& quire<992, 63>::operator=(
    posit_mult_intermediate<64, 3> p) noexcept;
template posit<64, 3> quire<992, 63>::to_posit<64, 3>() const noexcept;
template quire<992, 63>::operator quire<992, 63>::default_posit()
    const noexcept;
template quire<992, 63>& quire<992, 63>::operator+=(
    posit_mult_intermediate<64, 3> p) noexcept;
template quire<992, 63>& quire<992, 63>::operator-=(
    posit_mult_intermediate<64, 3> p) noexcept;
template void quire<992, 63>::Add(
    int min_bit_pos, quire<992, 63>::ArrayType significand) noexcept;
template void quire<992, 63>::Sub(
    int min_bit_pos, quire<992, 63>::ArrayType significand) noexcept;

#if POSIT_HAS_INT128
template quire<4032, 127>::quire(posit_mult_intermediate<128, 4>) noexcept;
template quire<4032, 127>& quire<4032, 127>::operator=(
    posit_mult_intermediate<128, 4> p) noexcept;
template posit<128, 4> quire<4032, 127>::to_posit<128, 4>()
    const noexcept;
template quire<4032, 127>::operator quire<4032, 127>::default_posit()
    const noexcept;
template quire<4032, 127>& quire<4032, 127>::operator+=(
    posit_mult_intermediate<128, 4> p) noexcept;
template quire<4032, 127>& quire<4032, 127>::operator-=(
    posit_mult_intermediate<128, 4> p) noexcept;
template void quire<4032, 127>::Add(
    int min_bit_pos, quire<4032, 127>::ArrayType significand) noexcept;
template void quire<4032, 127>::Sub(
    int min_bit_pos, quire<4032, 127>::ArrayType significand) noexcept;
#endif

#endif  // !POSIT_HEADER_ONLY
