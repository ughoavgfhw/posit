#include <stdint.h>
#include <math.h>
#include <iostream>
#include <iomanip>
#include <random>

#include "posit.h"

constexpr int kTrials = 100'000'000;

posit32 rand_p32() {
  static auto gen = [] {
    std::random_device dev;
    std::random_device::result_type a = dev(), b = dev(), c = dev(), d = dev();
    std::cerr << "Seeding: " << a << " " << b << " " << c << " " << d << "\n";
    std::seed_seq seed = {a, b, c, d};
    return std::mt19937_64(seed);
  }();
  // Equal chances of all bit patterns except NaR. Posit values near ±1 are
  // more likely, since there are more fraction bits there.
  static std::uniform_int_distribution<int32_t> rand(-0x7FFFFFFF, 0x7FFFFFFF);
  return posit32::WithBits(rand(gen));
}

double limit(double val) {
  // Round true results outside the posit range back, to avoid huge errors.
  if (val == 0.0) return 0.0;
  double sign = val >= 0 ? 1.0 : -1.0;
  if (abs(val) > double(posit32::Max())) return sign * double(posit32::Max());
  if (abs(val) < double(posit32::Min())) return sign * double(posit32::Min());
  return val;
}

// Returns true if abs_err is more than 1/2 ULP based on the exponent of
// pos_result.
bool err_too_big(double abs_err, double pos_result) {
  if (isinf(abs_err)) return true;  // Special marker when x/0 != NaR.
  // The minimum possible result is 2^-240, so errors at least 32 powers of
  // two below that are effectively zero.
  if (abs_err < 0x1.0p-272) return false;
  int exp;
  // Returns the true exponent + 1, and a value in [0.5, 1).
  double pos_scaled = frexp(abs(pos_result), &exp);
  int err_exp;
  double err_scaled = frexp(abs_err, &err_exp);
  int frac_bits = PositTraits<32, 2>::FractionBitsAtExponent(exp - 1);
  if (frac_bits > 0) {
    // If there are fraction bits, expect the error to be lower by at least
    // that many powers of two, and another for the hidden bit.
    return exp - frac_bits - 1 < err_exp;
  } else if (exp > 0) {
    // Regime 27 (exp 108) has no fraction bits but both exponent bits. The
    // error there should have an exponent difference of at least 1.
    // Regime 28 (exp 112) has no fraction bits and 1 exponent bit. The error
    // there must be smaller than the posit result.
    // Regime 29 and 30 (exp 116 and 120) have no fraction or exponent bits.
    // The error must be less than 2x the posit result.
    if (exp+1 < 112) return exp - 1 < err_exp;
    if (exp+1 < 116)
      return exp < err_exp || (exp == err_exp && pos_scaled < err_scaled);
    return exp < err_exp - 1;
  } else {
    // Regime -28 corresponds to regime 27, -29 to 28, and -30 to 29 or 30.
    if (exp+1 >= -112) return exp - 1 < err_exp;
    if (exp+1 >= -116)
      return exp < err_exp || (exp == err_exp && pos_scaled < err_scaled);
    return exp < err_exp - 1;
  }
}

void log_fail(double a, const char* op, double b, double result, double err) {
  std::cerr << "Error: " << std::hexfloat << a << " " << op << " " << b
            << " resulted in " << result << ", with an error of " << err
            << "\n" << std::defaultfloat;
}

bool smoke_binary_ops() {
  uint32_t add_fails = 0, sub_fails = 0, mul_fails = 0, div_fails = 0;
  uint32_t total_failures = 0;
  std::cerr << "Running " << kTrials << " trials of binary operations.\n";
  for (int i = 0; i < kTrials; ++i) {
    posit32 a = rand_p32(), b = rand_p32();
    posit32 sum = a + b, diff = a - b, prod = a * b, quot = a / b;
    // Check using doubles, as IEEE-754 doubles don't lose precision from a
    // posit32, as is confirmed by implicit conversion.
    double da = a, db = b;
    double sum_err = abs(limit(da + db) - (double)sum),
        diff_err = abs(limit(da - db) - (double)diff),
        prod_err = abs(limit(da * db) - (double)prod),
        quot_err = b != posit32() ? abs(limit(da / db) - (double)quot)
                                  : quot == posit32::NaR() ? 0.0 : INFINITY;
    if (err_too_big(sum_err, sum)) {
      ++add_fails;
      if (++total_failures <= 10) log_fail(a, "+", b, sum, sum_err);
    }
    if (err_too_big(diff_err, diff)) {
      ++sub_fails;
      if (++total_failures <= 10) log_fail(a, "-", b, diff, diff_err);
    }
    if (err_too_big(prod_err, prod)) {
      ++mul_fails;
      if (++total_failures <= 10) log_fail(a, "*", b, prod, prod_err);
    }
    if (err_too_big(quot_err, quot)) {
      ++div_fails;
      if (++total_failures <= 10) log_fail(a, "/", b, quot, quot_err);
    }
  }
  if (add_fails == 0 && sub_fails == 0 && mul_fails == 0 && div_fails == 0) {
    std::cout << "Binary operations: PASS\n";
    return true;
  }
  std::cout
      << "Binary operations: FAIL\n"
      << "  Addition:       " << std::setw(9) << add_fails << " incorrect\n"
      << "  Subtraction:    " << std::setw(9) << sub_fails << " incorrect\n"
      << "  Multiplication: " << std::setw(9) << mul_fails << " incorrect\n"
      << "  Division:       " << std::setw(9) << div_fails << " incorrect\n";
  return false;
}

int main() {
  bool ok = smoke_binary_ops();
  return ok ? 0 : 1;
}
