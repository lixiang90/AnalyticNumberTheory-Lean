import AnalyticNumberTheory.SieveMethods.ReciprocalConductorLargeSieve
import AnalyticNumberTheory.DirichletLFunctions.CharacterPolynomialSquares
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialDiagonals
import AnalyticNumberTheory.PrimeDistribution.Chebyshev

/-! # Conductor means of short polynomials on the critical line

These estimates apply at a single, arbitrary ordinate. In particular they
apply under the vertical integrals in the contour method for primes in
arithmetic progressions.
-/
noncomputable section
open Complex Finset
open scoped Classical ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- The primitive second moment on a conductor interval at a single ordinate.
The coefficient energy carries its critical-line weight exactly. -/
theorem conductor_polynomial_second_moment (a : ℕ→ℂ) (N R : ℕ) {Q : ℕ} (hQ : 1≤Q) (t : ℝ) :
    (∑ q∈Ioc Q R, (q.totient:ℝ)⁻¹*
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      ‖dirichletPoly (fun n => a n*χ n) N ((1/2:ℂ)+t*I)‖^2) ≤
      (2*(R:ℝ)+(N:ℝ)/Q)*∑n∈Icc 1 N, ‖a n‖^2*(n:ℝ)⁻¹ := by
  let s := (1/2:ℂ)+(t:ℂ)*I
  let b (n : ℕ) := a n*(n:ℂ)^(-s)
  have h := reciprocal_conductor_large_sieve b 0 N hQ R
  simp only [zero_add, ←Icc_add_one_left_eq_Ioc (a:=0),zero_add] at h
  have he (n) (hn : n∈Icc 1 N) : ‖b n‖^2=‖a n‖^2*(n:ℝ)⁻¹ := by
    have hn' := (mem_Icc.mp hn).1
    have hs : (-s).re=-(1/2:ℝ) := by simp [s]
    dsimp only [b]
    rw [norm_mul,mul_pow,Complex.norm_natCast_cpow_of_pos hn',hs,
      ←Real.rpow_mul_natCast (Nat.cast_nonneg n),show -(1/2:ℝ)*(2:ℕ)=-1 by norm_num,Real.rpow_neg_one]
  rw [sum_congr rfl he] at h
  convert h using 1
  apply sum_congr rfl;intro q _
  congr 1
  apply sum_congr rfl;intro χ _
  congr 2
  apply sum_congr rfl;intro n _
  dsimp only [b,s];ring

/-- For coefficients of modulus at most one, the harmonic sum bounds the
second moment. This includes the truncated Möbius polynomial. -/
theorem bounded_conductor_polynomial_second (a : ℕ→ℂ) {N Q R : ℕ} (hQ : 1≤Q)
    (ha : ∀n∈Icc 1 N,‖a n‖≤1) (t : ℝ) :
    (∑ q∈Ioc Q R, (q.totient:ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      ‖dirichletPoly (fun n => a n*χ n) N ((1/2:ℂ)+t*I)‖^2) ≤
      (2*(R:ℝ)+(N:ℝ)/Q)*(1+Real.log N) := by
  apply (conductor_polynomial_second_moment a N R hQ t).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans (b:=∑n∈Icc 1 N,(n:ℝ)⁻¹)
  · apply sum_le_sum; intro n hn
    exact mul_le_of_le_one_left (by positivity) ((pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2).trans_eq (one_pow _))
  · simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log N

/-- Fourth moment of a bounded-coefficient polynomial, uniform in the height
and all conductor cutoffs. The squared polynomial has length N². -/
theorem bounded_conductor_polynomial_fourth (a : ℕ→ℂ) {N Q R : ℕ} (hN : 1≤N) (hQ : 1≤Q)
    (ha : ∀n∈Icc 1 N,‖a n‖≤1) (t : ℝ) :
    (∑ q∈Ioc Q R, (q.totient:ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      ‖dirichletPoly (fun n => a n*χ n) N ((1/2:ℂ)+t*I)‖^4) ≤
      (2*(R:ℝ)+(N:ℝ)^2/Q)*(1+Real.log ((N^2:ℕ):ℝ))^4 := by
  let b := factorPairWeight (Icc 1 N) a
  have he {q : ℕ} (χ : DirichletCharacter ℂ q) :
      ‖dirichletPoly (fun n => a n*χ n) N ((1/2:ℂ)+t*I)‖^4 =
      ‖dirichletPoly (fun n => b n*χ n) (N^2) ((1/2:ℂ)+t*I)‖^2 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,←norm_pow]
    change ‖(∑n∈Icc 1 N,a n*χ n*(n:ℂ)^(-((1/2:ℂ)+t*I)))^2‖^2=_
    rw [weighted_characterPolynomial_square χ a _ (Finset.Subset.refl (Icc 1 N))]
    rfl
  simp_rw [he]
  apply (conductor_polynomial_second_moment b (N^2) R hQ t).trans
  rw [Nat.cast_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans (b:=∑n∈Icc 1 (N^2),(n.divisors.card:ℝ)^2*(n:ℝ)⁻¹)
  · apply sum_le_sum;intro n hn
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (norm_factorPairWeight_le ha (mem_Icc.mp hn).1) 2) (by positivity)
  · simpa only [Real.rpow_neg_one,Nat.cast_pow] using RiemannZeta.divisor_diagonal_critical (Nat.one_le_pow 2 N hN)

/-- The von Mangoldt polynomial on the critical line. Its diagonal is
bounded by log N times the first Mertens sum. -/
theorem mangoldt_conductor_polynomial_second {N Q R : ℕ} (hN : 1≤N) (hQ : 1≤Q) (t : ℝ) :
    (∑ q∈Ioc Q R, (q.totient:ℝ)⁻¹*∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      ‖dirichletPoly (fun n => (Λ n:ℂ)*χ n) N ((1/2:ℂ)+t*I)‖^2) ≤
      (2*(R:ℝ)+(N:ℝ)/Q)*(Real.log N*(Real.log N+Real.log 4+8)) := by
  apply (conductor_polynomial_second_moment (fun n => (Λ n:ℂ)) N R hQ t).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hm := (abs_le.mp (abs_sum_vonMangoldt_div_sub_log_le (by exact_mod_cast hN : (1:ℝ)≤N))).2
  rw [Nat.floor_natCast] at hm
  have hlog := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)
  calc _ ≤ ∑n∈Icc 1 N,Real.log N*(Λ n/n) := by
             apply sum_le_sum;intro n hn
             have hb := ArithmeticFunction.vonMangoldt_le_log (n:=n) |>.trans
               (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1 : (0:ℝ)<n) (Nat.cast_le.mpr (mem_Icc.mp hn).2 : (n:ℝ)≤N))
             have hp := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
             rw [Complex.norm_real,Real.norm_of_nonneg hp]
             rw [sq,div_eq_mul_inv,←mul_assoc]
             exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hp) (by positivity)
       _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left (by linarith only [hm]) hlog

end AnalyticNumberTheory.PrimeDistribution