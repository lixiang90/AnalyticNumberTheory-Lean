import AnalyticNumberTheory.SieveMethods.PrimeCharacterSieve

/-!
# A large sieve for general Gauss sums

The character transform of the additive samples is an exact identity for
arbitrary coefficient support, including terms sharing primes with the
modulus. Summing the identity over the moduli gives the Farey bound.
-/
noncomputable section
open Finset Complex Real
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

/-- Finite representative formula for the Gauss sum used in an outer sum
over natural moduli. At a positive modulus this is the usual Gauss sum. -/
def naturalGaussSum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :=
  ∑c∈range q,χ c*Complex.exp (2*Real.pi*I*(n:ℂ)*(c:ℂ)/(q:ℂ))

/-- At every nonzero modulus, the representative formula agrees with the
Gauss sum of the standard additive character. -/
theorem naturalGaussSum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    naturalGaussSum χ n=DirichletLFunctions.gaussSum χ n := (gaussSum_nat_eq_sum_range χ n).symm

/-- The complete Gauss-sum transform of any finite polynomial. -/
theorem gauss_polynomial_transform {q : ℕ} [NeZero q] (a : ℕ→ℂ) (M N : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ n∈Ioc M (M+N),a n*naturalGaussSum (star χ) n)=
      ∑c∈(range q).filter (fun c => c.Coprime q),star (χ c)*trigPoly a M N ((c:ℝ)/q) := by
  have he (n:ℕ) : a n*naturalGaussSum (star χ) n =
      ∑c∈(range q).filter (fun c => c.Coprime q),star (χ c)*(a n*e ((c:ℝ)/q*n)) := by
    rw [naturalGaussSum,mul_sum,sum_filter]
    apply sum_congr rfl;intro c hc
    by_cases hh : c.Coprime q
    · simp only [if_pos hh,MulChar.star_apply,e]
      push_cast
      rw [show 2*(Real.pi:ℂ)*I*n*c/q=2*(Real.pi:ℂ)*((c:ℂ)/q*n)*I by ring];ring
    · have hz := (char_nat_eq_zero_iff_not_coprime χ c).mpr hh
      simp [hh,hz,MulChar.star_apply]
  simp_rw [he];rw [sum_comm]
  apply sum_congr rfl;intro c _;rw [trigPoly,mul_sum]

/-- At one modulus, the totient-normalized character energy equals the
energy at additive samples of that exact denominator. -/
theorem gauss_polynomial_parseval {q : ℕ} [NeZero q] (a : ℕ→ℂ) (M N : ℕ) :
    (q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q,‖∑n∈Ioc M (M+N),a n*naturalGaussSum (star χ) n‖^2 =
      ∑c∈(range q).filter (fun c => c.Coprime q),‖trigPoly a M N ((c:ℝ)/q)‖^2 := by
  simp_rw [gauss_polynomial_transform a M N]
  rw [character_transform_parseval (fun c => trigPoly a M N ((c:ℝ)/q)),←mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'),one_mul]

/-- Large sieve for the Gauss transforms of all characters and arbitrary
coefficients, with the sharp Farey upper bound. -/
theorem gauss_polynomial_large_sieve (a : ℕ→ℂ) (M : ℕ) {N Q : ℕ} (hN : 1≤N) (hQ : 1≤Q) :
    (∑q∈Icc 1 Q,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q,‖∑n∈Ioc M (M+N),a n*naturalGaussSum (star χ) n‖^2)
      ≤ ((N:ℝ)-1+(Q:ℝ)^2)*∑n∈Ioc M (M+N),‖a n‖^2 := by
  apply le_trans _ (farey_large_sieve a M hN hQ)
  apply sum_le_sum;intro q hq
  letI : NeZero q := ⟨Nat.ne_of_gt (mem_Icc.mp hq).1⟩
  exact (gauss_polynomial_parseval a M N).le

end AnalyticNumberTheory.SieveMethods
