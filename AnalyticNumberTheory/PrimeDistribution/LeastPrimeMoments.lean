import AnalyticNumberTheory.PrimeDistribution.LeastPrime
import AnalyticNumberTheory.DirichletLFunctions.TuranPrimeWindow

/-!
# Detecting the least prime by high-order logarithmic derivatives

A moment at the fixed real point 1+1/1024 concentrates on primes below
exp(65536 m). Taking the Fourier coefficient in the finite character group
selects a reduced residue class. On the prime window above the modulus, a
character and its inducing primitive character have identical values.
-/
noncomputable section
open Finset Complex
open scoped Classical ArithmeticFunction
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.PrimeDistribution

/-- The normalized degree-m moment of a character's inducing primitive
L-function, evaluated on the real axis. -/
def primitivePrimeMoment {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  ∑' n, turanMangoldtTerm χ.primitiveCharacter (1/1024) 0 m n

theorem primitivePrimeMoment_eq_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (m : ℕ) :
    primitivePrimeMoment χ m = -(1/1024:ℂ)^(m+1)*
      signedTaylorCoeff (logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter)) (1+1/1024) m := by
  have h := (hasSum_turanMangoldtTerm χ.primitiveCharacter (by norm_num : (0:ℝ)<1/1024) 0 m).tsum_eq
  simpa only [primitivePrimeMoment,Complex.ofReal_zero,zero_mul,add_zero,Complex.ofReal_add,Complex.ofReal_one,
    Complex.ofReal_div,Complex.ofReal_ofNat] using h

/-- A finite, uniform least-prime criterion. If the character moment selecting
a reduced class exceeds the exponentially small truncation error, that class
contains a prime below exp(65536 m). No Euler factor corrections enter. -/
theorem leastPrimeAP_le_of_primitivePrimeMoment :
    ∃ D : ℝ, 0<D ∧ ∀ {q a : ℕ} [NeZero q] (ha : a.Coprime q) (m : ℕ),
      Real.log q≤m →
      (q.totient:ℝ)*D*(1/256:ℝ)^m <
        ‖∑ χ : DirichletCharacter ℂ q,star (χ a)*primitivePrimeMoment χ m‖ →
      (leastPrimeAP (NeZero.ne q) ha:ℝ) ≤ Real.exp (65536*m) := by
  obtain ⟨D,hD,htr⟩ := turan_prime_window_error
  refine ⟨D,hD,fun {q a} _ ha m hm hlarge => ?_⟩
  let U := Real.exp (65536*m)
  let W := turanPrimes q U
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hU : (q:ℝ)≤U := by
    rw [←Real.log_le_log_iff (by positivity) (Real.exp_pos _), Real.log_exp]
    linarith [Nat.cast_nonneg (α:=ℝ) m]
  let P := fun χ : DirichletCharacter ℂ q => ∑ n ∈ W,turanMangoldtTerm χ.primitiveCharacter (1/1024) 0 m n
  have hdiff (χ : DirichletCharacter ℂ q) : ‖primitivePrimeMoment χ m-P χ‖ ≤ D*(1/256:ℝ)^m := by
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    exact htr χ.primitiveCharacter (by norm_num) le_rfl 0 m hq hU (by linarith) (by dsimp [U]; rw [Real.log_exp]; linarith)
  by_contra! hbad
  have hzero : ∑ χ : DirichletCharacter ℂ q,star (χ a)*P χ = 0 := by
    dsimp only [P]; simp_rw [mul_sum]; rw [sum_comm]
    apply sum_eq_zero
    intro n hn
    obtain ⟨hint,hp⟩ := mem_filter.mp hn
    obtain ⟨hqn,hnU⟩ := mem_Ioc.mp hint
    rw [Nat.floor_natCast] at hqn
    have hcop : n.Coprime q := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hqn)
    have hne : ¬n≡a [MOD q] := by
      intro hc
      have hb := leastPrimeAP_le (NeZero.ne q) ha hp hc
      have hu : (n:ℝ)≤U := (Nat.le_floor_iff' hp.ne_zero).mp hnU
      exact (not_le_of_gt hbad) ((by exact_mod_cast hb : (leastPrimeAP (NeZero.ne q) ha:ℝ) ≤ n).trans hu)
    have hc (χ : DirichletCharacter ℂ q) : χ.primitiveCharacter n=χ n := by
      have hv := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level
        (Nat.isCoprime_iff_coprime.mpr hcop)
      simpa only [Int.cast_natCast,χ.changeLevel_primitiveCharacter] using hv.symm
    simp_rw [turanMangoldtTerm,Complex.ofReal_zero,neg_zero,zero_mul,Complex.cpow_zero,mul_one,hc]
    have he (χ : DirichletCharacter ℂ q) (v : ℂ) : star (χ a)*(v*χ n)=v*(χ n*star (χ a)) := by ring
    simp_rw [he,←mul_sum,sum_chars_nat_mul_conj_eq n ha,if_neg hne,mul_zero]
  have hsum : (∑ χ : DirichletCharacter ℂ q,star (χ a)*primitivePrimeMoment χ m) =
      ∑ χ : DirichletCharacter ℂ q,star (χ a)*(primitivePrimeMoment χ m-P χ) := by
    simp_rw [mul_sub,sum_sub_distrib,hzero,sub_zero]
  rw [hsum] at hlarge
  have hbound : ‖∑ χ : DirichletCharacter ℂ q,star (χ a)*(primitivePrimeMoment χ m-P χ)‖ ≤
      ∑ _χ : DirichletCharacter ℂ q,D*(1/256:ℝ)^m := by
    refine (norm_sum_le _ _).trans (sum_le_sum (fun χ _ => ?_))
    rw [norm_mul,norm_star]
    exact (mul_le_mul (norm_char_le_one χ _) (hdiff χ) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simp only [sum_const,card_univ,nsmul_eq_mul,card_dirichletCharacter_eq_totient] at hbound
  linarith

end AnalyticNumberTheory.PrimeDistribution
