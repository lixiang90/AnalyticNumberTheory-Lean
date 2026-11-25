import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialMoments
import AnalyticNumberTheory.RiemannZeta.RiemannDualGamma
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds

/-! # The analytic cross term in the critical-line fourth moment

The product of the error with the reflected short polynomial is holomorphic on a
rectangle extending into absolute convergence. On its left edge it agrees with
the mixed term obtained by expanding the critical-line fourth moment.
-/
noncomputable section
open Complex Real Finset Set
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.RiemannZeta

/-- Error after subtracting the direct and reflected short divisor polynomials. -/
def fourthMomentError (N : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s^2-divisorPolynomial N s-riemannDualGamma s^2*divisorPolynomial N (1-s)

/-- The analytic continuation of the error paired with the conjugate direct polynomial. -/
def fourthMomentCrossTerm (N : ℕ) (s : ℂ) : ℂ :=
  fourthMomentError N s * divisorPolynomial N (1-s)

theorem differentiable_divisorPolynomial (N : ℕ) : Differentiable ℂ (divisorPolynomial N) := by
  intro s
  unfold divisorPolynomial dirichletPoly
  apply DifferentiableAt.fun_sum
  intro n hn
  apply DifferentiableAt.const_mul
  exact (differentiableAt_id.neg).const_cpow (Or.inl (by
    exact_mod_cast (show n≠0 from (show 0<n from (mem_Icc.mp hn).1).ne')))

private theorem norm_divisorPolynomial_crude (N : ℕ) {s : ℂ} (hs : -1 ≤ s.re) :
    ‖divisorPolynomial N s‖ ≤ (N:ℝ)^3 := by
  unfold divisorPolynomial dirichletPoly
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N:ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      have hn₁ := (mem_Icc.mp hn).1
      have hnN : (n:ℝ)≤N := by exact_mod_cast (mem_Icc.mp hn).2
      have hcard : (n.divisors.card:ℝ)≤N := (show (n.divisors.card:ℝ)≤n by exact_mod_cast Nat.card_divisors_le_self n).trans hnN
      rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast_cpow_of_pos hn₁,Complex.neg_re]
      have hv : (n:ℝ)^(-s.re)≤n := (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn₁)
        (by linarith : -s.re≤1)).trans_eq (Real.rpow_one _)
      exact (mul_le_mul hcard (hv.trans hnN) (by positivity) (Nat.cast_nonneg N)).trans_eq (by ring)
    _ = _ := by simp [Nat.card_Icc];ring

/-- Polynomial growth throughout the rectangle is enough for rational interpolation. -/
theorem fourthMomentCrossTerm_crude :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ} {N : ℕ} {s : ℂ}, 4≤T → (N:ℝ)≤T →
      s.re∈Set.Icc (1/2:ℝ) 2 → s.im∈Set.Icc (T/2) (3*T) →
      ‖fourthMomentCrossTerm N s‖≤C*T^6 := by
  obtain ⟨A,hA,HA⟩ := norm_riemannZeta_critical_strip_le_of_two_le (ε:=1/2) (by norm_num)
  obtain ⟨B,hB,HB⟩ := norm_riemannZeta_re_ge_one_le
  obtain ⟨D,hD,HD⟩ := norm_riemannDualGamma_on_strip (1/2) 2
  let K := 4*(1+A+B)
  have hK : 0<K := by dsimp[K];positivity
  refine ⟨K^2+1+D^2,by positivity,?_⟩
  intro T N s hT hN hs ht
  have ht₀ : 2 ≤ |s.im| := by rw [abs_of_nonneg (by linarith [ht.1])];linarith [ht.1]
  have ht₁ : |s.im|≤3*T := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2
  have hz : ‖riemannZeta s‖ ≤ K*T := by
    rcases le_or_gt 1 s.re with h|h
    · have hh := HB h ht₀
      rw [Complex.re_add_im] at hh
      have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < |s.im|+2)
      apply hh.trans
      dsimp [K]
      nlinarith only [mul_le_mul_of_nonneg_left (by linarith : Real.log (|s.im|+2) ≤ 4*T) hB.le,
        mul_nonneg (by linarith : 0 ≤ 1+A) (by linarith : 0≤T)]
    · have hh := HA (show s.re ∈ Set.Icc 0 1 from ⟨by linarith [hs.1],h.le⟩) ht₀
      rw [Complex.re_add_im] at hh
      have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤|s.im|)
        (by linarith [hs.1] : (1-s.re)/2+1/2≤1)
      rw [Real.rpow_one] at hpow
      apply hh.trans
      dsimp [K]
      nlinarith only [mul_le_mul_of_nonneg_left (hpow.trans ht₁) hA.le,
        mul_nonneg (by linarith : 0≤1+B) (by linarith : 0≤T),mul_nonneg hA.le (by linarith : 0≤T)]
  have hg : ‖riemannDualGamma s‖≤D := by
    have hh := HD s hs (by linarith)
    have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤|s.im|) (by linarith [hs.1] : 1/2-s.re≤0)
    simpa using hh.trans (mul_le_mul_of_nonneg_left hpow hD.le)
  have hpowN := pow_le_pow_left₀ (Nat.cast_nonneg N) hN 3
  have hp₁ := (norm_divisorPolynomial_crude N (by linarith [hs.1] : -1≤s.re)).trans hpowN
  have hp₂ := (norm_divisorPolynomial_crude N (s:=1-s) (by simp;linarith [hs.2])).trans hpowN
  have hT₀ : 0≤T := by linarith
  have hzz : ‖riemannZeta s^2‖≤K^2*T^3 := by
    rw [norm_pow]
    apply (pow_le_pow_left₀ (norm_nonneg _) hz 2).trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith : 1≤T) (by norm_num : 2≤3)) (sq_nonneg K)
  have hgp : ‖riemannDualGamma s^2*divisorPolynomial N (1-s)‖ ≤ D^2*T^3 := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hg 2) hp₂ (norm_nonneg _) (sq_nonneg _)
  have hR : ‖fourthMomentError N s‖ ≤ (K^2+1+D^2)*T^3 := by
    unfold fourthMomentError
    apply (norm_sub_le ..).trans
    linarith only [norm_sub_le (riemannZeta s^2) (divisorPolynomial N s),hp₁,hzz,hgp]
  rw [fourthMomentCrossTerm,norm_mul]
  exact (mul_le_mul hR hp₂ (norm_nonneg _) (by positivity)).trans_eq (by ring)

end AnalyticNumberTheory.RiemannZeta
