import AnalyticNumberTheory.PrimeDistribution.SignedCharacterExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.PageRegion

/-! # The contribution of zeros near the right edge of the critical strip -/

noncomputable section

open Finset Complex AnalyticNumberTheory.DirichletLFunctions
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

/-- The regularized Perron sum over the zeros counted by the nonprincipal
density finset. Both the real-part and the ordinate cutoffs are inclusive. -/
def rightmostPerronZeroSum {q : ℕ} (χ : DirichletCharacter ℂ q) (y σ T : ℝ) : ℂ :=
  ∑ z ∈ nonprincipalDensityFinset χ σ T,
    (characterZeroMultiplicity χ z : ℂ) * perronDifferenceWeight y z

/-- Removing the zeros with real part below σ costs at most the full
zero count times (log x) x^σ, uniformly at every endpoint in [1,x]. -/
theorem norm_characterPerronZeroSum_sub_rightmost {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x)
    (σ T : ℝ) :
    ‖characterPerronZeroSum χ y T - rightmostPerronZeroSum χ y σ T‖ ≤
      (zeroCountL χ T : ℝ) * (Real.log x * x ^ σ) := by
  let S := characterStripZeros χ T
  let D := nonprincipalDensityFinset χ σ T
  let m (z : ℂ) : ℝ := characterZeroMultiplicity χ z
  let f (z : ℂ) := (characterZeroMultiplicity χ z : ℂ) * perronDifferenceWeight y z
  have hx := hy.trans hyx
  have hxy : 0 ≤ x := zero_le_one.trans hx
  have hd : D ⊆ S := by
    intro z hz
    obtain ⟨_, hzero, hpos, _, hone, ht⟩ := (mem_nonprincipalDensityFinset χ).mp hz
    exact (mem_characterStripZeros χ).mpr ⟨hpos, hone, (abs_le.mp ht).1, (abs_le.mp ht).2, hzero⟩
  have hweight (z : ℂ) (hz : z ∈ S \ D) :
      ‖f z‖ ≤ m z * (Real.log x * x ^ σ) := by
    obtain ⟨hs, hd'⟩ := mem_sdiff.mp hz
    obtain ⟨hpos, hone, hl, hu, hzero⟩ := (mem_characterStripZeros χ).mp hs
    have hlt : z.re < σ := lt_of_not_ge (fun h =>
      hd' ((mem_nonprincipalDensityFinset χ).mpr ⟨hχ, hzero, hpos, h, hone, abs_le.mpr ⟨hl, hu⟩⟩))
    have hpow : y ^ z.re ≤ x ^ σ :=
      (Real.rpow_le_rpow (zero_le_one.trans hy) hyx hpos.le).trans
        (Real.rpow_le_rpow_of_exponent_le hx hlt.le)
    dsimp only [f, m]
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left ((norm_perronDifferenceWeight_le_log hy hpos).trans
      (mul_le_mul (Real.log_le_log (zero_lt_one.trans_le hy) hyx) hpow
        (Real.rpow_nonneg (zero_le_one.trans hy) _) (Real.log_nonneg hx))) (Nat.cast_nonneg _)
  have hm : ∑ z ∈ S \ D, m z ≤ (zeroCountL χ T : ℝ) := by
    rw [← sum_characterZeroMultiplicity_eq_zeroCountL]
    exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun z _ _ => Nat.cast_nonneg _)
  change ‖(∑ z ∈ S, f z) - ∑ z ∈ D, f z‖ ≤ _
  rw [← sum_sdiff hd (f := f), add_sub_cancel_right]
  calc _ ≤ ∑ z ∈ S \ D, ‖f z‖ := norm_sum_le _ _
       _ ≤ ∑ z ∈ S \ D, m z * (Real.log x * x ^ σ) := sum_le_sum hweight
       _ ≤ _ := by
         rw [← sum_mul]
         exact mul_le_mul_of_nonneg_right hm (mul_nonneg (Real.log_nonneg hx) (Real.rpow_nonneg hxy _))

/-- The explicit formula retaining only zeros with real part at least σ.
A single choice of height and real-part cutoff works for all endpoints. -/
theorem nonprincipal_psi_rightmost_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ {x y T : ℝ}, 0 < T → T ^ 2 ≤ x → 1 ≤ y → y ≤ x → ∀ σ : ℝ,
        ‖psiChar y χ + rightmostPerronZeroSum χ y σ T‖ ≤
          C * (x/T) * (1 + Real.log ((q : ℝ)*x))^2 +
            (zeroCountL χ T : ℝ) * (Real.log x * x ^ σ) := by
  obtain ⟨C, hC, H⟩ := nonprincipal_psi_signed_explicit_at_height
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ x y T hT hTx hy hyx σ
  have h := norm_sub_le (psiChar y χ + characterPerronZeroSum χ y T)
    (characterPerronZeroSum χ y T - rightmostPerronZeroSum χ y σ T)
  rw [show (psiChar y χ + characterPerronZeroSum χ y T) -
    (characterPerronZeroSum χ y T - rightmostPerronZeroSum χ y σ T) =
    psiChar y χ + rightmostPerronZeroSum χ y σ T by abel] at h
  exact h.trans (add_le_add (H hχ hT hTx hy hyx)
    (norm_characterPerronZeroSum_sub_rightmost hχ hy hyx σ T))

private theorem zeroFreeThreshold_mono {a c t T : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ a)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    1 - c / Real.log (a*(t+2)) ≤ 1 - c / Real.log (a*(T+2)) := by
  have hp : 1 < a*(t+2) := by nlinarith only [ha, ht, mul_nonneg (sub_nonneg.mpr ha) ht]
  have hl := Real.log_le_log (zero_lt_one.trans hp)
    (mul_le_mul_of_nonneg_left (add_le_add htT (le_refl 2)) (zero_le_one.trans ha))
  exact sub_le_sub_left (div_le_div_of_nonneg_left hc (Real.log_pos hp) hl) 1

/-- In the classical zero-free rectangle the retained zeros form the empty
set or a singleton consisting of a simple real zero of a real character. -/
theorem nonprincipalDensityFinset_zeroFree_cases :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ {T σ : ℝ}, 0 ≤ T → 1 - c / Real.log ((q : ℝ)*(T+2)) ≤ σ →
        nonprincipalDensityFinset χ σ T = ∅ ∨
          ∃ β : ℝ, 0 < β ∧ σ ≤ β ∧ β < 1 ∧ IsReal χ ∧ χ.LFunction (β : ℂ) = 0 ∧
            characterZeroMultiplicity χ (β : ℂ) = 1 ∧ nonprincipalDensityFinset χ σ T = {(β : ℂ)} := by
  obtain ⟨c, hc, H⟩ := zeroFreeRegion
  refine ⟨c, hc, ?_⟩
  intro q _ χ hχ T σ hT hσ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  let D := nonprincipalDensityFinset χ σ T
  by_cases he : D = ∅
  · exact Or.inl he
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have region {w : ℂ} (hw : w ∈ D) :
      IsReal χ ∧ χ ≠ 1 ∧ w.im = 0 ∧ w.re < 1 ∧ analyticOrderNatAt χ.LFunction w = 1 ∧
        ∀ t : ℝ, 1 - c / Real.log (2*(q : ℝ)) ≤ t → χ.LFunction (t : ℂ) = 0 → t = w.re := by
    obtain ⟨_, hzero, _, hr, _, ht⟩ := (mem_nonprincipalDensityFinset χ).mp hw
    exact H χ w (Or.inl hχ)
      (((zeroFreeThreshold_mono hc.le hq (abs_nonneg w.im) ht).trans hσ).trans hr) hzero
  obtain ⟨hr, _, hzIm, _, hsimple, huniq⟩ := region hz
  obtain ⟨_, hz0, hβ, hσβ, hβ1, _⟩ := (mem_nonprincipalDensityFinset χ).mp hz
  have hez : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzIm.symm)
  refine Or.inr ⟨z.re, hβ, hσβ, hβ1, hr, by rwa [hez], ?_, ?_⟩
  · simpa only [hez, characterZeroMultiplicity, dite_eq_left (NeZero.ne q)] using hsimple
  · ext w
    rw [mem_singleton]
    constructor
    · intro hw
      obtain ⟨_, hzero, _, hσw, _, _⟩ := (mem_nonprincipalDensityFinset χ).mp hw
      have hwIm := (region hw).2.2.1
      have hew : (w.re : ℂ) = w := Complex.ext (by simp) (by simpa using hwIm.symm)
      have hreal : 1 - c / Real.log (2*(q : ℝ)) ≤ w.re := by
        have hh := ((zeroFreeThreshold_mono hc.le hq (le_refl 0) hT).trans hσ).trans hσw
        simpa only [zero_add, mul_comm (q : ℝ) 2] using hh
      exact hew.symm.trans (congrArg (fun t : ℝ => (t : ℂ)) (huniq w.re hreal (by rwa [hew])))
    · intro hw
      rwa [hw, hez]

/-- In the singleton case the retained sum is exactly the real main term
(y^β-1)/β. The same β works at every positive arithmetic endpoint. -/
theorem rightmostPerronZeroSum_of_singleton {q : ℕ} {χ : DirichletCharacter ℂ q}
    {σ T β : ℝ} (hβ : 0 < β) (hs : nonprincipalDensityFinset χ σ T = {(β : ℂ)})
    (hm : characterZeroMultiplicity χ (β : ℂ) = 1) {y : ℝ} (hy : 0 < y) :
    rightmostPerronZeroSum χ y σ T = (((y^β-1)/β : ℝ) : ℂ) := by
  rw [rightmostPerronZeroSum, hs, sum_singleton, hm, Nat.cast_one, one_mul,
    perronDifferenceWeight_eq hy (Complex.ofReal_ne_zero.mpr hβ.ne'),
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow hy.le]

/-- Uniformly for q ≤ Q, Page's exceptional primitive character is the only
one whose induced characters can contribute a zero in this rectangle. -/
theorem page_nonprincipalDensityFinset_empty :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/4 ∧ ∀ {Q : ℝ}, 2 ≤ Q →
      ∃ e : Σ m : ℕ, DirichletCharacter ℂ m,
        (e.1 = 0 ∨ PageExceptionalCharacter Q c e.2) ∧
        ∀ {q : ℕ} [NeZero q], (q : ℝ) ≤ Q → ∀ {χ : DirichletCharacter ℂ q},
          (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ m : ℕ, DirichletCharacter ℂ m) ≠ e →
          ∀ {σ T : ℝ}, 1 - c / Real.log ((Q+2)*(T+2)) ≤ σ →
            nonprincipalDensityFinset χ σ T = ∅ := by
  obtain ⟨c, hc, hc4, H⟩ := page_zeroFree_region_primitiveCharacter
  refine ⟨c, hc, hc4, ?_⟩
  intro Q hQ
  obtain ⟨e, he, hreg⟩ := H hQ
  refine ⟨e, he, ?_⟩
  intro q _ hq χ hne σ T hσ
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hχ, hzero, _, hβ, _, hT⟩ := (mem_nonprincipalDensityFinset χ).mp hz
  exact hreg hq hne hχ
    (((zeroFreeThreshold_mono hc.le (by linarith : 1 ≤ Q+2) (abs_nonneg z.im) hT).trans hσ).trans hβ)
    hzero

end AnalyticNumberTheory.PrimeDistribution
