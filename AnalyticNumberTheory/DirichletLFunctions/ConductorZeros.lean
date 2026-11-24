import AnalyticNumberTheory.DirichletLFunctions.ZeroExpansion

/-!
# Conductor invariance of critical-strip zero counts

The Euler factors introduced by a change of level are nonvanishing in the open
right half-plane. In particular their boundary zeros do not enter the open
critical strip, and all multiplicities there agree with the primitive ones.
-/

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletLFunctions

private noncomputable def levelEulerProduct {d : ℕ} (χ : DirichletCharacter ℂ d) (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - χ p * (p:ℂ)^(-s))

private theorem analyticAt_levelEulerProduct {d : ℕ} (χ : DirichletCharacter ℂ d) (q : ℕ) (s : ℂ) :
    AnalyticAt ℂ (levelEulerProduct χ q) s := by
  apply Differentiable.analyticAt
  intro w
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  apply (differentiableAt_const _).sub
  apply (differentiableAt_const _).mul
  exact differentiableAt_id.neg.const_cpow (Or.inl hp0)

private theorem levelEulerProduct_ne_zero {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (q : ℕ)
    {s : ℂ} (hs : 0 < s.re) : levelEulerProduct χ q s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hlt : ‖χ p * (p:ℂ)^(-s)‖ < 1 := calc
    _ ≤ ‖(p:ℂ)^(-s)‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one _ _)
    _ < 1 := by
      rw [norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_lt_zero.mpr hs)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hlt
  exact hlt.false

/-- On the open critical strip changing the level preserves both the zero
condition and the analytic multiplicity. -/
theorem LFunction_changeLevel_strip_zero_order {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    (DirichletCharacter.LFunction (χ.changeLevel hdq) s = 0 ↔ DirichletCharacter.LFunction χ s = 0) ∧
    analyticOrderNatAt (DirichletCharacter.LFunction (χ.changeLevel hdq)) s =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) s := by
  have hsne : s ≠ 1 := by rintro rfl; simp at hs1
  have he : DirichletCharacter.LFunction (χ.changeLevel hdq) =ᶠ[𝓝 s]
      (DirichletCharacter.LFunction χ * levelEulerProduct χ q) := by
    filter_upwards [isOpen_ne.mem_nhds hsne] with w hw using LFunction_changeLevel_eq hdq χ (Or.inr hw)
  have hp := levelEulerProduct_ne_zero χ q hs
  constructor
  · rw [he.eq_of_nhds, Pi.mul_apply, mul_eq_zero]
    exact or_iff_left hp
  · have hana : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
      have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {w : ℂ | w ≠ 1} :=
        fun w hw => (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
      exact hd.analyticAt (isOpen_ne.mem_nhds hsne)
    simp only [analyticOrderNatAt, analyticOrderAt_congr he, analyticOrderAt_mul hana (analyticAt_levelEulerProduct χ q s),
      (analyticAt_levelEulerProduct χ q s).analyticOrderAt_eq_zero.mpr hp, add_zero]

/-- Critical strip zeros of the induced character are exactly the primitive
ones with the same multiplicities, for every height (including zero). -/
theorem zeroCountL_changeLevel {d q : ℕ} [NeZero d] [NeZero q] (hdq : d ∣ q)
    (χ : DirichletCharacter ℂ d) (T : ℝ) : zeroCountL (χ.changeLevel hdq) T = zeroCountL χ T := by
  classical
  have he : criticalStripZeroFinset (χ.changeLevel hdq) (-T) T = criticalStripZeroFinset χ (-T) T := by
    ext s
    simp only [mem_criticalStripZeroFinset]
    constructor
    · rintro ⟨h0,h1,ht,ht',hz⟩
      exact ⟨h0,h1,ht,ht',(LFunction_changeLevel_strip_zero_order hdq χ h0 h1).1.mp hz⟩
    · rintro ⟨h0,h1,ht,ht',hz⟩
      exact ⟨h0,h1,ht,ht',(LFunction_changeLevel_strip_zero_order hdq χ h0 h1).1.mpr hz⟩
  rw [zeroCountL, zeroCountL, he]
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨h0,h1,_⟩ := (mem_criticalStripZeroFinset χ).mp hs
  exact (LFunction_changeLevel_strip_zero_order hdq χ h0 h1).2

/-- The level in the zero count can be replaced by the conductor. -/
theorem zeroCountL_eq_primitiveCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (T : ℝ) : zeroCountL χ T = zeroCountL χ.primitiveCharacter T := by
  simpa only [χ.changeLevel_primitiveCharacter] using
    zeroCountL_changeLevel χ.conductor_dvd_level χ.primitiveCharacter T

end AnalyticNumberTheory.DirichletLFunctions
