import AnalyticNumberTheory.PrimeDistribution.PrimitivePsiEnergy

/-! # Uniform cutoff estimates for the Barban conductor sum -/
noncomputable section
open Real Finset
namespace AnalyticNumberTheory.PrimeDistribution

/-- The logarithmic conductor cutoff separates a Siegel–Walfisz term
from the large-sieve terms, uniformly in the upper conductor endpoint. -/
theorem barban_primitive_energy_split (A : ℝ) (hA : 0≤A) :
    ∃C : ℝ,0<C ∧ ∀{x : ℝ},2≤x → 1≤Real.log x → ∀ U : ℕ,
    (∑d∈Icc 2 U,(d.totient:ℝ)⁻¹*primitivePsiEnergy x d)≤
      C*x^2/(Real.log x)^A + (2*(U:ℝ)+2*x/(Real.log x)^(A+1))*((Real.log 4+4)*x*Real.log x) := by
  obtain ⟨C,hC,hsmall⟩ := primitivePsiEnergy_small_conductors A (show 0≤A+1 by linarith)
  refine ⟨C,hC,?_⟩
  intro x hx hl U
  let P := (Real.log x)^(A+1)
  let R := ⌊P⌋₊
  have hp : 1≤P := Real.one_le_rpow hl (by linarith)
  have hp₀ : 0<P := by linarith
  have hr : 1≤R := Nat.le_floor (by simpa using hp)
  have hr' : (1:ℝ)≤R := by exact_mod_cast hr
  have hfloor : ⌊min (U:ℝ) P⌋₊=min U R := by
    by_cases h:(U:ℝ)≤P
    · rw [min_eq_left h,Nat.floor_natCast,min_eq_left (Nat.le_floor h)]
    · rw [min_eq_right (le_of_not_ge h),min_eq_right (by exact_mod_cast (Nat.floor_le hp₀.le).trans (le_of_not_ge h) : R≤U)]
  have hs := hsmall (Q:=(U:ℝ)) hx hl
  change (∑d∈Icc 2 ⌊min (U:ℝ) P⌋₊,_)≤_ at hs
  rw [hfloor] at hs
  have hh := primitivePsiEnergy_large_conductors (by linarith only [hx] : 1≤x) hr U
  have hdiv : x/(R:ℝ)≤2*x/P := by
    rw [div_le_div_iff₀ (by linarith) hp₀]
    have hpr := Nat.lt_floor_add_one P
    change P<(R:ℝ)+1 at hpr
    nlinarith only [mul_le_mul_of_nonneg_left (by linarith : P≤2*R) (by linarith only [hx] : 0≤x)]
  have he : Icc 2 U=Icc 2 (min U R)∪Ioc R U := by
    ext d;simp only [mem_Icc,mem_union,mem_Ioc,le_min_iff];omega
  have hd : Disjoint (Icc 2 (min U R)) (Ioc R U) := disjoint_left.mpr (by
    intro d h₁ h₂;have h₃ := (mem_Icc.mp h₁).2.trans (min_le_right ..);exact (mem_Ioc.mp h₂).1.not_ge h₃)
  rw [he,sum_union hd]
  apply add_le_add hs (hh.trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith only [hdiv]) (by positivity [show 0≤Real.log x by linarith])

end AnalyticNumberTheory.PrimeDistribution
