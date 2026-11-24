import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LocalPowerSums

/-!
# Scaled reciprocal moments of nearby zeros

The real part of the first reciprocal-zero sum bounds the square mass of the
scaled reciprocal zeros. A subdisk of radius proportional to the distance from the zero-free line
therefore contains only a bounded multiple of this mass.
-/

noncomputable section

open Complex Metric Finset
open scoped Classical

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Reciprocal-square mass of the zeros on a fixed disk, scaled by the
distance of the center from a zero-free half-plane. -/
theorem exists_local_scaled_inverse_square_mass {f : ℂ → ℂ} {c : ℂ} {η G B D : ℝ}
    (hη : 0 < η) (hc : c.re = 1+η) (hf : AnalyticOnNhd ℂ f (closedBall c (3/4)))
    (hn : ∀ u : ℂ, 1 ≤ u.re → f u ≠ 0) (hG : 0 < G)
    (hg : ∀ w ∈ sphere c (3/4), ‖f w/f c‖ ≤ G)
    (hDG : 352*Real.log G ≤ D) (hB : ‖logDeriv f c‖ ≤ B) :
    ∃ Z : Finset ℂ, (Z : Set ℂ) = zeroSet f c (3/8) ∧
      (∑ u ∈ Z, (analyticOrderNatAt f u:ℝ)*‖(η:ℂ)*(c-u)⁻¹‖^2 ≤ η*(B+D)) ∧
      ∀ k : ℕ, ‖signedTaylorCoeff (logDeriv f) c k -
        ∑ u ∈ Z, (analyticOrderNatAt f u:ℂ)*(c-u)⁻¹^(k+1)‖ ≤ 352*Real.log G*(16/5:ℝ)^k := by
  have hcn : f c ≠ 0 := hn _ (by linarith)
  obtain ⟨Z,hZ,_,he⟩ := local_logDeriv_power_sum hG hf hcn hg
  let m (u : ℂ) := analyticOrderNatAt f u
  let v (u : ℂ) := (η:ℂ)*(c-u)⁻¹
  have hzero {u : ℂ} (hu : u ∈ Z) : u ∈ closedBall c (3/8) ∧ f u = 0 := by
    apply mem_zeroSet.mp; rw [←hZ]; exact hu
  have hnrm (u : ℂ) : ‖v u‖ = η/‖c-u‖ := by
    rw [show v u = _ from rfl,norm_mul,Complex.norm_real,Real.norm_of_nonneg hη.le,norm_inv,div_eq_mul_inv]
  have hsep {u : ℂ} (hu : u ∈ Z) : η ≤ (c-u).re := by
    have hlt : u.re < 1 := lt_of_not_ge fun h => hn _ h (hzero hu).2
    rw [sub_re,hc]; linarith
  have hdist {u : ℂ} (hu : u ∈ Z) : 0 < ‖c-u‖ := hη.trans_le ((hsep hu).trans (re_le_norm _))
  have henergy (u : ℂ) (hu : u ∈ Z) : (m u:ℝ)*‖v u‖^2 ≤ η*((m u:ℝ)*((c-u)⁻¹).re) := by
    rw [hnrm,div_pow,Complex.inv_re,Complex.normSq_eq_norm_sq]
    have hp : 0 < ‖c-u‖^2 := sq_pos_of_pos (hdist hu)
    rw [show (m u:ℝ)*(η^2/‖c-u‖^2) = ((m u:ℝ)*η^2)/‖c-u‖^2 by ring,
      show η*((m u:ℝ)*((c-u).re/‖c-u‖^2)) = ((m u:ℝ)*η*(c-u).re)/‖c-u‖^2 by ring]
    apply div_le_div_of_nonneg_right _ hp.le
    rw [pow_two,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (hsep hu) (by positivity)
  let V := ∑ u ∈ Z, (m u:ℂ)*(c-u)⁻¹
  have hfirst : ‖logDeriv f c-V‖ ≤ D := by
    have h := he 0
    simp only [signedTaylorCoeff,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul,iteratedDeriv_zero,
      zero_add,pow_one,mul_one] at h
    exact h.trans hDG
  have hV : V.re ≤ B+D := by
    have h := norm_sub_le (logDeriv f c) (logDeriv f c-V)
    rw [sub_sub_cancel] at h
    exact (re_le_norm _).trans (h.trans (add_le_add hB hfirst))
  have hsum : ∑ u ∈ Z, (m u:ℝ)*‖v u‖^2 ≤ η*(B+D) := by
    apply (sum_le_sum henergy).trans
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left _ hη.le
    simpa only [V,re_sum,mul_re,natCast_re,natCast_im,zero_mul,sub_zero] using hV
  exact ⟨Z,hZ,hsum,he⟩

/-- Local zero count, with analytic multiplicity, inside radius `2η` of a point
at horizontal distance `η` from the zero-free half-plane. -/
theorem local_logDeriv_zero_count {f : ℂ → ℂ} {c : ℂ} {η G B D : ℝ}
    (hη : 0 < η) (hη' : 2*η ≤ 3/8) (hc : c.re = 1+η) (hf : AnalyticOnNhd ℂ f (closedBall c (3/4)))
    (hn : ∀ u : ℂ, 1 ≤ u.re → f u ≠ 0) (hG : 0 < G)
    (hg : ∀ w ∈ sphere c (3/4), ‖f w/f c‖ ≤ G)
    (hDG : 352*Real.log G ≤ D) (hB : ‖logDeriv f c‖ ≤ B) (S : Finset ℂ)
    (hS : ∀ u ∈ S, f u = 0 ∧ ‖c-u‖ ≤ 2*η) :
    (∑ u ∈ S, (analyticOrderNatAt f u:ℝ)) ≤ 4*(η*(B+D)) := by
  obtain ⟨Z,hZ,hsum,_⟩ := exists_local_scaled_inverse_square_mass hη hc hf hn hG hg hDG hB
  have hsub : S ⊆ Z := by
    intro u hu; change u ∈ (Z:Set ℂ)
    rw [hZ]; refine ⟨?_,(hS u hu).1⟩
    rw [mem_closedBall,Complex.dist_eq,norm_sub_rev]; exact (hS u hu).2.trans hη'
  have hmass := (sum_le_sum_of_subset_of_nonneg hsub
    (f:=fun u => (analyticOrderNatAt f u:ℝ)*‖(η:ℂ)*(c-u)⁻¹‖^2) (fun _ _ _ => by positivity)).trans hsum
  calc
    _ ≤ ∑ u ∈ S, 4*((analyticOrderNatAt f u:ℝ)*‖(η:ℂ)*(c-u)⁻¹‖^2) := by
      refine sum_le_sum fun u hu => ?_
      have hdist : 0 < ‖c-u‖ := by
        apply norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
        rintro rfl; exact hn c (by linarith) (hS c hu).1
      have hs : 1/2 ≤ ‖(η:ℂ)*(c-u)⁻¹‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hη.le,norm_inv,←div_eq_mul_inv,le_div_iff₀ hdist]
        linarith [(hS u hu).2]
      have hh := pow_le_pow_left₀ (by norm_num : 0≤(1/2:ℝ)) hs 2
      nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) (analyticOrderNatAt f u))]
    _ ≤ _ := by rw [←mul_sum]; gcongr

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
