import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.ZeroHeightSummation

/-! # The reciprocal first moment of nontrivial zeta zeros up to height T -/

noncomputable section

open Finset Complex

namespace AnalyticNumberTheory.PrimeDistribution

private theorem height_le_const_mul_norm :
    ∃ B : ℝ, 0 < B ∧ ∀ {T : ℝ} {ρ : ℂ}, ρ ∈ nontrivialZerosUpTo T → 1+|ρ.im| ≤ B*‖ρ‖ := by
  let F := nontrivialZerosUpTo 1
  let K := ∑ z ∈ F, 2/‖z‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨2+K,by linarith,?_⟩
  intro T ρ hρ
  obtain ⟨hz,hre,hre',_⟩ := mem_nontrivialZerosUpTo.mp hρ
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr (by rintro rfl; simp at hre)
  rcases le_or_gt |ρ.im| 1 with h | h
  · have hmem : ρ ∈ F := mem_nontrivialZerosUpTo.mpr ⟨hz,hre,hre',h⟩
    have hv : 2/‖ρ‖ ≤ K := Finset.single_le_sum (f := fun z : ℂ => 2/‖z‖) (fun _ _ => by positivity) hmem
    have h₂ := (div_le_iff₀ hn).mp hv
    nlinarith
  · nlinarith [Complex.abs_im_le_norm ρ, mul_nonneg hK hn.le]

/-- The sum of m(ρ)/|ρ| over the nontrivial zeros with |Im ρ| ≤ T is O(log² T),
with an absolute constant for every T ≥ 2. -/
theorem sum_zeroMultiplicity_div_norm_le :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 2 ≤ T →
      (∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ : ℝ)/‖ρ‖) ≤ K*(Real.log T)^2 := by
  classical
  obtain ⟨C,hC,HC⟩ := sum_zeroMultiplicity_nontrivialZerosUpTo_le
  obtain ⟨B,hB,HB⟩ := height_le_const_mul_norm
  refine ⟨B*(72*C),by positivity,?_⟩
  intro T hT
  let S := nontrivialZerosUpTo T
  let w (ρ : ℂ) : ℝ := zeroMultiplicity ρ
  let A := 3*C*Real.log T
  have hlog : 1/2 ≤ Real.log T := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hT)
  have hA : 0 ≤ A := by dsimp [A]; positivity [show 0 ≤ Real.log T by linarith]
  have hcount (u : ℝ) (hu : 2 ≤ u) (hut : u ≤ 2*(T+1)) :
      (∑ ρ ∈ S with |ρ.im| ≤ u, w ρ) ≤ A*u+0*Real.sqrt u := by
    have hsub : S.filter (fun ρ => |ρ.im| ≤ u) ⊆ nontrivialZerosUpTo u := by
      intro ρ hρ
      obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hρ
      obtain ⟨h₃,h₄,h₅,_⟩ := mem_nontrivialZerosUpTo.mp h₁
      exact mem_nontrivialZerosUpTo.mpr ⟨h₃,h₄,h₅,h₂⟩
    have hpow : u ≤ T^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T), sq_nonneg (T-1)]
    have hlogs : Real.log u ≤ 3*Real.log T := by simpa [Real.log_pow] using Real.log_le_log (by linarith) hpow
    calc
      _ ≤ ∑ ρ ∈ nontrivialZerosUpTo u, w ρ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ C*u*Real.log u := HC u hu
      _ ≤ C*u*(3*Real.log T) := mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = _ := by dsimp [A]; ring
  have hs := reciprocal_height_sum_le S (fun z : ℂ => |z.im|) w hA (le_refl (0:ℝ)) (by linarith)
    (fun z hz => ⟨abs_nonneg _, (mem_nontrivialZerosUpTo.mp hz).2.2.2⟩)
    (fun _ _ => Nat.cast_nonneg _) hcount
  have hlogs : Real.log (T+1) ≤ 2*Real.log T := by
    have hp : T+1 ≤ T^2 := by nlinarith [sq_nonneg (T-1)]
    simpa [Real.log_pow] using Real.log_le_log (by linarith) hp
  have hs' : (∑ ρ ∈ S, w ρ/(1+|ρ.im|)) ≤ (72*C)*(Real.log T)^2 := by
    apply hs.trans
    have h := mul_le_mul_of_nonneg_left (by linarith : 1+Real.log (T+1) ≤ 4*Real.log T) hA
    dsimp only [A] at *
    nlinarith
  calc
    _ ≤ ∑ ρ ∈ S, B*(w ρ/(1+|ρ.im|)) := by
      apply sum_le_sum
      intro ρ hρ
      have hb := HB hρ
      have hpos : 0 < ‖ρ‖ := by
        apply norm_pos_iff.mpr
        rintro rfl
        exact lt_irrefl 0 (mem_nontrivialZerosUpTo.mp hρ).2.1
      change w ρ/‖ρ‖ ≤ _
      rw [mul_div_assoc' B, div_le_div_iff₀ hpos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ w ρ from Nat.cast_nonneg _)]
    _ = B*(∑ ρ ∈ S, w ρ/(1+|ρ.im|)) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*((72*C)*(Real.log T)^2) := mul_le_mul_of_nonneg_left hs' hB.le
    _ = _ := by ring

end AnalyticNumberTheory.PrimeDistribution
