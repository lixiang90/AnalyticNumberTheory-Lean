import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The real density for sums of powers

The volume of the part of a power ball in the positive orthant is a power
of its level `t`. Its derivative gives the real density for Waring's problem.
-/

namespace AnalyticNumberTheory.AdditiveNumberTheory

open MeasureTheory Set Real
open scoped ENNReal NNReal

private theorem map_abs_volume :
    Measure.map (abs : ℝ → ℝ) volume = (2 : ℝ≥0) • volume.restrict (Ici 0) := by
  ext s hs
  have heq : (abs : ℝ → ℝ) ⁻¹' s = (s ∩ Ici 0) ∪ (fun x : ℝ => -x) ⁻¹' (s ∩ Ioi 0) := by
    ext x
    by_cases hx : 0 ≤ x <;> simp [hx, abs_of_nonneg, abs_of_neg, lt_of_not_ge, not_lt.mpr]
  have hdisj : Disjoint (s ∩ Ici 0) ((fun x : ℝ => -x) ⁻¹' (s ∩ Ioi 0)) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have hneg : 0 < -x := hy.2
    have hpos : 0 ≤ x := hx.2
    linarith
  have hneg := congrArg (fun μ : Measure ℝ => μ (s ∩ Ioi 0)) (Measure.map_neg_eq_self volume)
  simp only [Measure.map_apply measurable_neg (hs.inter measurableSet_Ioi)] at hneg
  have hnull : volume (s ∩ Ioi 0) = volume (s ∩ Ici 0) := by
    rw [← Measure.restrict_apply hs, ← Measure.restrict_apply hs, restrict_Ioi_eq_restrict_Ici]
  rw [Measure.map_apply continuous_abs.measurable hs, heq,
    measure_union hdisj (measurable_neg (hs.inter measurableSet_Ioi)), hneg, hnull,
    smul_apply, Measure.restrict_apply hs]
  change _ = 2 * volume (s ∩ Ici 0)
  rw [two_mul]

private theorem map_pi_abs_volume (s : ℕ) :
    Measure.map (fun (x : Fin s → ℝ) i => |x i|) volume =
      ((2 : ℝ≥0) ^ s) • (volume : Measure (Fin s → ℝ)).restrict (univ.pi fun _ => Ici 0) := by
  have : SigmaFinite (Measure.map (abs : ℝ → ℝ) volume) := by rw [map_abs_volume]; infer_instance
  rw [show (volume : Measure (Fin s → ℝ)) = Measure.pi (fun _ : Fin s => (volume : Measure ℝ)) from rfl,
    Measure.pi_map_pi (f := fun _ : Fin s => (abs : ℝ → ℝ)) (fun _ => continuous_abs.aemeasurable)]
  simp only [map_abs_volume]
  apply Measure.pi_eq
  intro A hA
  rw [smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hA), ← Set.pi_inter_distrib,
    Measure.pi_pi]
  simp only [smul_apply, Measure.restrict_apply (hA _)]
  change ((2 : ℝ≥0∞) ^ s) * (∏ i, volume (A i ∩ Ici 0)) = ∏ i, 2 * volume (A i ∩ Ici 0)
  simp [Finset.prod_mul_distrib]

/-- The real vectors with nonnegative coordinates whose `k`th powers sum to at most `t`. -/
def waringRegion (s k : ℕ) (t : ℝ) : Set (Fin s → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ^ k ≤ t}

/-- For negative levels the Waring region is empty. -/
theorem waringRegion_eq_empty_of_neg (s k : ℕ) {t : ℝ} (ht : t < 0) :
    waringRegion s k t = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact ht.not_ge ((Finset.sum_nonneg fun i _ => pow_nonneg (hx.1 i) k).trans hx.2)

/-- Lebesgue volume of the nonnegative portion of the `k`th power ball,
including the boundary at the level `t = 0`. -/
theorem volume_waringRegion {s k : ℕ} (hs : 0 < s) (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) :
    volume (waringRegion s k t) = ENNReal.ofReal
      (t ^ ((s : ℝ) / k) * (Gamma (1 / k + 1) ^ s / Gamma ((s : ℝ) / k + 1))) := by
  have : NeZero s := ⟨hs.ne'⟩
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let A := {x : Fin s → ℝ | ∑ i, x i ^ k ≤ t}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hreg : A ∩ univ.pi (fun _ => Ici (0 : ℝ)) = waringRegion s k t := by
    ext x
    simp [A, waringRegion, and_comm, Pi.le_def]
  have hfold := congrArg (fun μ : Measure (Fin s → ℝ) => μ A) (map_pi_abs_volume s)
  simp only [Measure.map_apply (by fun_prop : Measurable (fun (x : Fin s → ℝ) i => |x i|)) hA,
    smul_apply, Measure.restrict_apply hA, hreg, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_pow, ENNReal.coe_ofNat] at hfold
  have hfull := volume_sum_rpow_le (Fin s) (show (1 : ℝ) ≤ k by exact_mod_cast hk)
    (t ^ (1 / (k : ℝ)))
  simp only [Fintype.card_fin, Real.rpow_natCast] at hfull
  have hball : {x : Fin s → ℝ | (∑ i, |x i| ^ k) ^ (1 / (k : ℝ)) ≤ t ^ (1 / (k : ℝ))} =
      (fun (x : Fin s → ℝ) i => |x i|) ⁻¹' A := by
    ext x
    exact Real.rpow_le_rpow_iff (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _) ht
      (one_div_pos.mpr hkR)
  rw [hball, hfold] at hfull
  apply (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞) ^ s) (by positivity) (by finiteness)).mp
  rw [hfull, ← ENNReal.ofReal_pow (Real.rpow_nonneg ht _) _, ← Real.rpow_mul_natCast ht,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht _)]
  have htwo : (2 : ℝ≥0∞) ^ s = ENNReal.ofReal ((2 : ℝ) ^ s) := by simp [ENNReal.ofReal_pow]
  rw [htwo, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (1 / (k : ℝ)) * (s : ℝ) = s / k by ring, mul_pow]
  ring

/-- The real-valued volume function used to define the archimedean density. -/
noncomputable def waringVolume (s k : ℕ) (t : ℝ) : ℝ := (volume (waringRegion s k t)).toReal

theorem waringVolume_eq {s k : ℕ} (hs : 0 < s) (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) :
    waringVolume s k t = t ^ ((s : ℝ) / k) * (Gamma (1 / k + 1) ^ s / Gamma ((s : ℝ) / k + 1)) := by
  rw [waringVolume, volume_waringRegion hs hk ht, ENNReal.toReal_ofReal]
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  exact mul_nonneg (Real.rpow_nonneg ht _) (div_nonneg (pow_nonneg (Gamma_pos_of_pos (by positivity)).le _)
    (Gamma_pos_of_pos (by positivity)).le)

/-- Differentiating the volume at a positive level replaces `Γ(s/k + 1)`
by `Γ(s/k)` and lowers the power of `t` by one. -/
theorem hasDerivAt_waringVolume {s k : ℕ} (hs : 0 < s) (hk : 0 < k) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (waringVolume s k)
      ((Gamma (1 / k + 1) ^ s / Gamma ((s : ℝ) / k)) * t ^ ((s : ℝ) / k - 1)) t := by
  have he : 0 < (s : ℝ) / k := div_pos (Nat.cast_pos.mpr hs) (Nat.cast_pos.mpr hk)
  have hder := (Real.hasDerivAt_rpow_const (p := (s : ℝ) / k) (Or.inl ht.ne')).mul_const
    (Gamma (1 / k + 1) ^ s / Gamma ((s : ℝ) / k + 1))
  have hder' := hder.congr_of_eventuallyEq (f₁ := waringVolume s k)
    (by filter_upwards [lt_mem_nhds ht] with u hu using waringVolume_eq hs hk hu.le)
  convert hder' using 1
  rw [Gamma_add_one he.ne']
  field_simp [he.ne', (Gamma_pos_of_pos he).ne']

end AnalyticNumberTheory.AdditiveNumberTheory
