import AnalyticNumberTheory.AdditiveNumberTheory.WaringDiminishingRanges
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scales for the diminishing-ranges construction

Taking floors after a single degree-dependent rescaling produces integer
dyadic boxes with controlled volume and disjoint sums of powers.
-/

open Finset Filter Real
open scoped Topology
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Integer dyadic cutoff for the `j`-th successively shortened variable. -/
noncomputable def waringDiminishingCutoff (k P j : ℕ) : ℕ :=
  ⌊(4:ℝ)⁻¹^k*(P:ℝ)^((1-1/(k:ℝ))^j)⌋₊

private theorem cutoff_scale {k : ℕ} (hk : 1≤k) :
    (2*((4:ℝ)⁻¹^k))^k ≤ ((4:ℝ)⁻¹^k/2)^(k-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  change (2*((4:ℝ)⁻¹^(n+1)))^(n+1) ≤ ((4:ℝ)⁻¹^(n+1)/2)^n
  let c := (4:ℝ)⁻¹^(n+1)
  have he : 2*c*(4:ℝ)^n=1/2 := by dsimp [c]; rw [pow_succ, inv_pow]; field_simp; ring
  change (2*c)^(n+1) ≤ (c/2)^n
  calc
    _ = (2*c*4^n)*(c/2)^n := by rw [pow_succ, mul_assoc,← mul_pow]; ring_nf
    _ ≤ _ := by rw [he]; nlinarith [pow_nonneg (show 0≤c/2 by dsimp [c]; positivity) n]

private theorem diminishing_ratio_pos {k : ℕ} (hk : 2≤k) : 0<1-1/(k:ℝ) := by
  have h : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr h)

private theorem cutoff_floor_bounds {k : ℕ} (hk : 2≤k) (j : ℕ) :
    ∀ᶠ P : ℕ in atTop, 0<waringDiminishingCutoff k P j ∧
      ((4:ℝ)⁻¹^k/2)*(P:ℝ)^((1-1/(k:ℝ))^j) ≤ waringDiminishingCutoff k P j ∧
      (waringDiminishingCutoff k P j:ℝ)≤(4:ℝ)⁻¹^k*(P:ℝ)^((1-1/(k:ℝ))^j) := by
  have h := ((tendsto_rpow_atTop (pow_pos (diminishing_ratio_pos hk) j)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop (show 0<(4:ℝ)⁻¹^k by positivity)
  filter_upwards [h.eventually_ge_atTop 2] with P hP
  let X := (4:ℝ)⁻¹^k*(P:ℝ)^((1-1/(k:ℝ))^j)
  change 2≤X at hP
  change 0<⌊X⌋₊ ∧ _ ∧ (⌊X⌋₊:ℝ)≤X
  exact ⟨Nat.floor_pos.mpr (by linarith),by
    change _≤(⌊X⌋₊:ℝ)
    have hfloor := Nat.lt_floor_add_one X
    dsimp [X] at *
    linarith, Nat.floor_le (by linarith)⟩

private theorem cutoff_power_step {k P j : ℕ} (hk : 2≤k) (hP : 0<P)
    (hlo : ((4:ℝ)⁻¹^k/2)*(P:ℝ)^((1-1/(k:ℝ))^j) ≤ waringDiminishingCutoff k P j)
    (hhi : (waringDiminishingCutoff k P (j+1):ℝ) ≤ (4:ℝ)⁻¹^k*(P:ℝ)^((1-1/(k:ℝ))^(j+1))) :
    (2*waringDiminishingCutoff k P (j+1))^k ≤ (waringDiminishingCutoff k P j)^(k-1) := by
  let u := 1-1/(k:ℝ)
  let c := (4:ℝ)⁻¹^k
  have hp : (0:ℝ)<P := by exact_mod_cast hP
  have hkr : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hex : u^(j+1)*(k:ℝ) = u^j*((k-1:ℕ):ℝ) := by
    rw [pow_succ, mul_assoc, Nat.cast_sub (by omega : 1≤k)]
    congr 1
    dsimp [u]; field_simp; norm_num
  have he : ((P:ℝ)^(u^(j+1)))^k = ((P:ℝ)^(u^j))^(k-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, hex, Real.rpow_mul hp.le,Real.rpow_natCast]
  exact_mod_cast (calc
    (2*(waringDiminishingCutoff k P (j+1):ℝ))^k ≤ ((2*c)*(P:ℝ)^(u^(j+1)))^k := by
      rw [mul_assoc]; gcongr
    _ = (2*c)^k * ((P:ℝ)^(u^j))^(k-1) := by rw [mul_pow,he]
    _ ≤ (c/2)^(k-1)*((P:ℝ)^(u^j))^(k-1) := by
      apply mul_le_mul_of_nonneg_right (cutoff_scale (by omega)) (by positivity)
    _ ≤ (waringDiminishingCutoff k P j:ℝ)^(k-1) := by rw [← mul_pow]; gcongr)

/-- Eventually every box in a fixed list is nonempty and the gaps between
adjacent powers dominate the following box. -/
theorem eventually_waringDiminishingCutoff_admissible {k : ℕ} (hk : 2≤k) (m : ℕ) :
    ∀ᶠ P : ℕ in atTop, (∀ j, j<m → 0<waringDiminishingCutoff k P j) ∧
      ∀ j, j+1<m → (2*waringDiminishingCutoff k P (j+1))^k ≤ (waringDiminishingCutoff k P j)^(k-1) := by
  have hall := (eventually_all (ι:=Fin m)).mpr (fun i => cutoff_floor_bounds hk i)
  filter_upwards [hall,eventually_ge_atTop 1] with P h hP
  exact ⟨fun j hj => (h ⟨j,hj⟩).1,fun j hj => cutoff_power_step hk (by omega)
    (h ⟨j,by omega⟩).2.1 (h ⟨j+1,hj⟩).2.2⟩

/-- The volume of the product of boxes has exponent `k(1-(1-1/k)^m)` in the main cutoff. -/
theorem waringDiminishingCutoff_product_lower {k : ℕ} (hk : 2≤k) (m : ℕ) :
    ∃ d>(0:ℝ), ∀ᶠ P : ℕ in atTop,
      d*(P:ℝ)^((k:ℝ)*(1-(1-1/(k:ℝ))^m)) ≤ ∏ i : Fin m, (waringDiminishingCutoff k P i:ℝ) := by
  let u := 1-1/(k:ℝ)
  let c := (4:ℝ)⁻¹^k/2
  have hgeo : (∑ i : Fin m, u^i.val) = (k:ℝ)*(1-u^m) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => u^j)]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih, pow_succ]
      dsimp [u]
      field_simp
      ring
  refine ⟨c^m,by dsimp [c]; positivity,?_⟩
  have hall := (eventually_all (ι:=Fin m)).mpr (fun i => cutoff_floor_bounds hk i)
  filter_upwards [hall,eventually_ge_atTop 1] with P h hP
  have hp : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  change c^m*(P:ℝ)^((k:ℝ)*(1-u^m))≤_
  rw [← hgeo, Real.rpow_sum_of_pos hp]
  calc
    _ = ∏ i : Fin m, (c*(P:ℝ)^(u^i.val)) := by simp [prod_mul_distrib]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by dsimp [c]; positivity) (fun i _ => (h i).2.1)

/-- Every individual shift uses at most an eighth of the ambient power scale. -/
theorem eventually_waringDiminishingValues_small {k : ℕ} (hk : 3≤k) (m : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ a∈waringDiminishingValues k m (waringDiminishingCutoff k P),
      (a:ℝ) ≤ (P:ℝ)^k/8 := by
  let c := (4:ℝ)⁻¹^k
  have hc : c≤1/64 := by
    have h := pow_le_pow_of_le_one (by norm_num : 0≤(4:ℝ)⁻¹) (by norm_num : (4:ℝ)⁻¹≤1) hk
    norm_num at h
    simpa [c,one_div] using h
  have hc0 : 0≤c := by dsimp [c]; positivity
  have hc1 : (2*c)^k≤1/16 := by
    have h := pow_le_pow_of_le_one (by linarith : 0≤2*c) (by linarith : 2*c≤1) (by omega : 1≤k)
    rw [pow_one] at h
    linarith
  filter_upwards [eventually_waringDiminishingCutoff_admissible (by omega : 2≤k) m,
    cutoff_floor_bounds (by omega : 2≤k) 0] with P h h₀ a ha
  have hb : (a:ℝ)≤2*(2*(waringDiminishingCutoff k P 0:ℝ))^k := by
    exact_mod_cast waringDiminishingValues_le hk _ h.1 h.2 ha
  have hw : (waringDiminishingCutoff k P 0:ℝ)≤c*P := by simpa [c] using h₀.2.2
  calc
    _ ≤ 2*((2*c)*P)^k := hb.trans (by rw [mul_assoc]; gcongr)
    _ ≤ _ := by rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right hc1 (pow_nonneg (Nat.cast_nonneg (α:=ℝ) P) k)]

end AnalyticNumberTheory.AdditiveNumberTheory
