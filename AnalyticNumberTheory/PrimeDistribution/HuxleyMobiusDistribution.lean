import AnalyticNumberTheory.SieveMethods.HuxleyLargeValues
import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector

/-!
# The value distribution of a Möbius polynomial

Integrating over translates of the integer grid transfers the discrete
large-values inequality to Lebesgue measure. The estimate is uniform in
the length of the polynomial up to the height.
-/
noncomputable section
open Complex Real Finset MeasureTheory Filter
open scoped Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.PrimeDistribution

/-- Integrate the number of samples in a measurable set over all translations
of the unit-spaced grid. -/
theorem measure_real_le_of_shifted_grid_count (a : ℝ) (n : ℕ) {E : Set ℝ} (hE : MeasurableSet E)
    {B : ℝ} (hB : ∀ u∈Set.Icc (0:ℝ) 1,
      (((range n).filter fun (j : ℕ) => a+j+u ∈ E).card:ℝ) ≤ B) :
    (volume.restrict (Set.Ioc a (a+n))).real E ≤ B := by
  let f := E.indicator (1:ℝ → ℝ)
  have hfm : Measurable f := measurable_const.indicator hE
  have hf0 (x : ℝ) : ‖f x‖ ≤ 1 := by
    by_cases hx : x∈E <;> simp [f,hx]
  have hfi (c b d : ℝ) : IntervalIntegrable (fun u => f (c+u)) volume b d :=
    (intervalIntegrable_const (c:=(1:ℝ))).mono_fun' ((hfm.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall (fun u => hf0 (c+u)))
  have hi (b d : ℝ) : IntervalIntegrable f volume b d := by simpa only [zero_add] using hfi 0 b d
  have hpos : a ≤ a+n := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have heq : (volume.restrict (Set.Ioc a (a+n))).real E = ∫ t in a..a+n, f t := by
    rw [intervalIntegral.integral_of_le hpos,←integral_indicator_one hE]
  rw [heq]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (a:=fun j : ℕ => a+j) (n:=n)
    (f:=f) (fun j _ => hi ..)
  simp only [Nat.cast_zero,add_zero] at hsplit
  rw [←hsplit]
  have ht (j : ℕ) : (∫ t in a+j..a+((j+1:ℕ):ℝ), f t) = ∫ u in (0:ℝ)..1, f (a+j+u) := by
    rw [intervalIntegral.integral_comp_add_left]; push_cast; congr 1 <;> ring
  simp_rw [ht]
  rw [←intervalIntegral.integral_finsetSum (fun (j : ℕ) _ => hfi (a+j) 0 1)]
  calc
    _ ≤ ∫ _ in (0:ℝ)..1, B := by
      apply intervalIntegral.integral_mono_on (by norm_num) (by
        convert IntervalIntegrable.sum (range n) (fun (j : ℕ) _ => hfi (a+j) 0 1) using 1
        funext t; simp only [Finset.sum_apply])
        (intervalIntegrable_const)
      intro u hu
      simpa only [f,Set.indicator_apply,Pi.one_apply,sum_boole] using hB u hu
    _ = B := by simp

private theorem grid_unit_count (S : Finset ℕ) (b u : ℝ) :
    ((S.filter (fun (j : ℕ) => u ≤ b+j ∧ b+j ≤ u+1)).card:ℝ) ≤ 2 := by
  let F := S.filter (fun (j : ℕ) => u≤b+j ∧ b+j≤u+1)
  rcases F.eq_empty_or_nonempty with h | h
  · change (F.card:ℝ) ≤ 2; rw [h]; simp
  · let k := F.min' h
    have hk := F.min'_mem h
    have hk' := (mem_filter.mp hk).2.1
    change u ≤ b+(k:ℝ) at hk'
    have hsub : F ⊆ Icc k (k+1) := by
      intro j hj
      have hj' := (mem_filter.mp hj).2.2
      change b+(j:ℝ) ≤ u+1 at hj'
      exact mem_Icc.mpr ⟨F.min'_le j hj, by exact_mod_cast (by linarith : (j:ℝ)≤k+1)⟩
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    change (F.card:ℝ) ≤ 2
    exact_mod_cast (show F.card≤2 by omega)

/-- Weak second- and sixth-power bounds for a critical-line Möbius polynomial.
Both implicit constants are uniform when the length `X` is at most the height `T`. -/
theorem huxley_mobius_weak_distribution :
    ∃ D > (0:ℝ), ∀ {X T : ℕ}, 1≤X → X≤T → ∀ v : ℝ, 0<v →
      (volume.restrict (Set.Ioc (-(6*(T:ℝ))) (6*T))).real
          {t : ℝ | v<‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖} ≤
        D*X*(1+Real.log T)^3/v^2 + D*T*X*(1+Real.log T)^7/v^6 := by
  let C := 1+8000*π
  let D := 256*13*(C+12*C^3)
  have hC : 0<C := by dsimp [C]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro X T hX hXT v hv
  let L := 1+Real.log T
  have hXr : (1:ℝ)≤X := by exact_mod_cast hX
  have hTr : (1:ℝ)≤T := by exact_mod_cast hX.trans hXT
  have hT0 : 0<(T:ℝ) := by linarith
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg hTr]
  have hLX : 1+Real.log X ≤ L := add_le_add_right (Real.log_le_log (by linarith) (by exact_mod_cast hXT)) _
  let g (t : ℝ) := ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖
  let E := {t : ℝ | v < g t}
  have hg : Continuous g := by
    apply Continuous.norm
    unfold dirichletPoly
    apply continuous_finsetSum
    intro n hn
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    simp_rw [Complex.cpow_def_of_ne_zero hn0]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg))
  have hE : MeasurableSet E := measurableSet_lt measurable_const hg.measurable
  have hG : ∑ n∈Icc 1 X, ‖(μ n:ℂ)‖^2*(n:ℝ)^(-2*(1/2:ℝ)) ≤ L := by
    apply le_trans _ hLX
    apply le_trans (b:=∑ n∈Icc 1 X,(n:ℝ)⁻¹)
    · refine sum_le_sum fun n _ => ?_
      norm_num only [show -2*(1/2:ℝ) = -1 by norm_num,Real.rpow_neg_one]
      exact mul_le_of_le_one_left (by positivity) ((pow_le_pow_left₀ (norm_nonneg _) (norm_moebius_complex_le n) 2).trans_eq (one_pow _))
    · simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log X
  let a := -(6*(T:ℝ))
  have hend : a+(12*T:ℕ) = 6*(T:ℝ) := by dsimp [a]; push_cast; ring
  change (volume.restrict (Set.Ioc a (6*(T:ℝ)))).real E ≤ _
  rw [←hend]
  apply measure_real_le_of_shifted_grid_count a (12*T) hE
  intro u hu
  let S := (range (12*T)).filter fun (j : ℕ) => a+j+u∈E
  let z (j : ℕ) := (1/2:ℂ)+((a+j+u:ℝ):ℂ)*I
  have hre (j : ℕ) (_ : j∈S) : (1/2:ℝ) ≤ (z j).re := by simp [z]
  have him (j : ℕ) : (z j).im = a+j+u := by simp [z]
  have ht (j : ℕ) (hj : j∈S) : a≤(z j).im ∧ (z j).im≤a+12*T := by
    rw [him]
    have hj' : j<12*T := mem_range.mp (mem_filter.mp hj).1
    have hh : (j:ℝ)+1≤12*T := by exact_mod_cast Nat.succ_le_of_lt hj'
    exact ⟨by linarith [hu.1,Nat.cast_nonneg (α:=ℝ) j],by linarith [hu.2]⟩
  have hcell (q : ℝ) : ((S.filter (fun j => q≤(z j).im ∧ (z j).im≤q+1)).card:ℝ) ≤ 2 := by
    simpa only [him,show ∀ j : ℕ, a+j+u=a+u+j from fun j => by ring] using grid_unit_count S (a+u) q
  have h := huxley_dirichletPoly_large_values S (fun n => (μ n:ℂ)) hX z hv.le (by norm_num : 0≤(2:ℝ))
    (by linarith : 1≤12*(T:ℝ)) hre ht hcell hG (fun j hj => (mem_filter.mp hj).2.le)
  let B := L*(C*(1+Real.log X))
  have hB : B ≤ C*L^2 := by
    calc B ≤ L*(C*L) := by dsimp only [B]; gcongr
         _ = _ := by ring
  have hBp : 0≤B := by dsimp [B]; have := Real.log_nonneg hXr; positivity
  have hhlog : 1+Real.log (12*(T:ℝ)+1) ≤ 13*L := by
    have hh := Real.log_le_log (by linarith : 0<12*(T:ℝ)+1) (by linarith : 12*(T:ℝ)+1≤13*T)
    rw [Real.log_mul (by norm_num) hT0.ne'] at hh
    dsimp [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<13),Real.log_nonneg hTr]
  change (S.card:ℝ)*v^6 ≤ 128*2*X*(1+Real.log (12*(T:ℝ)+1))*(B*v^4+(12*T)*B^3) at h
  have hp : (S.card:ℝ)*v^6 ≤ 128*2*X*(13*L)*((C*L^2)*v^4+(12*T)*(C*L^2)^3) := by
    apply h.trans; gcongr
  have hh₁ : 0 ≤ (C^3)*(X*L^3*v^4) := by positivity
  have hh₂ : 0 ≤ C*((T:ℝ)*X*L^7) := by positivity
  change (S.card:ℝ) ≤ D*X*L^3/v^2+D*T*X*L^7/v^6
  have hb : (S.card:ℝ)*v^6 ≤ D*X*L^3*v^4+D*T*X*L^7 := by
    apply hp.trans
    dsimp only [D]
    linarith only [hh₁,hh₂]
  calc
    _ ≤ (D*X*L^3*v^4+D*T*X*L^7)/v^6 := (le_div_iff₀ (pow_pos hv 6)).mpr hb
    _ = _ := by field_simp

end AnalyticNumberTheory.PrimeDistribution
