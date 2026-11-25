import AnalyticNumberTheory.ModularAndPartitions.RademacherSeries
import Mathlib.Analysis.Calculus.DSlope

/-!
# The first relative correction to the partition asymptotic

Writing `c = π √(2/3)`, the shifted square root in the Rademacher term
contributes `-c/48`, and the derivative of its hyperbolic kernel
contributes `-1/c`. The remaining denominators are exponentially smaller.
-/

open Real Filter Asymptotics
open scoped Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private theorem scaled_product {v f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto (fun n => v n*(f n-1)) atTop (𝓝 a))
    (hg : Tendsto (fun n => v n*(g n-1)) atTop (𝓝 b))
    (hg' : Tendsto g atTop (𝓝 1)) :
    Tendsto (fun n => v n*(f n*g n-1)) atTop (𝓝 (a+b)) := by
  have H := (hf.mul hg').add hg
  rw [mul_one] at H
  apply H.congr'
  filter_upwards with n; ring

private theorem first_term_correction :
    let c := π*√(2/3)
    Tendsto (fun n : ℕ => √(n:ℝ)*(rademacherPsi 1 n/hardyRamanujanMainTerm n-1))
      atTop (𝓝 (-c/48-1/c)) := by
  intro c
  have hc : 0<c := by dsimp [c]; positivity
  let u (n : ℕ) := √((n:ℝ)-1/24)
  let v (n : ℕ) := √(n:ℝ)
  have hu : Tendsto u atTop atTop := tendsto_sqrt_atTop.comp (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(1/24:ℝ)) (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hv : Tendsto v atTop atTop := tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n in atTop,0<u n ∧ 0<v n ∧ (u n)^2=(n:ℝ)-1/24 ∧ (v n)^2=(n:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h₁ : (1:ℝ)≤n := by exact_mod_cast hn
    have h₂ : 0<(n:ℝ)-1/24 := by linarith
    exact ⟨Real.sqrt_pos.mpr h₂,Real.sqrt_pos.mpr (by linarith),Real.sq_sqrt h₂.le,Real.sq_sqrt (by positivity)⟩
  have huv : Tendsto (fun n => u n/v n) atTop (𝓝 1) := by
    have H := ((tendsto_const_nhds (x:=(1:ℝ))).sub ((tendsto_const_nhds (x:=(1/24:ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ)))).sqrt
    simp only [sub_zero,Real.sqrt_one] at H
    apply H.congr'
    filter_upwards [hpos] with n hn
    have hn' : (n:ℝ)≠0 := by rw [←hn.2.2.2]; exact pow_ne_zero _ hn.2.1.ne'
    change √(1-(1/24)/(n:ℝ))=√((n:ℝ)-1/24)/√(n:ℝ)
    rw [←Real.sqrt_div (by linarith [sq_nonneg (u n),hn.2.2.1])]
    congr 1; field_simp
  have hvu : Tendsto (fun n => v n/u n) atTop (𝓝 1) := by simpa using huv.inv₀ one_ne_zero
  have hdiff : Tendsto (fun n => v n*(u n-v n)) atTop (𝓝 (-1/48)) := by
    have H := (tendsto_const_nhds (x:=(-1/24:ℝ))).div ((tendsto_const_nhds (x:=(1:ℝ))).add huv) (by norm_num)
    norm_num at H
    rw [neg_div]
    apply H.congr'
    filter_upwards [hpos] with n hn
    have hsum := (add_pos hn.2.1 hn.1).ne'
    have he : (u n-v n)*(v n+u n)= -(1/24) := by nlinarith [hn.2.2.1,hn.2.2.2]
    change -(1/24)/(1+u n/v n)=v n*(u n-v n)
    rw [←he,show 1+u n/v n=(v n+u n)/v n by field_simp [hn.2.1.ne']]
    field_simp [hn.2.1.ne',hsum]
  have hdiff₀ : Tendsto (fun n => u n-v n) atTop (𝓝 0) := by
    apply (hdiff.div_atTop hv).congr'
    filter_upwards [hpos] with n hn
    field_simp [hn.2.1.ne']
  let E n := Real.exp (c*(u n-v n))
  have hE : Tendsto E atTop (𝓝 1) := by simpa [E,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp (hdiff₀.const_mul c)
  have hEsc : Tendsto (fun n => v n*(E n-1)) atTop (𝓝 (-c/48)) := by
    have hD := continuousAt_dslope_same.mpr (Real.differentiableAt_exp (x:=0))
    have harg : Tendsto (fun n => c*(u n-v n)) atTop (𝓝 0) := by simpa using hdiff₀.const_mul c
    have H := (hD.tendsto.comp harg).mul (hdiff.const_mul c)
    simp only [dslope_same,Real.deriv_exp,Real.exp_zero,one_mul] at H
    convert H.congr' ?_ using 2
    · ring
    filter_upwards with n
    have hS := sub_smul_dslope Real.exp 0 (c*(u n-v n))
    simp only [sub_zero,smul_eq_mul,Real.exp_zero] at hS
    dsimp [Function.comp_def,E]
    linear_combination v n*hS
  let A (n : ℕ) := (n:ℝ)/((n:ℝ)-1/24)
  have hAsc : Tendsto (fun n => v n*(A n-1)) atTop (𝓝 0) := by
    have H := (hvu.const_mul (1/24:ℝ)).div_atTop hu
    apply H.congr'
    filter_upwards [hpos] with n hn
    dsimp [A]
    rw [←hn.2.2.1,←hn.2.2.2]
    field_simp [hn.1.ne']
    nlinarith [hn.2.2.1,hn.2.2.2]
  let R n := Real.exp (-2*c*u n)
  have hRu : Tendsto (fun n => u n*R n) atTop (𝓝 0) := by
    have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2*c) (by positivity)).comp hu
    simpa [Function.comp_def,R,neg_mul] using H
  have hRv : Tendsto (fun n => v n*R n) atTop (𝓝 0) := by
    have H := hvu.mul hRu
    rw [mul_zero] at H
    apply H.congr'
    filter_upwards [hpos] with n hn
    field_simp [hn.1.ne']
  have hR : Tendsto R atTop (𝓝 0) := by
    apply (hRu.div_atTop hu).congr'
    filter_upwards [hpos] with n hn
    field_simp [hn.1.ne']
  let D n := 1+R n-(1-R n)/(c*u n)
  have hD : Tendsto D atTop (𝓝 1) := by
    have H := ((tendsto_const_nhds (x:=(1:ℝ))).add hR).sub
      (((tendsto_const_nhds (x:=(1:ℝ))).sub hR).div_atTop (hu.const_mul_atTop hc))
    simpa [D] using H
  have hDsc : Tendsto (fun n => v n*(D n-1)) atTop (𝓝 (-1/c)) := by
    have H := hRv.sub ((hvu.mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hR)).div_const c)
    simp only [sub_zero,one_mul,zero_sub] at H
    rw [neg_div]
    apply H.congr'
    filter_upwards with n
    dsimp [D]; ring
  have H := scaled_product (scaled_product hAsc hEsc hE) hDsc hD
  rw [show (0+ -c/48)+ -1/c= -c/48-1/c by ring] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [rademacherPsi_one_div_mainTerm hn]

private theorem scaled_rademacher_tail :
    Tendsto (fun n : ℕ => √(n:ℝ)*(((partitionCount n:ℝ)-rademacherPsi 1 n)/hardyRamanujanMainTerm n))
      atTop (𝓝 0) := by
  let c : ℝ := π*√(2/3)
  let K := c^3/(6*π*√2)*(∑' k : ℕ+, (k:ℝ)^(-(3/2:ℝ)))
  have hc : 0<c := by dsimp [c]; positivity
  have H := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 (c/2) (by positivity)).comp
    (tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))).const_mul (4*√3*K)
  rw [mul_zero] at H
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ H
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn₁ : (1:ℝ)≤n := by exact_mod_cast hn
  have hM : 0<hardyRamanujanMainTerm n := by dsimp [hardyRamanujanMainTerm]; positivity
  have hv := Real.sq_sqrt (Nat.cast_nonneg n)
  have hb := abs_partitionCount_sub_psi_one_le_of_rademacher (dedekindSum_zero_left 1) rademacherSeriesFormula hn
  change _ ≤ (c^3/(6*π*√2))*Real.exp (c*√(n:ℝ)/2)*(∑' k : ℕ+, (k:ℝ)^(-(3/2:ℝ))) at hb
  have hmain : hardyRamanujanMainTerm n= Real.exp (c*√(n:ℝ))/(4*(n:ℝ)*√3) := by
    rw [hardyRamanujanMainTerm,show 2*(n:ℝ)/3=2/3*(n:ℝ) by ring,Real.sqrt_mul (by norm_num)]
    dsimp [c]; ring
  have hp (x : ℝ) : x^(3:ℝ)=x^3 := Real.rpow_natCast x 3
  simp only [Function.comp_apply,hp,Real.norm_eq_abs,abs_mul,abs_div,
    abs_of_nonneg (Real.sqrt_nonneg (n:ℝ)),abs_of_pos hM]
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hM.le) (Real.sqrt_nonneg _)).trans
  rw [hmain,div_div_eq_mul_div]
  have hex : Real.exp (c*√(n:ℝ)/2)/Real.exp (c*√(n:ℝ))=Real.exp (-(c/2)*√(n:ℝ)) := by
    rw [←Real.exp_sub]; congr 1; ring
  dsimp [K]
  rw [←hex]
  generalize √(n:ℝ)=w at hv ⊢
  rw [←hv]; apply le_of_eq; ring

/-- The coefficient of the first relative correction to the Hardy–Ramanujan
formula is `-c/48-1/c`, where `c = π√(2/3)`. -/
theorem tendsto_partitionCount_first_correction :
    let c := π*√(2/3)
    Tendsto (fun n : ℕ => √(n:ℝ)*((partitionCount n:ℝ)/hardyRamanujanMainTerm n-1))
      atTop (𝓝 (-c/48-1/c)) := by
  intro c
  have H := scaled_rademacher_tail.add first_term_correction
  rw [zero_add] at H
  apply H.congr'
  filter_upwards with n
  ring

/-- The Hardy–Ramanujan main term has relative error `O(1/√n)`. -/
theorem partitionCount_relative_error_isBigO :
    (fun n : ℕ => (partitionCount n:ℝ)/hardyRamanujanMainTerm n-1) =O[atTop]
      (fun n : ℕ => 1/√(n:ℝ)) := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds _ (-(π*√(2/3))/48-1/(π*√(2/3))) _
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have H : √(n:ℝ)≠0 := by positivity
    simp [H]
  · apply tendsto_partitionCount_first_correction.congr'
    filter_upwards with n
    change _=(_)/(1/√(n:ℝ)); rw [one_div,div_inv_eq_mul]; ring

end AnalyticNumberTheory.ModularAndPartitions
