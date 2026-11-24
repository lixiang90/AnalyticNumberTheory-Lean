import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The second moment of the zeta function on the critical line

To isolate the diagonal main term, truncate at `T/√(Real.log T)`. The remaining
part of the long Dirichlet polynomial has harmonic mass `O(√(Real.log T))`,
and the long polynomial approximates zeta in mean square with bounded
normalized error. The triangle inequality in `L²[1,T]` compares their norms.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.RiemannZeta

private noncomputable def criticalPoly (M : ℕ) (t : ℝ) :=
  dirichletPoly (fun _ => 1) M ((1/2:ℂ)+t*I)

private theorem continuous_criticalPoly (M : ℕ) : Continuous (criticalPoly M) := by
  unfold criticalPoly
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using continuous_dirichletPoly_one M (1/2)

private noncomputable def mass (T : ℝ) (f : ℝ → ℂ) : ℝ := ∫ t in (1:ℝ)..T, ‖f t‖^2

private theorem mass_nonneg {T : ℝ} (hT : 1 ≤ T) (f : ℝ → ℂ) : 0 ≤ mass T f :=
  intervalIntegral.integral_nonneg hT (fun _ _ => sq_nonneg _)

private theorem sqrt_mass_sub_le {T : ℝ} (hT : 1 ≤ T) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    |√(mass T f)-√(mass T g)| ≤ √(mass T (f-g)) := by
  let μ := volume.restrict (Set.Ioc 1 T)
  have he {u : ℝ → ℂ} (hu : Continuous u) : lpNorm u 2 μ = √(mass T u) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hu.aestronglyMeasurable,
      mass, intervalIntegral.integral_of_le hT,Real.sqrt_eq_rpow]
    norm_num [μ]
  have hm {u : ℝ → ℂ} (hu : Continuous u) : MemLp u 2 μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr ((hu.norm.pow 2).intervalIntegrable ..).1
  rw [← he hf,← he hg,← he (hf.sub hg),abs_le]
  have h1 := lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) (hm hg) (by norm_num)
  have h2 := lpNorm_le_lpNorm_add_lpNorm_sub (f := g) (hm hf) (by norm_num)
  exact ⟨by linarith,by linarith⟩

private theorem poly_diagonal {T : ℝ} (hT : 1 ≤ T) (M : ℕ) :
    |mass T (criticalPoly M) - (T-1)*(harmonic M:ℝ)| ≤ 2*π*M*(harmonic M:ℝ) := by
  have H := dirichletPoly_mean_sq_asymp (fun _ => (1:ℂ)) M (1/2) hT
  have he : (-2*(1/2:ℝ)) = -1 := by norm_num
  simpa only [mass,criticalPoly,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,he,Real.rpow_neg_one,norm_one,
    one_pow,one_mul,Real.norm_eq_abs] using H

private theorem tail_coeff_energy (M N : ℕ) (hM : 0 < M) :
    ∑ n ∈ Icc 1 N, ‖if M < n then (1:ℂ) else 0‖^2*(n:ℝ)^(-2*(1/2:ℝ)) ≤ N/M := by
  classical
  simp only [show -2*(1/2:ℝ) = -1 by norm_num,Real.rpow_neg_one]
  calc _ ≤ ∑ _n ∈ Icc 1 N, (M:ℝ)⁻¹ := by
            apply sum_le_sum
            intro n hn
            by_cases h : M < n
            · simp only [h,ite_true,norm_one,one_pow,one_mul]
              exact inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast h.le)
            · simp [h]
       _ = _ := by simp [Nat.card_Icc,div_eq_mul_inv]

private theorem criticalPoly_sub {M N : ℕ} (hMN : M ≤ N) (t : ℝ) :
    criticalPoly N t - criticalPoly M t =
      dirichletPoly (fun n => if M < n then (1:ℂ) else 0) N ((1/2:ℂ)+t*I) := by
  classical
  let f := fun n : ℕ => (n:ℂ)^(-((1/2:ℂ)+t*I))
  have he : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n; simp only [mem_filter,mem_Icc]; omega
  have H := sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n ≤ M) f
  rw [he] at H
  simp only [criticalPoly,dirichletPoly,one_mul,ite_mul,zero_mul, ← sum_filter]
  simp only [not_le] at H
  change _ - _ = ∑ n ∈ (Icc 1 N).filter (fun n => M < n), f n
  linear_combination -H

private theorem tail_mass {T : ℝ} (hT : 1 ≤ T) {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    mass T (criticalPoly N - criticalPoly M) ≤ (T+2*π*N)*(N/M) := by
  let a := fun n => if M < n then (1:ℂ) else 0
  let D := ∑ n ∈ Icc 1 N, ‖a n‖^2*(n:ℝ)^(-2*(1/2:ℝ))
  have hd : 0 ≤ D := sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have H := dirichletPoly_mean_sq_asymp a N (1/2) hT
  have he : mass T (criticalPoly N-criticalPoly M) =
      ∫ t in (1:ℝ)..T, ‖dirichletPoly a N (((1/2:ℝ):ℂ)+t*I)‖^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Pi.sub_apply,criticalPoly_sub hMN,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,a]
  rw [← he,Real.norm_eq_abs] at H
  change |mass T _-(T-1)*D| ≤ 2*π*N*D at H
  apply le_trans _ (mul_le_mul_of_nonneg_left (tail_coeff_energy M N hM) (by positivity : 0 ≤ T+2*π*N))
  change _ ≤ (T+2*π*N)*D
  linarith only [(abs_le.mp H).2,hd]

private theorem harmonic_gap_le {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    |(harmonic N:ℝ)-(harmonic M:ℝ)| ≤ N/M := by
  have he : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n; simp only [mem_filter,mem_Icc]; omega
  have H := sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n ≤ M) (fun n => (n:ℝ)⁻¹)
  rw [he] at H
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [← H,add_sub_cancel_left,abs_of_nonneg (sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp only [not_le]
  calc _ ≤ ∑ _n ∈ (Icc 1 N).filter (fun n => M < n), (M:ℝ)⁻¹ := by
            apply sum_le_sum
            intro n hn
            exact inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast (mem_filter.mp hn).2.le)
       _ ≤ (N:ℝ)*(M:ℝ)⁻¹ := by
            rw [sum_const,nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (card_filter_le ..).trans (by simp [Nat.card_Icc] : (Icc 1 N).card ≤ N)
       _ = _ := by rw [div_eq_mul_inv]

private noncomputable def shortLength (T : ℝ) : ℕ := ⌊T/√(Real.log T)⌋₊+1
private noncomputable def longLength (T : ℝ) : ℕ := ⌊T⌋₊+1

private theorem eventually_lengths : ∀ᶠ T : ℝ in atTop,
    1 ≤ T ∧ 1 ≤ Real.log T ∧ 1 ≤ √(Real.log T) ∧ shortLength T ≤ longLength T ∧
    T ≤ longLength T ∧ (longLength T:ℝ) ≤ 2*T ∧
    (longLength T:ℝ)/shortLength T ≤ 2*√(Real.log T) ∧
    (shortLength T:ℝ)/T ≤ (√(Real.log T))⁻¹+T⁻¹ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hlog
  have hs : 1 ≤ √(Real.log T) := by simpa using Real.sqrt_le_sqrt hlog
  have hsp : 0 < √(Real.log T) := by linarith
  have ht : 0 < T := by linarith
  have hMN : shortLength T ≤ longLength T :=
    Nat.succ_le_succ (Nat.floor_mono (div_le_self ht.le hs))
  have hnlo : T ≤ (longLength T:ℝ) := by simpa [longLength] using (Nat.lt_floor_add_one T).le
  have hnhi : (longLength T:ℝ) ≤ 2*T := by
    simp only [longLength,Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le ht.le]
  have hmlo : T/√(Real.log T) ≤ (shortLength T:ℝ) := by
    simpa [shortLength] using (Nat.lt_floor_add_one (T/√(Real.log T))).le
  have hmhi : (shortLength T:ℝ) ≤ T/√(Real.log T)+1 := by
    simp only [shortLength,Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg ht.le hsp.le)]
  refine ⟨hT,hlog,hs,hMN,hnlo,hnhi,?_,?_⟩
  · rw [div_le_iff₀ (by dsimp [shortLength]; positivity)]
    nlinarith only [hnhi,(div_le_iff₀ hsp).mp hmlo]
  · rw [div_le_iff₀ ht]
    apply hmhi.trans_eq
    field_simp

private theorem tendsto_inv_sqrt_log : Tendsto (fun T : ℝ => (√(Real.log T))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

private theorem tendsto_sqrt_log_div_log : Tendsto (fun T : ℝ => √(Real.log T)/Real.log T) atTop (𝓝 0) := by
  apply tendsto_inv_sqrt_log.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T ht
  have hs := Real.sqrt_pos.mpr ht
  apply (eq_div_iff ht.ne').mpr
  field_simp
  nlinarith only [Real.sq_sqrt ht.le]

private theorem tendsto_shortLength_div : Tendsto (fun T : ℝ => (shortLength T:ℝ)/T) atTop (𝓝 0) := by
  apply squeeze_zero' _ (eventually_lengths.mono fun T h => h.2.2.2.2.2.2.2) _
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT; positivity
  · simpa using tendsto_inv_sqrt_log.add (tendsto_inv_atTop_zero (𝕜 := ℝ))

private theorem tendsto_short_harmonic : Tendsto (fun T : ℝ => (harmonic (shortLength T):ℝ)/Real.log T)
    atTop (𝓝 1) := by
  have hbound : ∀ᶠ T : ℝ in atTop,
      |(harmonic (shortLength T):ℝ)/Real.log T-1| ≤ (1+Real.log 2)/Real.log T+2*(√(Real.log T)/Real.log T) := by
    filter_upwards [eventually_lengths] with T h
    obtain ⟨hT,hlog,hs,hMN,hlo,hhi,hquot,_⟩ := h
    have ht : 0 < T := by linarith
    have hl : 0 < Real.log T := by linarith
    have hN : 0 < (longLength T:ℝ) := ht.trans_le hlo
    have h1 : Real.log T ≤ (harmonic (longLength T):ℝ) := by
      apply (Real.log_le_log ht (hlo.trans (show (longLength T:ℝ) ≤ ((longLength T+1:ℕ):ℝ) by norm_num))).trans
      exact log_add_one_le_harmonic _
    have h2 := (harmonic_le_one_add_log (longLength T)).trans (add_le_add le_rfl (Real.log_le_log hN hhi))
    rw [Real.log_mul (by norm_num) ht.ne'] at h2
    have hd := (harmonic_gap_le (M := shortLength T) (Nat.succ_pos _) hMN).trans hquot
    rw [abs_le] at hd ⊢
    constructor <;> field_simp <;> nlinarith only [h1,h2,hd.1,hd.2,Real.sqrt_nonneg (Real.log T),Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have H : Tendsto (fun T : ℝ => (1+Real.log 2)/Real.log T+2*(√(Real.log T)/Real.log T)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add (tendsto_sqrt_log_div_log.const_mul 2)
  filter_upwards [hbound,H.eventually_lt_const hε] with T ht h
  exact (show |(harmonic (shortLength T):ℝ)/Real.log T-1| < ε from ht.trans_lt h)

private theorem tendsto_mass_shortPoly :
    Tendsto (fun T : ℝ => mass T (criticalPoly (shortLength T))/(T*Real.log T)) atTop (𝓝 1) := by
  let A (T : ℝ) := (1-T⁻¹)*((harmonic (shortLength T):ℝ)/Real.log T)
  have hA : Tendsto A atTop (𝓝 1) := by
    simpa [A] using (tendsto_const_nhds.sub (tendsto_inv_atTop_zero (𝕜 := ℝ))).mul tendsto_short_harmonic
  have hE : Tendsto (fun T : ℝ => 2*π*((shortLength T:ℝ)/T)*((harmonic (shortLength T):ℝ)/Real.log T))
      atTop (𝓝 0) := by
    simpa using (tendsto_shortLength_div.const_mul (2*π)).mul tendsto_short_harmonic
  apply hA.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hE
  filter_upwards [eventually_lengths] with T h
  have ht : 0 < T := by linarith [h.1]
  have hl : 0 < Real.log T := by linarith [h.2.1]
  have hd := poly_diagonal h.1 (shortLength T)
  rw [dist_comm,Real.dist_eq]
  change |mass T _/(T*Real.log T)-(1-T⁻¹)*(_/Real.log T)| ≤ _
  calc _ = |mass T (criticalPoly (shortLength T))-(T-1)*(harmonic (shortLength T):ℝ)|/(T*Real.log T) := by
            rw [← abs_of_pos (mul_pos ht hl),← abs_div]
            congr 1
            rw [abs_of_pos (mul_pos ht hl)]
            field_simp <;> ring
       _ ≤ _ := (div_le_div_of_nonneg_right hd (mul_nonneg ht.le hl.le)).trans_eq (by ring)

private theorem tendsto_normalized_tail :
    Tendsto (fun T : ℝ => mass T (criticalPoly (longLength T)-criticalPoly (shortLength T))/(T*Real.log T))
      atTop (𝓝 0) := by
  have hzero := tendsto_sqrt_log_div_log.const_mul (2*(1+4*π))
  apply squeeze_zero' _ _ (by simpa using hzero)
  · filter_upwards [eventually_lengths] with T h
    exact div_nonneg (mass_nonneg h.1 _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1]))
  filter_upwards [eventually_lengths] with T h
  obtain ⟨hT,hlog,hs,hMN,hlo,hhi,hquot,_⟩ := h
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := by linarith
  have hb := tail_mass hT (M := shortLength T) (Nat.succ_pos _) hMN
  apply (div_le_div_of_nonneg_right hb (mul_nonneg ht.le hl.le)).trans
  have hfactor : T+2*π*(longLength T) ≤ (1+4*π)*T := by nlinarith only [mul_le_mul_of_nonneg_left hhi Real.pi_pos.le]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul hfactor hquot (by positivity) (by positivity)) (mul_nonneg ht.le hl.le)).trans_eq
  field_simp

private noncomputable def criticalZeta (t : ℝ) := riemannZeta ((1/2:ℂ)+t*I)

private theorem tendsto_normalized_long_error :
    Tendsto (fun T : ℝ => mass T (criticalZeta-criticalPoly (longLength T))/(T*Real.log T))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,H⟩ := mean_sq_zeta_sub_long_dirichletPoly_half
  apply squeeze_zero' _ _ (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop (a := C))
  · filter_upwards [eventually_lengths] with T h
    exact div_nonneg (mass_nonneg h.1 _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1]))
  filter_upwards [eventually_lengths] with T h
  rw [← div_div]
  exact div_le_div_of_nonneg_right (H h.1) (by linarith [h.2.1])

private theorem transfer_normalized_mass {f g : ℝ → ℝ → ℂ}
    (hf : ∀ T, Continuous (f T)) (hg : ∀ T, Continuous (g T))
    (hmain : Tendsto (fun T : ℝ => mass T (g T)/(T*Real.log T)) atTop (𝓝 1))
    (herr : Tendsto (fun T : ℝ => mass T (f T-g T)/(T*Real.log T)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => mass T (f T)/(T*Real.log T)) atTop (𝓝 1) := by
  have hs : Tendsto (fun T : ℝ => √(mass T (f T)/(T*Real.log T))) atTop (𝓝 1) := by
    apply (show Tendsto (fun T : ℝ => √(mass T (g T)/(T*Real.log T))) atTop (𝓝 1) by
      simpa only [Function.comp_def,Real.sqrt_one] using (Real.continuous_sqrt.tendsto 1).comp hmain).congr_dist
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _
      (show Tendsto (fun T : ℝ => √(mass T (f T-g T)/(T*Real.log T))) atTop (𝓝 0) by
        simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp herr)
    filter_upwards [eventually_lengths] with T h
    rw [dist_comm,Real.dist_eq, Real.sqrt_div (mass_nonneg h.1 _) _, Real.sqrt_div (mass_nonneg h.1 _) _,
      Real.sqrt_div (mass_nonneg h.1 _) _, ← sub_div,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (sqrt_mass_sub_le h.1 (hf T) (hg T)) (Real.sqrt_nonneg _)
  apply (show Tendsto (fun T : ℝ => √(mass T (f T)/(T*Real.log T))^2) atTop (𝓝 1) by simpa using hs.pow 2).congr'
  filter_upwards [eventually_lengths] with T h
  exact Real.sq_sqrt (div_nonneg (mass_nonneg h.1 _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1])))

/-- The second moment on the critical line has leading term `T log T`.
The coefficient of the logarithm is exactly one. -/
theorem mean_sq_riemannZeta_half_asymptotic :
    (fun T : ℝ => ∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^2) ~[atTop]
      (fun T : ℝ => T*Real.log T) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · apply transfer_normalized_mass (f := fun _ => criticalZeta) (g := fun T => criticalPoly (longLength T))
      (fun _ => continuous_riemannZeta_half) (fun _ => continuous_criticalPoly _) _ tendsto_normalized_long_error
    exact transfer_normalized_mass (fun _ => continuous_criticalPoly _) (fun _ => continuous_criticalPoly _)
      tendsto_mass_shortPoly tendsto_normalized_tail
  · filter_upwards [eventually_lengths] with T h
    exact mul_ne_zero (by linarith [h.1]) (by linarith [h.2.1])

end AnalyticNumberTheory.RiemannZeta
