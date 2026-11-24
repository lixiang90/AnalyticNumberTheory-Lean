import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A critical-line mean-square criterion

The diagonal determines the critical-line second moment whenever bounded
coefficients have a harmonic mean and a polynomial of length comparable to
the height approximates the function with bounded mean square error.
-/

open Complex Real Finset Filter MeasureTheory
open scoped Topology Asymptotics
open AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.DirichletSeries

/-- A finite Dirichlet polynomial restricted to the critical line. -/
noncomputable def criticalLinePolynomial (a : ℕ → ℂ) (M : ℕ) (t : ℝ) : ℂ :=
  dirichletPoly a M ((1/2:ℂ)+t*I)

/-- The critical-line diagonal mass of a coefficient sequence. -/
noncomputable def harmonicMass (a : ℕ → ℂ) (M : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 M, ‖a n‖^2/(n:ℝ)

theorem continuous_criticalLinePolynomial (a : ℕ → ℂ) (M : ℕ) : Continuous (criticalLinePolynomial a M) := by
  change Continuous (fun t : ℝ => ∑ n ∈ Icc 1 M, a n * (n:ℂ)^(-((1/2:ℂ)+t*I)))
  apply continuous_finsetSum
  intro n hn
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hn).1; omega)
  simp only [Complex.cpow_def_of_ne_zero hn']
  fun_prop

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


private theorem poly_diagonal (a : ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) (M : ℕ) :
    |mass T (criticalLinePolynomial a M) - (T-1)*harmonicMass a M| ≤ 2*π*M*harmonicMass a M := by
  have H := dirichletPoly_mean_sq_asymp a M (1/2) hT
  simpa only [mass,criticalLinePolynomial,harmonicMass,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,
    Complex.ofReal_one,Complex.ofReal_ofNat,show -2*(1*(2:ℝ)⁻¹) = -1 by norm_num,
    Real.rpow_neg_one,Real.norm_eq_abs] using H

private theorem tail_energy (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (M N : ℕ) (hM : 0 < M) :
    harmonicMass (fun n => if M < n then a n else 0) N ≤ N/M := by
  unfold harmonicMass
  calc _ ≤ ∑ _n ∈ Icc 1 N, (M:ℝ)⁻¹ := by
            apply sum_le_sum
            intro n hn
            by_cases h : M < n
            · simp only [h,ite_true,div_eq_mul_inv]
              apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha n) 2)
                (by positivity : 0 ≤ (n:ℝ)⁻¹)).trans
              simpa using (inv_anti₀ (by exact_mod_cast hM : (0:ℝ)<M) (by exact_mod_cast h.le : (M:ℝ) ≤ n))
            · simp [h]
       _ = _ := by simp [Nat.card_Icc,div_eq_mul_inv]

private theorem poly_sub (a : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) (t : ℝ) :
    criticalLinePolynomial a N t - criticalLinePolynomial a M t =
      criticalLinePolynomial (fun n => if M < n then a n else 0) N t := by
  classical
  let f := fun n : ℕ => a n*(n:ℂ)^(-((1/2:ℂ)+t*I))
  have he : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n; simp only [mem_filter,mem_Icc]; omega
  have H := sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n ≤ M) f
  rw [he] at H
  simp only [criticalLinePolynomial,dirichletPoly,ite_mul,zero_mul, ← sum_filter]
  simp only [not_le] at H
  change _ - _ = ∑ n ∈ (Icc 1 N).filter (fun n => M < n), f n
  linear_combination -H

private theorem tail_mass (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {T : ℝ} (hT : 1 ≤ T)
    {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    mass T (criticalLinePolynomial a N - criticalLinePolynomial a M) ≤ (T+2*π*N)*(N/M) := by
  let b := fun n => if M < n then a n else 0
  have he : criticalLinePolynomial a N - criticalLinePolynomial a M = criticalLinePolynomial b N :=
    funext (poly_sub a hMN)
  rw [he]
  have H := (abs_le.mp (poly_diagonal b hT N)).2
  have hD : 0 ≤ harmonicMass b N := sum_nonneg fun _ _ => by positivity
  apply le_trans _ (mul_le_mul_of_nonneg_left (tail_energy a ha M N hM) (by positivity : 0 ≤ T+2*π*N))
  change _ ≤ (T+2*π*N)*harmonicMass b N
  linarith only [H,hD]

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

private theorem transfer_normalized_mass {κ : ℝ} (hκ : 0 ≤ κ) {f g : ℝ → ℝ → ℂ}
    (hf : ∀ T, Continuous (f T)) (hg : ∀ T, Continuous (g T))
    (hmain : Tendsto (fun T : ℝ => mass T (g T)/(T*Real.log T)) atTop (𝓝 κ))
    (herr : Tendsto (fun T : ℝ => mass T (f T-g T)/(T*Real.log T)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => mass T (f T)/(T*Real.log T)) atTop (𝓝 κ) := by
  have hs : Tendsto (fun T : ℝ => √(mass T (f T)/(T*Real.log T))) atTop (𝓝 (√κ)) := by
    apply (show Tendsto (fun T : ℝ => √(mass T (g T)/(T*Real.log T))) atTop (𝓝 (√κ)) by
      simpa only [Function.comp_def] using (Real.continuous_sqrt.tendsto κ).comp hmain).congr_dist
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _
      (show Tendsto (fun T : ℝ => √(mass T (f T-g T)/(T*Real.log T))) atTop (𝓝 0) by
        simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp herr)
    filter_upwards [eventually_lengths] with T h
    rw [dist_comm,Real.dist_eq, Real.sqrt_div (mass_nonneg h.1 _) _, Real.sqrt_div (mass_nonneg h.1 _) _,
      Real.sqrt_div (mass_nonneg h.1 _) _, ← sub_div,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (sqrt_mass_sub_le h.1 (hf T) (hg T)) (Real.sqrt_nonneg _)
  apply (show Tendsto (fun T : ℝ => √(mass T (f T)/(T*Real.log T))^2) atTop (𝓝 κ) by simpa only [Real.sq_sqrt hκ] using hs.pow 2).congr'
  filter_upwards [eventually_lengths] with T h
  exact Real.sq_sqrt (div_nonneg (mass_nonneg h.1 _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1])))


/-- Transfer a diagonal mean-square asymptotic from a family of continuous
polynomials to a continuous function. The three estimates express the
short-polynomial mean value, the tail energy, and the approximation at
a cutoff comparable to the height. -/
theorem criticalMeanSquare_of_family {F : ℝ → ℂ} (hF : Continuous F)
    (P : ℕ → ℝ → ℂ) (hc : ∀ n, Continuous (P n)) (d : ℕ → ℝ) {K κ : ℝ}
    (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hdiag : ∃ B : ℝ, ∀ n, |d n-κ*(harmonic n:ℝ)| ≤ B)
    (hpoly : ∀ {T : ℝ}, 1 ≤ T → ∀ n : ℕ,
      |(∫ t in (1:ℝ)..T, ‖P n t‖^2)-(T-1)*d n| ≤ K*n*d n)
    (htailBound : ∀ {T : ℝ}, 1≤T → ∀ {M N : ℕ}, 0<M → M≤N →
      (∫ t in (1:ℝ)..T, ‖(P N-P M) t‖^2) ≤ (T+K*N)*(N/M))
    (M : ℝ → ℕ) (hM : ∃ D > 0, ∀ᶠ T : ℝ in atTop, ⌊T⌋₊+1 ≤ M T ∧ (M T:ℝ) ≤ D*T)
    (happrox : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, ‖F t-P (M T) t‖^2)/T ≤ C) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖F t‖^2)/(T*Real.log T)) atTop (𝓝 κ) := by
  obtain ⟨B,hB⟩ := hdiag
  obtain ⟨D,hD,hcut⟩ := hM
  obtain ⟨C,hC⟩ := happrox
  have hH : Tendsto (fun T : ℝ => d (shortLength T)/Real.log T) atTop (𝓝 κ) := by
    apply (show Tendsto (fun T : ℝ => κ*((harmonic (shortLength T):ℝ)/Real.log T)) atTop (𝓝 κ) by
      simpa using tendsto_short_harmonic.const_mul κ).congr_dist
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop (a := B))
    filter_upwards [eventually_lengths] with T h
    rw [dist_comm,Real.dist_eq,← mul_div_assoc,← sub_div,abs_div,abs_of_pos (by linarith [h.2.1] : 0 < Real.log T)]
    exact div_le_div_of_nonneg_right (hB _) (by linarith [h.2.1])
  have hmain : Tendsto (fun T : ℝ => mass T (P (shortLength T))/(T*Real.log T))
      atTop (𝓝 κ) := by
    have hA : Tendsto (fun T : ℝ => (1-T⁻¹)*(d (shortLength T)/Real.log T)) atTop (𝓝 κ) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_inv_atTop_zero (𝕜 := ℝ))).mul hH
    apply hA.congr_dist
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _
      (show Tendsto (fun T : ℝ => K*((shortLength T:ℝ)/T)*(d (shortLength T)/Real.log T)) atTop (𝓝 0) by
        simpa using (tendsto_shortLength_div.const_mul (K)).mul hH)
    filter_upwards [eventually_lengths] with T h
    have ht : 0 < T := by linarith [h.1]
    have hl : 0 < Real.log T := by linarith [h.2.1]
    have hd := hpoly h.1 (shortLength T)
    rw [dist_comm,Real.dist_eq]
    calc _ = |mass T (P (shortLength T))-(T-1)*d (shortLength T)|/(T*Real.log T) := by
              rw [← abs_of_pos (mul_pos ht hl),← abs_div]
              congr 1
              rw [abs_of_pos (mul_pos ht hl)]
              field_simp
         _ ≤ _ := (div_le_div_of_nonneg_right hd (mul_nonneg ht.le hl.le)).trans_eq (by ring)
  have htail : Tendsto (fun T : ℝ =>
      mass T (P (M T)-P (shortLength T))/(T*Real.log T)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using tendsto_sqrt_log_div_log.const_mul (D*(1+K*D)))
    · filter_upwards [eventually_lengths] with T h
      exact div_nonneg (mass_nonneg h.1 _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1]))
    filter_upwards [eventually_lengths,hcut] with T h hcut
    obtain ⟨hT,hlog,hs,hMN,_,_,_,_⟩ := h
    have ht : 0 < T := by linarith
    have hl : 0 < Real.log T := by linarith
    have hsp : 0 < √(Real.log T) := by positivity
    have hmlo : T/√(Real.log T) ≤ (shortLength T:ℝ) := by
      simpa [shortLength] using (Nat.lt_floor_add_one (T/√(Real.log T))).le
    have hquot : (M T:ℝ)/shortLength T ≤ D*√(Real.log T) := by
      rw [div_le_iff₀ (by dsimp [shortLength]; positivity)]
      exact hcut.2.trans (by nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ hsp).mp hmlo) hD.le])
    have hb := htailBound hT (M := shortLength T) (Nat.succ_pos _) (hMN.trans hcut.1)
    have hfactor : T+K*(M T) ≤ (1+K*D)*T := by nlinarith only [mul_le_mul_of_nonneg_left hcut.2 hK]
    apply (div_le_div_of_nonneg_right hb (mul_nonneg ht.le hl.le)).trans
    apply (div_le_div_of_nonneg_right (mul_le_mul hfactor hquot (by positivity) (by positivity)) (mul_nonneg ht.le hl.le)).trans_eq
    field_simp
  apply transfer_normalized_mass hκ (f := fun _ => F) (g := fun T => P (M T))
      (fun _ => hF) (fun _ => hc _)
      (transfer_normalized_mass hκ (fun _ => hc _) (fun _ => hc _) hmain htail)
  apply squeeze_zero' _ _ (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop (a := C))
  · filter_upwards [eventually_lengths] with T h
    exact div_nonneg (mass_nonneg h.1 _) (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1]))
  filter_upwards [eventually_lengths,hC] with T h hC
  rw [← div_div]
  exact div_le_div_of_nonneg_right hC (by linarith [h.2.1])

/-- A bounded-coefficient Dirichlet polynomial determines the critical
second moment when its diagonal is `κ H_N + O(1)` and a linear-length
approximation has bounded normalized mean square error. -/
theorem criticalMeanSquare_of_approx {F : ℝ → ℂ} (hF : Continuous F) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hdiag : ∃ B : ℝ, ∀ M, |harmonicMass a M-κ*(harmonic M:ℝ)| ≤ B)
    (M : ℝ → ℕ) (hM : ∃ D > 0, ∀ᶠ T : ℝ in atTop, ⌊T⌋₊+1 ≤ M T ∧ (M T:ℝ) ≤ D*T)
    (happrox : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, ‖F t-criticalLinePolynomial a (M T) t‖^2)/T ≤ C) :
    Tendsto (fun T : ℝ => (∫ t in (1:ℝ)..T, ‖F t‖^2)/(T*Real.log T)) atTop (𝓝 κ) := by
  exact criticalMeanSquare_of_family hF (criticalLinePolynomial a) (continuous_criticalLinePolynomial a)
    (harmonicMass a) (K:=2*π) (by positivity) hκ hdiag (fun ht n => poly_diagonal a ht n)
    (fun {T} ht {m n} hpos hle => tail_mass a ha ht hpos hle) M hM happrox

end AnalyticNumberTheory.DirichletSeries
