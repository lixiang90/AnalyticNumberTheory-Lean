import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Positivity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Uniqueness, Non-Vanishing, and Landau's Theorem for Dirichlet Series

This file provides:

- Uniqueness theorems for Dirichlet series agreeing on a complex sequence with `Re (s k) → ∞`,
  a real sequence `σ k → ∞`, an open subset, or a set with an accumulation point in a half-plane
  of absolute convergence.
- Non-vanishing of `LSeries a s` on a right half-plane `σ₀ ≤ Re s` whenever `a 1 ≠ 0` and the
  series converges somewhere.
- **Landau's theorem** for Dirichlet series with nonnegative coefficients: if `LSeries a`
  converges for `Re s > σ₀` and extends analytically to a neighborhood of `σ₀`, then it converges
  past `σ₀` (equivalently, a Dirichlet series with nonnegative coefficients and finite abscissa
  has a singularity at its abscissa).
-/

open Complex Filter Topology
open scoped LSeries.notation ComplexOrder

namespace AnalyticNumberTheory.DirichletSeries

/-! ### Asymptotics as `Re s → ∞` and Uniqueness -/

private theorem tendsto_rpow_sub_atTop {b y : ℝ} (hb : 1 < b) {ι : Type*} {F : Filter ι}
    {u : ι → ℝ} (hu : Tendsto u F atTop) :
    Tendsto (fun k ↦ b ^ (y - u k)) F (𝓝 0) := by
  have hb_pos : 0 < b := zero_lt_one.trans hb
  have hlog : 0 < Real.log b := Real.log_pos hb
  have hmul : Tendsto (fun k ↦ Real.log b * (y - u k)) F atBot := by
    have hsub : Tendsto (fun k ↦ y - u k) F atBot := by
      simpa only [sub_eq_add_neg] using tendsto_const_nhds.add_atBot (tendsto_neg_atBot_iff.mpr hu)
    simpa [mul_comm] using hsub.atBot_mul_const hlog
  refine (Real.tendsto_exp_atBot.comp hmul).congr fun k ↦ ?_
  rw [Function.comp_apply, Real.rpow_def_of_pos hb_pos]

private theorem convex_re_gt_EReal (r : EReal) : Convex ℝ {s : ℂ | r < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [hre]
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add] at hab
    subst hab
    simpa using hy
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rcases eq_or_ne b 0 with rfl | hb0
    · simp only [add_zero] at hab
      subst hab
      simpa using hx
    · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real (lt_min hx hy)
      have hxr : c < x.re := EReal.coe_lt_coe_iff.mp (hc2.trans_le (min_le_left _ _))
      have hyr : c < y.re := EReal.coe_lt_coe_iff.mp (hc2.trans_le (min_le_right _ _))
      have hcomb : c < a * x.re + b * y.re := by
        calc
          c = a * c + b * c := by rw [← add_mul, hab, one_mul]
          _ < a * x.re + b * y.re := add_lt_add (mul_lt_mul_of_pos_left hxr ha_pos)
            (mul_lt_mul_of_pos_left hyr hb_pos)
      exact hc1.trans (EReal.coe_lt_coe_iff.mpr hcomb)

/-- If `f m = 0` for all `m ≤ n` and `abscissaOfAbsConv f < ⊤`, then for any `y : ℝ` with
`abscissaOfAbsConv f < y` and any `z : ℂ` with `y ≤ z.re`,
`‖(n + 1 : ℂ) ^ z * LSeries f z - f (n + 1)‖ ≤ ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * C`. -/
theorem norm_cpow_mul_LSeries_sub_le {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
    {y : ℝ} (hy : LSeries.abscissaOfAbsConv f < y) :
    ∃ C ≥ 0, ∀ z : ℂ, y ≤ z.re →
      ‖(n + 1 : ℂ) ^ z * LSeries f z - f (n + 1)‖ ≤
        ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * C := by
  let F : ℂ → ℕ → ℂ := fun z m ↦
    if n + 1 < m then ((n + 1 : ℂ) ^ z) * LSeries.term f z m else 0
  have hFy_sum : Summable (fun m ↦ ‖F y m‖) := by
    have hsy : LSeriesSummable f y :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hy)
    have hmul : Summable (fun m ↦ ‖(n + 1 : ℂ) ^ (y : ℂ) * LSeries.term f y m‖) := by
      simp_rw [norm_mul]
      exact (summable_norm_iff.mpr hsy).mul_left _
    refine hmul.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
    dsimp only [F]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      positivity
  refine ⟨∑' m : ℕ, ‖F y m‖, tsum_nonneg fun _ ↦ norm_nonneg _, fun z hz ↦ ?_⟩
  have hsz : LSeriesSummable f z :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (hy.trans_le (mod_cast hz))
  have hmuls : Summable (fun m ↦ (n + 1 : ℂ) ^ z * LSeries.term f z m) :=
    hsz.mul_left ((n + 1 : ℂ) ^ z)
  have hFz_sum : Summable (F z) := by
    refine hmuls.norm.of_norm_bounded_eventually (Filter.Eventually.of_forall fun m ↦ ?_)
    dsimp only [F]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      positivity
  have hsplit : (n + 1 : ℂ) ^ z * LSeries f z = f (n + 1) + ∑' m : ℕ, F z m := by
    rw [LSeries, ← tsum_mul_left, hmuls.tsum_eq_add_tsum_ite (n + 1), LSeries.pow_mul_term_eq]
    congr 1
    refine tsum_congr fun m ↦ ?_
    rcases lt_trichotomy m (n + 1) with hm | rfl | hm
    · have hmle : m ≤ n := by omega
      have hterm0 : LSeries.term f z m = 0 := by
        rcases eq_or_ne m 0 with rfl | hm0
        · simp
        · simp [LSeries.term_of_ne_zero hm0, h m hmle]
      simp [F, show ¬ n + 1 < m by omega, show m ≠ n + 1 by omega, hterm0]
    · simp [F]
    · simp [F, hm, show m ≠ n + 1 by omega]
  rw [hsplit, add_sub_cancel_left]
  have hle (m : ℕ) : ‖F z m‖ ≤ ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * ‖F y m‖ := by
    dsimp only [F]
    split_ifs with hm
    · have hm0 : m ≠ 0 := by omega
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
      have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have hc1 : ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) := by push_cast; rfl
      have hnorm_z : ‖((n : ℂ) + 1) ^ z * LSeries.term f z m‖ =
          ((n + 1 : ℝ) ^ z.re) * (‖f m‖ / (m : ℝ) ^ z.re) := by
        rw [norm_mul, hc1, Complex.norm_cpow_eq_rpow_re_of_pos hn1_pos, LSeries.norm_term_eq,
          ite_eq_right hm0]
      have hnorm_y : ‖((n : ℂ) + 1) ^ (y : ℂ) * LSeries.term f y m‖ =
          ((n + 1 : ℝ) ^ y) * (‖f m‖ / (m : ℝ) ^ y) := by
        rw [norm_mul, hc1, Complex.norm_cpow_eq_rpow_re_of_pos hn1_pos, Complex.ofReal_re,
          LSeries.norm_term_eq, ite_eq_right hm0, Complex.ofReal_re]
      rw [hnorm_z, hnorm_y]
      have hm_ge : (n + 2 : ℝ) / (n + 1 : ℝ) ≤ (m : ℝ) / (n + 1 : ℝ) := by
        gcongr
        exact mod_cast hm
      have hratio_pow : ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (z.re - y) ≤
          ((m : ℝ) / (n + 1 : ℝ)) ^ (z.re - y) :=
        Real.rpow_le_rpow (by positivity) hm_ge (sub_nonneg.mpr hz)
      have hinv_pow : ((m : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) ≤
          ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) := by
        have h1 : y - z.re = -(z.re - y) := by ring
        rw [h1, Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hratio_pow
      calc
        (n + 1 : ℝ) ^ z.re * (‖f m‖ / (m : ℝ) ^ z.re)
            = ‖f m‖ * ((m : ℝ) / (n + 1 : ℝ)) ^ (-z.re) := by
          rw [Real.div_rpow hm_pos.le hn1_pos.le, Real.rpow_neg hm_pos.le,
            Real.rpow_neg hn1_pos.le]
          field_simp
        _ = ‖f m‖ * (((m : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * ((m : ℝ) / (n + 1 : ℝ)) ^ (-y)) := by
          rw [← Real.rpow_add (by positivity), show y - z.re + -y = -z.re by ring]
        _ ≤ ‖f m‖ * (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * ((m : ℝ) / (n + 1 : ℝ)) ^ (-y)) := by
          gcongr
        _ = ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * ((n + 1 : ℝ) ^ y * (‖f m‖ / (m : ℝ) ^ y)) := by
          rw [Real.div_rpow hm_pos.le hn1_pos.le, Real.rpow_neg hm_pos.le,
            Real.rpow_neg hn1_pos.le]
          field_simp
    · simp
  calc
    ‖∑' m : ℕ, F z m‖ ≤ ∑' m : ℕ, ‖F z m‖ := norm_tsum_le_tsum_norm hFz_sum.norm
    _ ≤ ∑' m : ℕ, ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * ‖F y m‖ :=
      Summable.tsum_le_tsum hle hFz_sum.norm (hFy_sum.mul_left _)
    _ = ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - z.re) * ∑' m : ℕ, ‖F y m‖ := tsum_mul_left

/-- If `f m = 0` for `m ≤ n` and `abscissaOfAbsConv f < ⊤`, then along any sequence `s : ℕ → ℂ`
with `Re (s k) → ∞`, `(n + 1) ^ (s k) * LSeries f (s k) → f (n + 1)`. -/
theorem tendsto_cpow_mul_LSeries_of_re_tendsto {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
    (ha : LSeries.abscissaOfAbsConv f < ⊤) {s : ℕ → ℂ}
    (hs : Tendsto (fun k ↦ (s k).re) atTop atTop) :
    Tendsto (fun k ↦ (n + 1 : ℂ) ^ (s k) * LSeries f (s k)) atTop (𝓝 (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  obtain ⟨C, _, hC⟩ := norm_cpow_mul_LSeries_sub_le h hay
  have hbase : (1 : ℝ) < (n + 2 : ℝ) / (n + 1 : ℝ) := by
    rw [one_lt_div (by positivity)]
    linarith
  have hlim : Tendsto (fun k ↦ ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - (s k).re) * C) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k ↦ ((n + 2 : ℝ) / (n + 1 : ℝ)) ^ (y - (s k).re)) atTop (𝓝 0) :=
      tendsto_rpow_sub_atTop hbase hs
    simpa using h0.mul_const C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hs.eventually_ge_atTop y] with k hk
  exact hC (s k) hk

/-- Uniqueness along a complex sequence with `Re (s k) → ∞`: if `LSeries f` and `LSeries g`
both converge somewhere and agree at `s k` for all `k` (or eventually), then `f n = g n` for
all `n ≥ 1`. -/
theorem eq_of_LSeries_eq_on_seq {f g : ℕ → ℂ}
    (hf : LSeries.abscissaOfAbsConv f < ⊤) (hg : LSeries.abscissaOfAbsConv g < ⊤)
    {s : ℕ → ℂ} (hs : Tendsto (fun k ↦ (s k).re) atTop atTop)
    (heq : ∀ᶠ k in atTop, LSeries f (s k) = LSeries g (s k)) :
    ∀ n ≠ 0, f n = g n := by
  let h : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n - g n
  have habs_h : LSeries.abscissaOfAbsConv h < ⊤ := by
    have hcongr : LSeries.abscissaOfAbsConv h = LSeries.abscissaOfAbsConv (f - g) :=
      LSeries.abscissaOfAbsConv_congr (fun {n} hn ↦ by simp [h, hn])
    rw [hcongr]
    exact (LSeries.abscissaOfAbsConv_sub_le f g).trans_lt (max_lt hf hg)
  have hLh : ∀ᶠ k in atTop, LSeries h (s k) = 0 := by
    obtain ⟨yf, hyf1, hyf2⟩ := exists_between hf
    obtain ⟨yg, hyg1, hyg2⟩ := exists_between hg
    lift yf to ℝ using ⟨hyf2.ne, ((OrderBot.bot_le _).trans_lt hyf1).ne'⟩
    lift yg to ℝ using ⟨hyg2.ne, ((OrderBot.bot_le _).trans_lt hyg1).ne'⟩
    let y : ℝ := max yf yg
    have hyf : LSeries.abscissaOfAbsConv f < y := hyf1.trans_le (mod_cast le_max_left yf yg)
    have hyg : LSeries.abscissaOfAbsConv g < y := hyg1.trans_le (mod_cast le_max_right yf yg)
    filter_upwards [heq, hs.eventually_gt_atTop y] with k hkeq hky
    have hsf : LSeriesSummable f (s k) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (hyf.trans (EReal.coe_lt_coe_iff.mpr hky))
    have hsg : LSeriesSummable g (s k) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (hyg.trans (EReal.coe_lt_coe_iff.mpr hky))
    rw [LSeries_congr (f := h) (g := f - g) (fun {n} hn ↦ by simp [h, hn]) (s k),
      LSeries_sub hsf hsg, hkeq, sub_self]
  have hh0 : ∀ n, h n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with | ind n ih =>
    cases n with
    | zero => simp [h]
    | succ m =>
      have ht := tendsto_cpow_mul_LSeries_of_re_tendsto (n := m)
        (fun k hk ↦ ih k (Nat.lt_succ_of_le hk)) habs_h hs
      have ht0 : Tendsto (fun k ↦ (m + 1 : ℂ) ^ (s k) * LSeries h (s k)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hLh] with k hk
        simp [hk]
      exact tendsto_nhds_unique ht ht0
  intro n hn
  have := hh0 n
  simpa [h, hn, sub_eq_zero] using this

/-- Uniqueness along a real sequence `σ k → ∞`: if `LSeries f` and `LSeries g` both converge
somewhere and agree at `(σ k : ℂ)` for all large `k`, then `f n = g n` for all `n ≥ 1`. -/
theorem eq_of_LSeries_eq_on_real_seq {f g : ℕ → ℂ}
    (hf : LSeries.abscissaOfAbsConv f < ⊤) (hg : LSeries.abscissaOfAbsConv g < ⊤)
    {σ : ℕ → ℝ} (hσ : Tendsto σ atTop atTop)
    (heq : ∀ᶠ k in atTop, LSeries f (σ k) = LSeries g (σ k)) :
    ∀ n ≠ 0, f n = g n :=
  eq_of_LSeries_eq_on_seq hf hg (s := fun k ↦ (σ k : ℂ)) (by simpa using hσ) heq

/-- Uniqueness on a set with an accumulation point in a convergence half-plane: if `LSeries f`
and `LSeries g` agree on a punctured neighborhood sequence accumulating at `z₀` in their common
half-plane of absolute convergence, then `f n = g n` for all `n ≥ 1`. -/
theorem eq_of_LSeries_frequently_eq {f g : ℕ → ℂ}
    {z₀ : ℂ} (hf : LSeries.abscissaOfAbsConv f < z₀.re)
    (hg : LSeries.abscissaOfAbsConv g < z₀.re)
    (hfg : ∃ᶠ z in 𝓝[≠] z₀, LSeries f z = LSeries g z) :
    ∀ n ≠ 0, f n = g n := by
  let U : Set ℂ := {s : ℂ | max (LSeries.abscissaOfAbsConv f) (LSeries.abscissaOfAbsConv g) < s.re}
  have hU_pre : IsPreconnected U :=
    (convex_re_gt_EReal (max (LSeries.abscissaOfAbsConv f) (LSeries.abscissaOfAbsConv g))).isPreconnected
  have hz₀ : z₀ ∈ U := max_lt hf hg
  have hf_an : AnalyticOnNhd ℂ (LSeries f) U :=
    (LSeries_analyticOnNhd f).mono fun s hs ↦ Set.mem_ofPred.mpr ((le_max_left _ _).trans_lt hs)
  have hg_an : AnalyticOnNhd ℂ (LSeries g) U :=
    (LSeries_analyticOnNhd g).mono fun s hs ↦ Set.mem_ofPred.mpr ((le_max_right _ _).trans_lt hs)
  have hEqOn : U.EqOn (LSeries f) (LSeries g) :=
    hf_an.eqOn_of_preconnected_of_frequently_eq hg_an hU_pre hz₀ hfg
  have hf_top : LSeries.abscissaOfAbsConv f < ⊤ := hf.trans (EReal.coe_lt_top _)
  have hg_top : LSeries.abscissaOfAbsConv g < ⊤ := hg.trans (EReal.coe_lt_top _)
  have hlarge : ∀ᶠ x : ℝ in atTop, LSeries f x = LSeries g x := by
    obtain ⟨y, hy1, _⟩ := EReal.exists_between_coe_real (max_lt hf_top hg_top)
    filter_upwards [eventually_gt_atTop y] with x hx
    apply hEqOn
    change max (LSeries.abscissaOfAbsConv f) (LSeries.abscissaOfAbsConv g) < ((x : ℂ).re : EReal)
    simpa using hy1.trans (EReal.coe_lt_coe_iff.mpr hx)
  exact fun n hn ↦ LSeries.eq_of_LSeries_eventually_eq hf_top hg_top hlarge hn

/-- Uniqueness on a nonempty open subset `V` of the common half-plane of absolute convergence. -/
theorem eq_of_LSeries_eqOn_open {f g : ℕ → ℂ} {V : Set ℂ}
    (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hVf : ∀ s ∈ V, LSeries.abscissaOfAbsConv f < s.re)
    (hVg : ∀ s ∈ V, LSeries.abscissaOfAbsConv g < s.re)
    (hfg : V.EqOn (LSeries f) (LSeries g)) :
    ∀ n ≠ 0, f n = g n := by
  obtain ⟨z₀, hz₀⟩ := hV_ne
  refine eq_of_LSeries_frequently_eq (hVf z₀ hz₀) (hVg z₀ hz₀) ?_
  have hmem : V ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (hV_open.mem_nhds hz₀)
  exact (Filter.eventually_of_mem hmem hfg).frequently

/-- Ergonomic bridge to Mathlib's `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`. -/
theorem LSeries_eq_iff {f g : ℕ → ℂ}
    (hf : LSeries.abscissaOfAbsConv f < ⊤) (hg : LSeries.abscissaOfAbsConv g < ⊤) :
    LSeries f = LSeries g ↔ ∀ n ≠ 0, f n = g n :=
  LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf hg

/-! ### Non-Vanishing on a Right Half-Plane -/

/-- If `abscissaOfAbsConv a < ⊤`, then `LSeries a s` is arbitrarily close to `a 1` uniformly
on a sufficiently far right half-plane `σ₀ ≤ Re s`. -/
theorem exists_re_ge_norm_LSeries_sub_lt {a : ℕ → ℂ}
    (ha : LSeries.abscissaOfAbsConv a < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, (LSeries.abscissaOfAbsConv a < σ₀) ∧
      ∀ s : ℂ, σ₀ ≤ s.re → ‖LSeries a s - a 1‖ < ε := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  let b : ℕ → ℂ := fun n ↦ if n = 0 then 0 else if n = 1 then 0 else a n
  have hba : LSeries.abscissaOfAbsConv b < y := by
    have hcongr : LSeries.abscissaOfAbsConv b = LSeries.abscissaOfAbsConv a := by
      refine LSeries.abscissaOfAbsConv_congr' ?_
      filter_upwards [eventually_gt_atTop 1] with n hn
      simp [b, show n ≠ 0 by omega, show n ≠ 1 by omega]
    simpa [hcongr] using hay
  obtain ⟨C, _, hC⟩ := norm_cpow_mul_LSeries_sub_le (n := 0) (f := b) (fun m hm ↦ by
    rw [Nat.le_zero.mp hm]; simp [b]) hba
  have hlim : Tendsto (fun σ : ℝ ↦ (2 : ℝ) ^ (y - σ) * C) atTop (𝓝 0) := by
    have h0 : Tendsto (fun σ : ℝ ↦ (2 : ℝ) ^ (y - σ)) atTop (𝓝 0) :=
      tendsto_rpow_sub_atTop one_lt_two tendsto_id
    simpa using h0.mul_const C
  obtain ⟨σ₁, hσ₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  let σ₀ := max (y + 1) σ₁
  have hyσ₀ : y < σ₀ := by linarith [le_max_left (y + 1) σ₁]
  refine ⟨σ₀, hay.trans (mod_cast hyσ₀), fun s hs ↦ ?_⟩
  have hys : y ≤ s.re := hyσ₀.le.trans hs
  have has : LSeriesSummable a s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (hay.trans_le (mod_cast hys))
  have hsplit : LSeries a s = a 1 + LSeries b s := by
    rw [LSeries, LSeries, has.tsum_eq_add_tsum_ite 1, LSeries.term_of_ne_zero one_ne_zero,
      Nat.cast_one, one_cpow, div_one]
    congr 1
    refine tsum_congr fun m ↦ ?_
    rcases eq_or_ne m 0 with rfl | hm0
    · simp [b]
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [b]
    · simp [b, hm0, hm1]
  rw [hsplit, add_sub_cancel_left]
  have hb0 := hC s hys
  have hb1 : b (0 + 1) = 0 := by simp [b]
  rw [Nat.cast_zero, zero_add, one_cpow, one_mul, hb1, sub_zero] at hb0
  norm_num at hb0
  have hpow_le : (2 : ℝ) ^ (y - s.re) * C ≤ (2 : ℝ) ^ (y - σ₀) * C := by
    gcongr
    exact one_le_two
  exact hb0.trans_lt (lt_of_le_of_lt hpow_le (hσ₁ σ₀ (le_max_right _ _)))

/-- If `abscissaOfAbsConv a < ⊤` and `a 1 ≠ 0`, then `LSeries a s ≠ 0` on a right half-plane
`σ₀ ≤ Re s`. -/
theorem exists_re_ge_LSeries_ne_zero {a : ℕ → ℂ}
    (ha : LSeries.abscissaOfAbsConv a < ⊤) (ha1 : a 1 ≠ 0) :
    ∃ σ₀ : ℝ, (LSeries.abscissaOfAbsConv a < σ₀) ∧
      ∀ s : ℂ, σ₀ ≤ s.re → LSeries a s ≠ 0 := by
  have hpos : 0 < ‖a 1‖ / 2 := half_pos (norm_pos_iff.mpr ha1)
  obtain ⟨σ₀, hσ₀, hbound⟩ := exists_re_ge_norm_LSeries_sub_lt ha hpos
  refine ⟨σ₀, hσ₀, fun s hs h0 ↦ ?_⟩
  have h := hbound s hs
  rw [h0, zero_sub, norm_neg] at h
  linarith

/-! ### Landau's Theorem for Dirichlet Series with Nonnegative Coefficients -/

private theorem term_logPowMul_real (a : ℕ → ℝ) (k : ℕ) (c : ℝ) (n : ℕ) :
    LSeries.term (LSeries.logMul^[k] (fun m ↦ (a m : ℂ))) c n =
      ((if n = 0 then 0 else a n * (Real.log n) ^ k / (n : ℝ) ^ c : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hiter (j : ℕ) :
      (LSeries.logMul^[j] (fun m ↦ (a m : ℂ))) n = ((a n * (Real.log n) ^ j : ℝ) : ℂ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, ← Complex.natCast_log]
      push_cast
      ring
  rw [LSeries.term_of_ne_zero hn, ite_eq_right hn, hiter k]
  push_cast
  rw [Complex.ofReal_cpow n.cast_nonneg]
  rfl

private theorem landau_taylor_real {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {c x : ℝ} (hxc : x < c)
    (hc_abs : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) < c)
    {F : ℂ → ℂ} (hF_nhd : F =ᶠ[𝓝 (c : ℂ)] LSeries (fun n ↦ (a n : ℂ)))
    (htaylor : HasSum (fun k : ℕ ↦ (k.factorial : ℂ)⁻¹ • ((x : ℂ) - c) ^ k • iteratedDeriv k F c)
      (F x)) :
    let u := c - x
    let b : ℕ → ℕ → ℝ := fun k n ↦
      if n = 0 then 0 else (u ^ k / (k.factorial : ℝ)) * (a n * (Real.log n) ^ k / (n : ℝ) ^ c)
    (∀ k n, 0 ≤ b k n) ∧ (∀ k, Summable (b k)) ∧
      HasSum (fun k : ℕ ↦ ∑' n : ℕ, b k n) (F x).re := by
  intro u b
  have hu_pos : 0 < u := sub_pos.mpr hxc
  have hc_re : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) < (c : ℂ).re := by
    simpa using hc_abs
  have hb_nonneg (k n : ℕ) : 0 ≤ b k n := by
    dsimp [b]
    split_ifs with hn
    · exact le_rfl
    · have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have hpow : 0 ≤ (n : ℝ) ^ c := Real.rpow_nonneg n.cast_nonneg c
      have hfac : 0 ≤ (k.factorial : ℝ) := by positivity
      exact mul_nonneg (div_nonneg (pow_nonneg hu_pos.le k) hfac)
        (div_nonneg (mul_nonneg (ha n) (pow_nonneg hlog k)) hpow)
  have hb_sum_n (k : ℕ) : Summable (b k) := by
    have hLs : LSeriesSummable (LSeries.logMul^[k] (fun n ↦ (a n : ℂ))) (c : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re
        (f := LSeries.logMul^[k] (fun n ↦ (a n : ℂ))) (s := (c : ℂ))
        (by simpa [LSeries.abscissaOfAbsConv_logPowMul] using hc_re)
    have hreal : Summable (fun n : ℕ ↦
        if n = 0 then 0 else a n * (Real.log n) ^ k / (n : ℝ) ^ c) := by
      rw [← Complex.summable_ofReal]
      exact hLs.congr fun n ↦ term_logPowMul_real a k c n
    simpa [b] using hreal.mul_left (u ^ k / (k.factorial : ℝ))
  refine ⟨hb_nonneg, hb_sum_n, ?_⟩
  have hre : HasSum (fun k : ℕ ↦
      (((k.factorial : ℂ)⁻¹ • ((x : ℂ) - c) ^ k • iteratedDeriv k F c)).re) (F x).re :=
    Complex.reCLM.hasSum htaylor
  refine hre.congr_fun fun k ↦ ?_
  have hderiv : iteratedDeriv k F c =
      (-1) ^ k * LSeries (LSeries.logMul^[k] (fun n ↦ (a n : ℂ))) c := by
    rw [hF_nhd.iteratedDeriv_eq, LSeries_iteratedDeriv k hc_re]
  have hxmc : (x : ℂ) - c = -(u : ℂ) := by
    dsimp [u]
    push_cast
    ring
  have hsign : (-(u : ℂ)) ^ k * (-1 : ℂ) ^ k = (u : ℂ) ^ k := by
    rw [neg_eq_neg_one_mul (u : ℂ), mul_pow, mul_comm ((-1 : ℂ) ^ k) ((u : ℂ) ^ k),
      mul_assoc, ← mul_pow]
    simp
  have hLsum : LSeries (LSeries.logMul^[k] (fun n ↦ (a n : ℂ))) c =
      ((∑' n : ℕ, if n = 0 then 0 else a n * (Real.log n) ^ k / (n : ℝ) ^ c : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr fun n ↦ term_logPowMul_real a k c n
  have hterm_eq : (k.factorial : ℂ)⁻¹ • ((x : ℂ) - c) ^ k • iteratedDeriv k F c =
      ((∑' n : ℕ, b k n : ℝ) : ℂ) := by
    rw [hderiv, smul_eq_mul, smul_eq_mul]
    calc
      (k.factorial : ℂ)⁻¹ * (((x : ℂ) - c) ^ k *
          ((-1) ^ k * LSeries (LSeries.logMul^[k] (fun n ↦ (a n : ℂ))) c))
          = (k.factorial : ℂ)⁻¹ * ((-(u : ℂ)) ^ k * (-1 : ℂ) ^ k) *
              LSeries (LSeries.logMul^[k] (fun n ↦ (a n : ℂ))) c := by
        rw [hxmc]; ring
      _ = ((u ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
            ((∑' n : ℕ, if n = 0 then 0 else a n * (Real.log n) ^ k / (n : ℝ) ^ c : ℝ) : ℂ) := by
        rw [hsign, hLsum]
        push_cast
        ring
      _ = ((∑' n : ℕ, b k n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← tsum_mul_left]
        congr 1
        refine tsum_congr fun n ↦ ?_
        dsimp [b]
        split_ifs <;> ring
  rw [hterm_eq, Complex.ofReal_re]

/-- **Landau's Theorem (Real Coefficients)**: Let `a : ℕ → ℝ` satisfy `0 ≤ a n` for all `n`, and
suppose `LSeries (fun n ↦ (a n : ℂ))` converges absolutely for `Re s > σ₀`. If `F : ℂ → ℂ`
is complex-differentiable on `Metric.ball (σ₀ : ℂ) r` (`r > 0`) and agrees with `LSeries` on
`Metric.ball (σ₀ : ℂ) r ∩ {z | σ₀ < z.re}`, then `LSeries` actually converges absolutely for
`Re s > σ₀ - r / 6` (so `abscissaOfAbsConv < σ₀`), and `F` agrees with `LSeries` on
`Metric.ball (σ₀ : ℂ) r ∩ {z | σ₀ - r / 6 < z.re}`. -/
theorem landau_theorem_real {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₀ r : ℝ} (hr : 0 < r)
    (hσ : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ σ₀)
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re →
      F z = LSeries (fun n ↦ (a n : ℂ)) z) :
    LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ σ₀ - r / 6 ∧
      (∀ s : ℂ, σ₀ - r / 6 < s.re → LSeriesSummable (fun n ↦ (a n : ℂ)) s) ∧
      (∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ - r / 6 < z.re →
        F z = LSeries (fun n ↦ (a n : ℂ)) z) := by
  let c : ℝ := σ₀ + r / 3
  let R : ℝ := 2 * r / 3
  let x : ℝ := σ₀ - r / 6
  let u : ℝ := c - x
  have hxc : x < c := by dsimp [x, c]; linarith
  have hc_gt : σ₀ < c := by dsimp [c]; linarith
  have hball_sub : Metric.ball (c : ℂ) R ⊆ Metric.ball (σ₀ : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have h1 : ‖(c : ℂ) - (σ₀ : ℂ)‖ = r / 3 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by dsimp [c]; linarith)]
      dsimp [c]; ring
    calc
      ‖z - (σ₀ : ℂ)‖ = ‖(z - (c : ℂ)) + ((c : ℂ) - (σ₀ : ℂ))‖ := by ring_nf
      _ ≤ ‖z - (c : ℂ)‖ + ‖(c : ℂ) - (σ₀ : ℂ)‖ := norm_add_le _ _
      _ < R + r / 3 := by linarith
      _ = r := by dsimp [R]; ring
  have hx_ball : (x : ℂ) ∈ Metric.ball (c : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by dsimp [x, c]; linarith)]
    dsimp [x, c, R]; linarith
  have hF_ball : DifferentiableOn ℂ F (Metric.ball (c : ℂ) R) := hF_diff.mono hball_sub
  have hc_abs : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) < c :=
    hσ.trans_lt (EReal.coe_lt_coe_iff.mpr hc_gt)
  have hF_nhd : F =ᶠ[𝓝 (c : ℂ)] LSeries (fun n ↦ (a n : ℂ)) := by
    have hopen : IsOpen (Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re}) :=
      Metric.isOpen_ball.inter (Complex.isOpen_re_gt σ₀)
    have hmem : (c : ℂ) ∈ Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re} := by
      refine ⟨?_, by simpa using hc_gt⟩
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (by dsimp [c]; linarith)]
      dsimp [c]; linarith
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact hF_eq z hz.1 hz.2
  have htaylor := Complex.hasSum_taylorSeries_on_ball hF_ball hx_ball
  obtain ⟨hb_nonneg, hb_sum_n, htaylor_real⟩ :=
    landau_taylor_real ha hxc hc_abs hF_nhd htaylor
  let b : ℕ → ℕ → ℝ := fun k n ↦
    if n = 0 then 0 else (u ^ k / (k.factorial : ℝ)) * (a n * (Real.log n) ^ k / (n : ℝ) ^ c)
  have henn_ne_top : ∑' n : ℕ, ∑' k : ℕ, ENNReal.ofReal (b k n) ≠ ⊤ := by
    rw [tsum_comm]
    have hinner (k : ℕ) :
        ∑' n : ℕ, ENNReal.ofReal (b k n) = ENNReal.ofReal (∑' n : ℕ, b k n) :=
      (ENNReal.ofReal_tsum_of_nonneg (hb_nonneg k) (hb_sum_n k)).symm
    simp_rw [hinner]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ tsum_nonneg (hb_nonneg k)) htaylor_real.summable]
    exact ENNReal.ofReal_ne_top
  have htarget_enn :
      ∑' n : ℕ, ENNReal.ofReal (if n = 0 then 0 else a n / (n : ℝ) ^ x) ≠ ⊤ := by
    have hmatch (n : ℕ) :
        ∑' k : ℕ, ENNReal.ofReal (b k n) =
          ENNReal.ofReal (if n = 0 then 0 else a n / (n : ℝ) ^ x) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [b]
      · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hpow_series : HasSum (fun k : ℕ ↦ (u * Real.log n) ^ k / (k.factorial : ℝ))
            (Real.exp (u * Real.log n)) := by
          rw [Real.exp_eq_exp_ℝ]
          exact NormedSpace.expSeries_div_hasSum_exp (u * Real.log n)
        have hcol : HasSum (fun k : ℕ ↦ b k n) (a n / (n : ℝ) ^ x) := by
          have hmul := hpow_series.mul_left (a n / (n : ℝ) ^ c)
          have hval : a n / (n : ℝ) ^ c * Real.exp (u * Real.log n) = a n / (n : ℝ) ^ x := by
            rw [mul_comm u (Real.log n), ← Real.rpow_def_of_pos hn_pos,
              div_eq_mul_inv, ← Real.rpow_neg hn_pos.le, mul_assoc,
              ← Real.rpow_add hn_pos, show -c + u = -x by dsimp [u]; ring,
              Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
          rw [hval] at hmul
          refine hmul.congr_fun fun k ↦ ?_
          dsimp [b]
          rw [ite_eq_right hn, mul_pow]
          ring
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ hb_nonneg k n) hcol.summable, hcol.tsum_eq,
          ite_eq_right hn]
    simpa only [hmatch] using henn_ne_top
  have hsummable_real :
      Summable (fun n : ℕ ↦ if n = 0 then 0 else a n / (n : ℝ) ^ x) := by
    have hnn : Summable (fun n : ℕ ↦ (if n = 0 then 0 else a n / (n : ℝ) ^ x).toNNReal) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      exact htarget_enn
    rw [← NNReal.summable_coe] at hnn
    refine hnn.congr fun n ↦ ?_
    rw [Real.coe_toNNReal']
    split_ifs with hn
    · simp
    · exact max_eq_left (div_nonneg (ha n) (Real.rpow_nonneg n.cast_nonneg x))
  have hLsumm_x : LSeriesSummable (fun n ↦ (a n : ℂ)) x := by
    rw [LSeriesSummable, ← summable_norm_iff]
    refine hsummable_real.congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn, Complex.ofReal_re,
        Complex.norm_real, Real.norm_of_nonneg (ha n)]
  have hx_absc : LSeries.abscissaOfAbsConv (fun n ↦ (a n : ℂ)) ≤ x := by
    simpa using hLsumm_x.abscissaOfAbsConv_le
  refine ⟨hx_absc, fun s hs ↦ LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (hx_absc.trans_lt (EReal.coe_lt_coe_iff.mpr hs)), ?_⟩
  let W : Set ℂ := Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | x < z.re}
  have hW_conv : Convex ℝ W :=
    (convex_ball (σ₀ : ℂ) r).inter (by simpa using convex_re_gt_EReal x)
  have hF_anW : AnalyticOnNhd ℂ F W :=
    (hF_diff.analyticOnNhd Metric.isOpen_ball).mono Set.inter_subset_left
  have hL_anW : AnalyticOnNhd ℂ (LSeries (fun n ↦ (a n : ℂ))) W :=
    (LSeries_analyticOnNhd (fun n ↦ (a n : ℂ))).mono fun z hz ↦
      hx_absc.trans_lt (EReal.coe_lt_coe_iff.mpr hz.2)
  have hc_W : (c : ℂ) ∈ W := by
    refine ⟨?_, by simpa using hxc⟩
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by dsimp [c]; linarith)]
    dsimp [c]; linarith
  have hW_eq : W.EqOn F (LSeries (fun n ↦ (a n : ℂ))) :=
    hF_anW.eqOn_of_preconnected_of_eventuallyEq hL_anW hW_conv.isPreconnected hc_W hF_nhd
  intro z hz hzx
  exact hW_eq ⟨hz, hzx⟩

/-- **Landau's Theorem** for complex sequences `a : ℕ → ℂ` with nonnegative real values (`0 ≤ a`
in `ComplexOrder`): if `LSeries a` converges for `Re s > σ₀` and agrees with an analytic
function `F` on `Metric.ball (σ₀ : ℂ) r ∩ {z | σ₀ < z.re}`, then `abscissaOfAbsConv a ≤ σ₀ - r / 6`. -/
theorem landau_theorem {a : ℕ → ℂ} (ha : 0 ≤ a) {σ₀ r : ℝ} (hr : 0 < r)
    (hσ : LSeries.abscissaOfAbsConv a ≤ σ₀)
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re → F z = LSeries a z) :
    LSeries.abscissaOfAbsConv a ≤ σ₀ - r / 6 ∧
      (∀ s : ℂ, σ₀ - r / 6 < s.re → LSeriesSummable a s) ∧
      (∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ - r / 6 < z.re → F z = LSeries a z) := by
  let aR : ℕ → ℝ := fun n ↦ (a n).re
  have haR : ∀ n, 0 ≤ aR n := fun n ↦ (Complex.le_def.mp (ha n)).1
  have ha_eq : (fun n ↦ (aR n : ℂ)) = a := by
    ext n
    have him : (a n).im = 0 := (Complex.le_def.mp (ha n)).2.symm
    exact Complex.ext rfl him.symm
  simpa only [ha_eq] using landau_theorem_real haR hr (by simpa [ha_eq] using hσ) hF_diff
    (by simpa [ha_eq] using hF_eq)

/-- **Landau's Theorem (Real-Interval Hypothesis)**: agreeing with an analytic function `F` near
`σ₀` on a real interval `(σ₀, σ₀ + w)` already forces convergence past `σ₀`. -/
theorem landau_theorem_of_eqOn_Ioo {a : ℕ → ℂ} (ha : 0 ≤ a) {σ₀ r w : ℝ}
    (hr : 0 < r) (hw : 0 < w) (hσ : LSeries.abscissaOfAbsConv a ≤ σ₀)
    {F : ℂ → ℂ} (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ t : ℝ, σ₀ < t → t < σ₀ + w → F t = LSeries a t) :
    LSeries.abscissaOfAbsConv a ≤ σ₀ - r / 6 := by
  let U : Set ℂ := Metric.ball (σ₀ : ℂ) r ∩ {z : ℂ | σ₀ < z.re}
  have hU_conv : Convex ℝ U :=
    (convex_ball (σ₀ : ℂ) r).inter (by simpa using convex_re_gt_EReal σ₀)
  have hF_an : AnalyticOnNhd ℂ F U :=
    (hF_diff.analyticOnNhd Metric.isOpen_ball).mono Set.inter_subset_left
  have hL_an : AnalyticOnNhd ℂ (LSeries a) U :=
    (LSeries_analyticOnNhd a).mono fun z hz ↦ hσ.trans_lt (EReal.coe_lt_coe_iff.mpr hz.2)
  let t₀ : ℝ := σ₀ + min r w / 2
  have ht₀_pos : 0 < min r w / 2 := half_pos (lt_min hr hw)
  have ht₀_U : (t₀ : ℂ) ∈ U := by
    refine ⟨?_, by simpa [t₀] using ht₀_pos⟩
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by dsimp [t₀]; linarith)]
    dsimp [t₀]
    linarith [min_le_left r w]
  have hfreq : ∃ᶠ z in 𝓝[≠] (t₀ : ℂ), F z = LSeries a z := by
    let seq : ℕ → ℂ := fun k ↦ ((t₀ + min r w / (2 * (k + 2 : ℝ)) : ℝ) : ℂ)
    have hseq_ne : ∀ k : ℕ, seq k ≠ (t₀ : ℂ) := by
      intro k hk
      have h1 : t₀ + min r w / (2 * (k + 2 : ℝ)) = t₀ := Complex.ofReal_injective hk
      have hpos : 0 < min r w / (2 * (k + 2 : ℝ)) := by positivity
      linarith
    have hseq_tendsto : Tendsto seq atTop (𝓝[≠] (t₀ : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hseq_ne⟩
      have hreal : Tendsto (fun k : ℕ ↦ t₀ + min r w / (2 * (k + 2 : ℝ))) atTop (𝓝 (t₀ + 0)) := by
        refine tendsto_const_nhds.add ?_
        have hdenom : Tendsto (fun k : ℕ ↦ 2 * ((k : ℝ) + 2)) atTop atTop :=
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num)
        exact tendsto_const_nhds.div_atTop hdenom
      rw [add_zero] at hreal
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    refine hseq_tendsto.frequently (Eventually.of_forall fun k ↦ ?_).frequently
    have hdiv_pos : 0 < min r w / (2 * (k + 2 : ℝ)) := by positivity
    have hdiv_le : min r w / (2 * (k + 2 : ℝ)) < min r w / 2 := by
      gcongr
      linarith
    refine hF_eq _ (by dsimp [t₀]; linarith) ?_
    dsimp [t₀]
    linarith [min_le_right r w]
  have hEqOn : U.EqOn F (LSeries a) :=
    hF_an.eqOn_of_preconnected_of_frequently_eq hL_an hU_conv.isPreconnected ht₀_U hfreq
  exact (landau_theorem ha hr hσ hF_diff fun z hz1 hz2 ↦ hEqOn ⟨hz1, hz2⟩).1

/-- **Singularity at the Abscissa**: if `0 ≤ a` and `abscissaOfAbsConv a = (σ₀ : EReal)` is
finite, then `LSeries a` cannot be analytically continued to any neighborhood of `(σ₀ : ℂ)`. -/
theorem not_analyticAt_of_abscissaOfAbsConv_eq {a : ℕ → ℂ} (ha : 0 ≤ a) {σ₀ : ℝ}
    (hσ : LSeries.abscissaOfAbsConv a = σ₀) {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF_diff : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hF_eq : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < z.re → F z = LSeries a z) : False := by
  have hle := (landau_theorem ha hr hσ.le hF_diff hF_eq).1
  rw [hσ] at hle
  have hlt : σ₀ ≤ σ₀ - r / 6 := EReal.coe_le_coe_iff.mp hle
  linarith

end AnalyticNumberTheory.DirichletSeries
