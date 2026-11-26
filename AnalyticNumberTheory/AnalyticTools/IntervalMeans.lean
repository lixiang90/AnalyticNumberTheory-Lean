import AnalyticNumberTheory.AnalyticTools.ExponentialMeans

/-! # Exponential means on intervals with moving endpoints -/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.AnalyticTools

/-- Integral average on a real interval with specified endpoints. -/
def intervalMean (f : ℝ → ℂ) (x y : ℝ) : ℂ :=
  (∫ t : ℝ in x..y, f t) / ((y - x : ℝ) : ℂ)

/-- A symmetric interval is the special case of endpoints `-T` and `T`. -/
theorem intervalMean_neg_self (f : ℝ → ℂ) (T : ℝ) :
    intervalMean f (-T) T = symmetricMean f T := by
  unfold intervalMean symmetricMean
  push_cast
  rw [sub_neg_eq_add, two_mul]

/-- Translating an interval multiplies the mean of a single frequency by its
phase at the midpoint. Only the interval length enters the sinc factor. -/
theorem intervalMean_exp {x y : ℝ} (hxy : x ≠ y) (r : ℝ) :
    intervalMean (fun t : ℝ => Complex.exp ((r*t : ℝ) * I)) x y =
      Complex.exp ((r*((x+y)/2) : ℝ) * I) * (Real.sinc (r*((y-x)/2)) : ℂ) := by
  let m := (x+y)/2
  let w := (y-x)/2
  have hl : -w + m = x := by dsimp [w, m]; ring
  have hr : w + m = y := by dsimp [w, m]; ring
  have hw : w ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxy.symm) two_ne_zero
  let E (t : ℝ) := Complex.exp ((r*t : ℝ) * I)
  have he (t : ℝ) : E (t+m) = E m * E t := by
    dsimp [E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hi : (∫ t : ℝ in x..y, E t) = E m * ∫ t : ℝ in -w..w, E t := by
    calc
      _ = ∫ t : ℝ in -w+m..w+m, E t := by rw [hl, hr]
      _ = ∫ t : ℝ in -w..w, E (t+m) := (intervalIntegral.integral_comp_add_right E m).symm
      _ = _ := by simp only [he, intervalIntegral.integral_const_mul]
  have hden : ((y-x : ℝ) : ℂ) = 2 * (w : ℂ) := by dsimp [w]; push_cast; ring
  change (∫ t : ℝ in x..y, E t) / ((y-x : ℝ) : ℂ) = E m * _
  rw [hi, hden, mul_div_assoc, ← symmetricMean, symmetricMean_exp hw]

private theorem norm_intervalMean_exp {x y : ℝ} (hxy : x ≠ y) (r : ℝ) :
    ‖intervalMean (fun t : ℝ => Complex.exp ((r*t : ℝ) * I)) x y‖ =
      |Real.sinc (r*((y-x)/2))| := by
  rw [intervalMean_exp hxy, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- On any family of intervals whose lengths tend to infinity, the mean of
a nonzero real frequency vanishes and that of the zero frequency tends to one. -/
theorem tendsto_intervalMean_exp {α : Type*} {l : Filter α} (x y : α → ℝ)
    (hlen : Tendsto (fun k => y k - x k) l atTop) (r : ℝ) :
    Tendsto (fun k => intervalMean (fun t : ℝ => Complex.exp ((r*t : ℝ) * I)) (x k) (y k)) l
      (𝓝 (if r = 0 then 1 else 0)) := by
  have hpos := hlen.eventually_gt_atTop 0
  by_cases hr : r = 0
  · subst r
    apply tendsto_const_nhds.congr'
    filter_upwards [hpos] with k hk
    rw [intervalMean_exp (sub_pos.mp hk).ne]
    simp
  · simp only [hr, ↓reduceIte]
    have ht := (tendsto_sinc_frequency r).comp (hlen.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have hdec : Tendsto (fun k => |Real.sinc (r*((y k-x k)/2))|) l (𝓝 0) := by
      simpa [hr, Function.comp_def, Complex.norm_real] using ht.norm
    apply squeeze_zero_norm' _ hdec
    filter_upwards [hpos] with k hk
    exact (norm_intervalMean_exp (sub_pos.mp hk).ne r).le

/-- The integral means of an absolutely summable expansion on any intervals
of lengths tending to infinity converge to the total coefficient at frequency
zero. The endpoints may move independently of the coefficients. -/
theorem tendsto_intervalMean_expansion {ι α : Type*} [Countable ι] {l : Filter α}
    (c : ι → ℂ) (ω : ι → ℝ) (hc : Summable (fun j => ‖c j‖)) (x y : α → ℝ)
    (hlen : Tendsto (fun k => y k - x k) l atTop) :
    Tendsto (fun k => intervalMean (exponentialSeries c ω) (x k) (y k)) l
      (𝓝 (∑' j, if ω j = 0 then c j else 0)) := by
  let E (j : ι) (t : ℝ) := Complex.exp ((ω j*t : ℝ) * I)
  have hlim (j : ι) : Tendsto (fun k => c j * intervalMean (E j) (x k) (y k)) l
      (𝓝 (if ω j = 0 then c j else 0)) := by
    simpa only [E, mul_ite, mul_one, mul_zero] using
      (tendsto_intervalMean_exp x y hlen (ω j)).const_mul (c j)
  have hbound : ∀ᶠ k in l, ∀ j, ‖c j * intervalMean (E j) (x k) (y k)‖ ≤ ‖c j‖ := by
    filter_upwards [hlen.eventually_gt_atTop 0] with k hk
    intro j
    rw [norm_mul, show ‖intervalMean (E j) (x k) (y k)‖ = _ from norm_intervalMean_exp (sub_pos.mp hk).ne (ω j)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sinc_le_one _)
  apply (tendsto_tsum_of_dominated_convergence hc hlim hbound).congr
  intro k
  rw [intervalMean, integral_exponentialSeries c ω hc, ← tsum_div_const]
  exact tsum_congr fun j => (mul_div_assoc _ _ _).symm

end AnalyticNumberTheory.AnalyticTools
