import AnalyticNumberTheory.ExponentialSums.VanDerCorput

/-!
# Exponential sums with a shifted logarithmic phase

On a dyadic interval the logarithm has a second derivative of size
`|τ|/M²`. Its forward difference with step `r` has a second derivative
of size `|τ| r/M³`. The constants below are uniform in the offset in
the closed unit interval and in the endpoints of an incomplete block.
-/

open Real Complex Finset Set

namespace AnalyticNumberTheory.ExponentialSums

/-- The real logarithmic phase before applying the additive character. -/
noncomputable def logPhase (τ a x : ℝ) := τ*Real.log (x+a)

/-- First derivative of the shifted logarithmic phase. -/
theorem logPhase_deriv (τ a : ℝ) {x : ℝ} (hx : 0 < x+a) :
    HasDerivAt (logPhase τ a) (τ/(x+a)) x := by
  change HasDerivAt (fun y : ℝ => τ*Real.log (y+a)) _ x
  simpa only [id_eq,div_eq_mul_inv,one_mul,mul_one] using
    (((hasDerivAt_id x).add_const a).log hx.ne').const_mul τ

/-- Second derivative of the shifted logarithmic phase. -/
theorem logPhase_second (τ a : ℝ) {x : ℝ} (hx : 0 < x+a) :
    HasDerivAt (fun u => τ/(u+a)) (-τ/(x+a)^2) x := by
  convert (hasDerivAt_const x τ).div ((hasDerivAt_id x).add_const a) hx.ne' using 1 <;> first | rfl | simp

/-- The second derivative test for an incomplete shifted logarithmic block. -/
theorem logPhase_second_derivative_bound {M b : ℕ} (hM : 1 ≤ M) (hb : M < b) (hb' : b ≤ 2*M)
    {a τ : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hτ : 0 < |τ|) :
    ‖∑ n ∈ Finset.Ioc M b, Complex.exp (2*Real.pi*(logPhase τ a n:ℂ)*I)‖ ≤
      200*(((b:ℝ)-M)*Real.sqrt (|τ|/(9*(M:ℝ)^2)) + (Real.sqrt (|τ|/(9*(M:ℝ)^2)))⁻¹) := by
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hu : (b:ℝ) ≤ 2*M := by exact_mod_cast hb'
  have hx {x : ℝ} (h : x ∈ Set.Icc (M:ℝ) b) : (M:ℝ) ≤ x+a ∧ x+a ≤ 3*M := by
    constructor <;> linarith [h.1,h.2,ha.1,ha.2]
  let lam := |τ|/(9*(M:ℝ)^2)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have H := vanDerCorput_second_deriv (f:=logPhase τ a) (f':=fun x => τ/(x+a))
    (f'':=fun x => -τ/(x+a)^2) hb hlam (c:=9) (by norm_num)
    (fun x h => logPhase_deriv τ a (by linarith [(hx h).1]))
    (fun x h => logPhase_second τ a (by linarith [(hx h).1]))
    (continuousOn_const.div ((continuous_id.add continuous_const).pow 2).continuousOn
      (fun x h => pow_ne_zero 2 (show x+a ≠ 0 by linarith [(hx h).1]))) (by
      intro x h
      obtain ⟨hlo,hhi⟩ := hx h
      have hh : 0<x+a := by linarith
      rw [abs_div,abs_neg,abs_of_nonneg (sq_nonneg (x+a))]
      have hl : (M:ℝ)^2 ≤ (x+a)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hlo _
      have hh' := pow_le_pow_left₀ hh.le hhi 2
      constructor
      · apply div_le_div_of_nonneg_left hτ.le (sq_pos_of_pos hh)
        nlinarith only [hh']
      · dsimp [lam]
        calc |τ|/(x+a)^2 ≤ |τ|/(M:ℝ)^2 := div_le_div_of_nonneg_left hτ.le (by positivity) hl
             _ = _ := by field_simp <;> ring)
  simpa only [show (20:ℝ)*9+20=200 by norm_num,← Real.sqrt_eq_rpow,
    Real.rpow_neg hlam.le,lam] using H

private theorem logPhase_diff_size {m x r τ : ℝ} (hm : 0<m) (hx : m≤x) (hx' : x≤3*m)
    (hr : 0<r) (hr' : r≤m) :
    |τ| * r/(256*m^3) ≤ |(-τ/(x+r)^2)-(-τ/x^2)| ∧
      |(-τ/(x+r)^2)-(-τ/x^2)| ≤ 1792*(|τ| * r/(256*m^3)) := by
  have hx0 : 0<x := by linarith
  have hxr : 0<x+r := by linarith
  have he : (-τ/(x+r)^2)-(-τ/x^2) = τ*r*(2*x+r)/(x^2*(x+r)^2) := by field_simp; ring
  rw [he,abs_div,abs_mul,abs_mul,abs_of_pos hr,abs_of_pos (by linarith : 0<2*x+r),
    abs_of_pos (by positivity : 0<x^2*(x+r)^2)]
  have hl : m^4 ≤ x^2*(x+r)^2 := by
    calc _ = m^2*m^2 := by ring
         _ ≤ _ := by gcongr <;> linarith
  have hu : x^2*(x+r)^2 ≤ (4*m)^4 := by
    calc _ ≤ (4*m)^2*(4*m)^2 := by gcongr <;> linarith
         _ = _ := by ring
  constructor
  · calc |τ| * r/(256*m^3) = |τ| * r*m/(4*m)^4 := by field_simp; ring
         _ ≤ _ := div_le_div₀ (by positivity) (by gcongr; linarith) (by positivity) hu
  · calc _ ≤ |τ| * r*(7*m)/m^4 := div_le_div₀ (by positivity) (by gcongr; linarith) (by positivity) hl
         _ = _ := by field_simp; ring

/-- Second derivative estimate for a forward difference of logarithmic
phases, uniform in the position and length of the dyadic block. -/
theorem logPhase_difference_bound {M b r : ℕ} (hM : 1≤M) (hb : M<b) (hb' : b≤2*M)
    (hr : 1≤r) (hr' : r≤M) {a τ : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (hτ : 0 < |τ|) :
    let lam := |τ| * r/(256*(M:ℝ)^3)
    ‖∑ n ∈ Finset.Ioc M b, Complex.exp (2*Real.pi*
      ((logPhase τ a (n+r:ℕ)-logPhase τ a n:ℝ):ℂ)*I)‖ ≤
        35860*(((b:ℝ)-M)*Real.sqrt lam+(Real.sqrt lam)⁻¹) := by
  let m := (M:ℝ)
  have hm : 1≤m := by dsimp [m]; exact_mod_cast hM
  have hu : (b:ℝ)≤2*m := by dsimp [m]; exact_mod_cast hb'
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr
  have hrm : (r:ℝ)≤m := by dsimp [m]; exact_mod_cast hr'
  let lam := |τ| * r/(256*m^3)
  have hlam : 0<lam := by dsimp [lam]; positivity
  let f := fun x : ℝ => logPhase τ a (x+r)-logPhase τ a x
  let f' := fun x : ℝ => τ/(x+r+a)-τ/(x+a)
  let f'' := fun x : ℝ => -τ/(x+r+a)^2-(-τ/(x+a)^2)
  have hx {x : ℝ} (h : x ∈ Set.Icc (M:ℝ) b) : m ≤ x+a ∧ x+a ≤ 3*m := by
    change (m≤x ∧ x≤(b:ℝ)) at h
    constructor <;> linarith [h.1,h.2,ha.1,ha.2]
  have h1 {x : ℝ} (h : x ∈ Set.Icc (M:ℝ) b) : 0<x+a := by linarith [(hx h).1]
  have h2 {x : ℝ} (h : x ∈ Set.Icc (M:ℝ) b) : 0<x+r+a := by linarith [h1 h]
  have hd (x) (h : x ∈ Set.Icc (M:ℝ) b) : HasDerivAt f (f' x) x := by
    simpa only [f,f',Function.comp_def,Pi.sub_def,id_eq,mul_one] using
      ((logPhase_deriv τ a (h2 h)).comp x ((hasDerivAt_id x).add_const (r:ℝ))).sub (logPhase_deriv τ a (h1 h))
  have hd' (x) (h : x ∈ Set.Icc (M:ℝ) b) : HasDerivAt f' (f'' x) x := by
    simpa only [f',f'',Function.comp_def,Pi.sub_def,id_eq,mul_one] using
      ((logPhase_second τ a (h2 h)).comp x ((hasDerivAt_id x).add_const (r:ℝ))).sub (logPhase_second τ a (h1 h))
  have hc : ContinuousOn f'' (Set.Icc (M:ℝ) b) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div (((continuous_id.add continuous_const).add continuous_const).pow 2).continuousOn
        (fun x h => pow_ne_zero 2 (h2 h).ne')
    · exact continuousOn_const.div ((continuous_id.add continuous_const).pow 2).continuousOn
        (fun x h => pow_ne_zero 2 (h1 h).ne')
  have H := vanDerCorput_second_deriv hb hlam (c:=1792) (by norm_num) hd hd' hc (fun x h => by
    simpa only [f'',show x+(r:ℝ)+a = x+a+r by ring] using
      logPhase_diff_size (τ:=τ) (by linarith : 0<m) (hx h).1 (hx h).2 hr0 hrm)
  simpa only [f,Nat.cast_add,show (20:ℝ)*1792+20=35860 by norm_num,
    Real.rpow_neg hlam.le,← Real.sqrt_eq_rpow,lam,m] using H

end AnalyticNumberTheory.ExponentialSums
