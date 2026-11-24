import AnalyticNumberTheory.RiemannZeta.FourthMomentMainTerms
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialDiagonals
import AnalyticNumberTheory.RiemannZeta.FourthMoment

/-!
# Logarithmic upper bound for the fourth zeta moment

Two ordinary divisor polynomials approximate zeta squared in mean square with
error `O(T (1+log T)^3)`. Their own square means give the classical upper bound
of order `T (log T)^4` for the fourth moment.
-/

open Complex Real MeasureTheory Filter Set
open scoped Asymptotics
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.RiemannZeta

private theorem short_fourthMomentPiece_bound :
    ∃ C > (0:ℝ), ∀ {T : ℝ}, 2 ≤ T → ∀ neg : Bool,
    (∫ t in T..2*T, ‖fourthMomentPiece (-(1/4)) ⌈T⌉₊ neg t‖^2) ≤ C*T*(1+Real.log T)^3 := by
  obtain ⟨K,hK,h⟩ := norm_fourthMomentKernel_le (c := -(1/4)) (by norm_num) (by norm_num)
  refine ⟨64*π*(1+4*π)*K^2,by positivity,?_⟩
  intro T hT neg
  have hh := divisorPolynomial_quarter_gaussian_log hT hK.le neg (fourthMomentKernel (-(1/4)) neg)
    (fun t ht v => h hT ⟨ht.1.le,ht.2⟩ neg v)
  change (∫ t in T..2*T, ‖∫ v, fourthMomentKernel (-(1/4)) neg t v *
    divisorPolynomial ⌈T⌉₊ (((1/2+(-(1/4)):ℝ):ℂ)+((if neg then v-t else v+t):ℝ)*I)‖^2) ≤ _
  rw [show (((1/2+(-(1/4)):ℝ):ℂ)) = 1/4 by norm_num]
  exact hh

private theorem long_fourthMomentPiece_bound :
    ∃ C > (0:ℝ), ∀ {T : ℝ}, 2 ≤ T → ∀ neg : Bool,
    (∫ t in T..2*T, ‖fourthMomentPiece 4 ⌈T^2⌉₊ neg t - fourthMomentPiece 4 ⌈T⌉₊ neg t‖^2) ≤
      C*T*(1+Real.log T)^3 := by
  obtain ⟨K,hK,h⟩ := norm_fourthMomentKernel_le (c := 4) (by norm_num) (by norm_num)
  let A := 108*π*(1+4*π)*K^2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨4*A,by positivity,?_⟩
  intro T hT neg
  let N := ⌈T⌉₊
  let M := ⌈T^2⌉₊
  have hT0 : 0 < T := by linarith
  have htlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hTN : T ≤ (N:ℝ) := Nat.le_ceil T
  have hN : 0 < N := Nat.ceil_pos.mpr hT0
  have hNM : N ≤ M := Nat.ceil_mono (by nlinarith)
  have hM : (M:ℝ) ≤ 2*T^2 := by
    have hc : (M:ℝ) < T^2 + 1 := Nat.ceil_lt_add_one (sq_nonneg T)
    nlinarith
  let B := A*T*(1+Real.log T)^3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (j : ℕ) : let X := 2^j*N
      X ≤ M → (∫ t in T..2*T, ‖fourthMomentPiece 4 (min M (2*X)) neg t - fourthMomentPiece 4 X neg t‖^2) ≤
        B*(1/4:ℝ)^j := by
    let X := 2^j*N
    let Y := min M (2*X)
    dsimp only
    intro hX
    have hXY : X ≤ Y := le_min hX (by omega)
    have hx : (2:ℝ)^j*T ≤ X := by dsimp [X]; push_cast; exact mul_le_mul_of_nonneg_left hTN (by positivity)
    have hY : (Y:ℝ) ≤ 2*T^2 := le_trans (Nat.cast_le.mpr (min_le_left ..)) hM
    have hh := divisorPolynomial_tail_gaussian_log hT hK.le hXY (min_le_right ..) hx hY neg (fourthMomentKernel 4 neg)
      (fun t ht v => by have hv := h hT ⟨ht.1.le,ht.2⟩ neg v; simpa using hv)
    have he := intervalIntegral.integral_congr (μ := volume) (a := T) (b := 2*T) (f := fun t =>
      ‖fourthMomentPiece 4 Y neg t-fourthMomentPiece 4 X neg t‖^2)
      (g := fun t => ‖∫ v, fourthMomentKernel 4 neg t v *
        (divisorPolynomial Y ((9/2:ℂ)+((if neg then v-t else v+t):ℝ)*I) -
        divisorPolynomial X ((9/2:ℂ)+((if neg then v-t else v+t):ℝ)*I))‖^2) (by
        intro t ht
        rw [uIcc_of_le (by linarith : T ≤ 2*T)] at ht
        dsimp only
        rw [fourthMomentPiece_sub_eq_integral (c := 4) (by norm_num) (by norm_num) hT ht Y X neg]
        norm_num)
    change (∫ t in T..2*T, ‖fourthMomentPiece 4 Y neg t-fourthMomentPiece 4 X neg t‖^2) ≤ _
    rw [he]
    apply hh.trans
    change B*(1/2:ℝ)^(7*j) ≤ B*(1/4:ℝ)^j
    rw [pow_mul]
    apply mul_le_mul_of_nonneg_left _ hB
    exact pow_le_pow_left₀ (by positivity) (by norm_num) j
  exact (fourthMomentPiece_tail_mean_sq hT hB hN hNM neg hb).trans_eq (by dsimp [B]; ring)

/-- In mean square on `[T,2T]`, the approximation of zeta squared by its two ordinary divisor
polynomials of length `⌈T⌉` has error `O(T (1+log T)^3)`. -/
theorem zeta_sq_sub_fourthMomentMainTerms_mean_sq :
    ∃ C > (0:ℝ), ∀ {T : ℝ}, 2 ≤ T →
    (∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)^2 -
      (fourthMomentMainTerm ⌈T⌉₊ false t + fourthMomentMainTerm ⌈T⌉₊ true t)‖^2) ≤
      C*T*(1+Real.log T)^3 := by
  obtain ⟨B,hB,h⟩ := norm_zeta_sq_sub_fourthMomentMainTerms_le
  obtain ⟨C,hC,hc⟩ := short_fourthMomentPiece_bound
  obtain ⟨D,hD,hd⟩ := long_fourthMomentPiece_bound
  refine ⟨2*B^2 + 16*(C+D),by positivity,?_⟩
  intro T hT
  let N := ⌈T⌉₊
  let M := ⌈T^2⌉₊
  let A := fourthMomentMainTerm N
  let P := fourthMomentPiece (-(1/4)) N
  let Q (neg : Bool) (t : ℝ) := fourthMomentPiece 4 M neg t-fourthMomentPiece 4 N neg t
  let U (neg : Bool) (t : ℝ) := P neg t+Q neg t
  let Z (t : ℝ) := riemannZeta ((1/2:ℂ)+t*I)^2
  let E (t : ℝ) := Z t - ((A false t+P false t+Q false t)+(A true t+P true t+Q true t))
  let L := (1+Real.log T)^3
  have hab : T ≤ 2*T := by linarith
  have htlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hl : 1 ≤ L := one_le_pow₀ (by linarith : 1 ≤ 1+Real.log T) (n := 3)
  have hp (neg : Bool) : ContinuousOn (P neg) (Icc T (2*T)) := continuousOn_fourthMomentPiece (by norm_num) (by norm_num) hT N neg
  have hq (neg : Bool) : ContinuousOn (Q neg) (Icc T (2*T)) :=
    (continuousOn_fourthMomentPiece (c := 4) (by norm_num) (by norm_num) hT M neg).sub
    (continuousOn_fourthMomentPiece (c := 4) (by norm_num) (by norm_num) hT N neg)
  have hu (neg : Bool) : ContinuousOn (U neg) (Icc T (2*T)) := (hp neg).add (hq neg)
  have hE : ContinuousOn E (Icc T (2*T)) := (continuous_riemannZeta_half.pow 2).continuousOn.sub
    ((((continuous_fourthMomentMainTerm N false).continuousOn.add (hp false)).add (hq false)).add
    (((continuous_fourthMomentMainTerm N true).continuousOn.add (hp true)).add (hq true)))
  have hEb : (∫ t in T..2*T, ‖E t‖^2) ≤ T*B^2 := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab ((hE.norm.pow 2).intervalIntegrable_of_Icc hab)
      intervalIntegrable_const (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (h hT ht N) 2)
    apply hi.trans_eq
    rw [intervalIntegral.integral_const]; change (2*T-T)*B^2 = T*B^2; ring
  have hU (neg : Bool) := integral_norm_add_sq_le hab (hp neg) (hq neg) (hc hT neg) (hd hT neg)
  have hV := integral_norm_add_sq_le hab (hu false) (hu true) (hU false) (hU true)
  have hAll := integral_norm_add_sq_le hab hE ((hu false).add (hu true)) hEb hV
  have he (t : ℝ) : Z t-(A false t+A true t) = E t+(U false t+U true t) := by dsimp only [E,U]; ring
  change (∫ t in T..2*T, ‖Z t-(A false t+A true t)‖^2) ≤ _
  simp_rw [he]
  apply hAll.trans
  have hBL : T*B^2 ≤ T*B^2*L := le_mul_of_one_le_right (by positivity) hl
  change 2*(T*B^2+2*(2*(C*T*L+D*T*L)+2*(C*T*L+D*T*L))) ≤ (2*B^2+16*(C+D))*T*L
  linarith

/-- The sharp order upper bound for the critical-line fourth moment on dyadic intervals. -/
theorem fourthMoment_riemannZeta_dyadic_log_le :
    ∃ C > (0:ℝ), ∀ {T : ℝ}, 2 ≤ T →
      (∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) ≤ C*T*(1+Real.log T)^4 := by
  obtain ⟨D,hD,hd⟩ := zeta_sq_sub_fourthMomentMainTerms_mean_sq
  let B := 16*(1+4*π)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨2*D+8*B,by positivity,?_⟩
  intro T hT
  let A := fourthMomentMainTerm ⌈T⌉₊
  let Z (t : ℝ) := riemannZeta ((1/2:ℂ)+t*I)^2
  let E (t : ℝ) := Z t-(A false t+A true t)
  have hab : T ≤ 2*T := by linarith
  have hA (neg : Bool) := (continuous_fourthMomentMainTerm ⌈T⌉₊ neg).continuousOn (s := Icc T (2*T))
  have hmain (neg : Bool) : (∫ t in T..2*T, ‖A neg t‖^2) ≤ B*T*(1+Real.log T)^4 := by
    dsimp only [A]; simp_rw [norm_fourthMomentMainTerm_eq]; exact divisorPolynomial_critical_dyadic_log hT
  have he : ContinuousOn E (Icc T (2*T)) := (continuous_riemannZeta_half.pow 2).continuousOn.sub ((hA false).add (hA true))
  have hboth := integral_norm_add_sq_le hab (hA false) (hA true) (hmain false) (hmain true)
  have hsum := integral_norm_add_sq_le hab he ((hA false).add (hA true)) (hd hT) hboth
  have hid (t : ℝ) : ‖Z t‖^2 = ‖E t+(A false t+A true t)‖^2 := by dsimp only [E]; rw [sub_add_cancel]
  have hpow (t : ℝ) : ‖riemannZeta ((1/2:ℂ)+t*I)‖^4 = ‖Z t‖^2 := by dsimp only [Z]; rw [norm_pow]; ring
  simp_rw [hpow,hid]
  apply hsum.trans
  have hlog : 1 ≤ 1+Real.log T := by linarith [Real.log_nonneg (by linarith : 1 ≤ T)]
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by decide : 3 ≤ 4)) (show 0 ≤ D*T by positivity)
  linarith

/-- Global fourth-moment bound, valid from height one onwards. -/
theorem fourthMoment_riemannZeta_log_le :
    ∃ C > (0:ℝ), ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) ≤ C*T*(1+Real.log T)^4 := by
  let g (t : ℝ) := (1+Real.log (max 1 t))^4
  have hg : Continuous g := (continuous_const.add ((continuous_const.max continuous_id).log (fun t => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 t))))).pow 4
  have hgp (t : ℝ) : 0 < g t := by dsimp [g]; have := Real.log_nonneg (le_max_left 1 t); positivity
  have hmono : MonotoneOn g (Ici 1) := by
    intro x hx y hy hxy
    change 1 ≤ x at hx
    change 1 ≤ y at hy
    dsimp [g]; rw [max_eq_right hx,max_eq_right hy]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hx]) (by linarith [Real.log_le_log (by linarith : 0 < x) hxy]) 4
  obtain ⟨C,hC,h⟩ := fourthMoment_riemannZeta_dyadic_log_le
  obtain ⟨K,hK,hk⟩ := integral_from_one_of_weighted_dyadic (f := fun t : ℝ => ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) (continuous_riemannZeta_half.norm.pow 4)
    (fun _ => pow_nonneg (norm_nonneg _) 4) hg hgp hmono (by norm_num : 0 < (1:ℝ)) hC.le
    (fun T hT => by simpa only [Real.rpow_one,g,max_eq_right (by linarith : 1 ≤ T)] using h hT)
  exact ⟨K,hK,fun T ht => by simpa only [g,max_eq_right ht,Real.rpow_one] using hk T ht⟩

/-- On the critical line the fourth moment is `O(T (log T)^4)` as `T → ∞`. -/
theorem fourthMoment_riemannZeta_log_isBigO :
    (fun T : ℝ => ∫ t in (1:ℝ)..T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4) =O[atTop]
      (fun T : ℝ => T*(Real.log T)^4) := by
  obtain ⟨C,hC,h⟩ := fourthMoment_riemannZeta_log_le
  refine Asymptotics.isBigO_iff.mpr ⟨16*C,?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have h1 : 1 ≤ T := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hT
  have hl : 1 ≤ Real.log T := (Real.le_log_iff_exp_le (by linarith)).mpr hT
  rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg h1 (fun _ _ => by positivity)),Real.norm_of_nonneg (by positivity : 0 ≤ T*(Real.log T)^4)]
  apply (h T h1).trans
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log T) (by linarith : 1+Real.log T ≤ 2*Real.log T) 4) (show 0 ≤ C*T by positivity)
  nlinarith

end AnalyticNumberTheory.RiemannZeta
