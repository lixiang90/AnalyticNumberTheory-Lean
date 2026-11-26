import AnalyticNumberTheory.PrimeDistribution.GoldstonZeroSum
import AnalyticNumberTheory.PrimeDistribution.HighTruncation
import AnalyticNumberTheory.PrimeDistribution.LogarithmicMangoldtSlope

/-!
# Goldston's conditional error in the truncated explicit formula

Monotonicity brackets the inclusive Chebyshev function by signed logarithmic
slopes at distance 1/(2T). Their sharp zero approximations have the same
center and the same O(x/T + √x log T) error.
-/

noncomputable section

open Complex Filter
open scoped Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- Goldston's RH truncation estimate, with absolute implied constant.
It holds at every real height T ≥ 2 and all x ≥ exp(2), including prime powers. -/
theorem goldston_truncated_explicit_formula_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x T : ℝ}, Real.exp 2 ≤ x → 2 ≤ T →
      ‖(Chebyshev.psi x:ℂ)-(x:ℂ)+sharpZetaZeroSum x T‖ ≤ C*(x/T+Real.sqrt x*Real.log T) := by
  obtain ⟨M,hM,HM⟩ := norm_tsum_logarithmicPoleSlope_sub_sharp_le_of_rh hRH
  obtain ⟨Z,HZ⟩ := exists_logarithmicMangoldtSlope_explicit_formula
  let c := Complex.log (2*(Real.pi:ℂ))
  let d := ‖c‖+2
  have hd : 0 < d := by dsimp only [d]; positivity
  let A := 1+M+2*d
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨2*A,by positivity,?_⟩
  intro x T hx hT
  let u := Real.log x
  let X := x/T
  let Y := Real.sqrt x*Real.log T
  let R := A*(X+Y)
  let z := (x:ℂ)-sharpZetaZeroSum x T
  have hx₀ := (Real.exp_pos 2).trans_le hx
  have hT₀ : 0 < T := by linarith
  have hu : 2 ≤ u := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hx
  have he : Real.exp u = x := Real.exp_log hx₀
  have hE : Real.exp (u/2) = Real.sqrt x := by rw [Real.exp_half,he]
  have hE₁ : 1 ≤ Real.sqrt x := hE ▸ Real.one_le_exp_iff.mpr (by linarith : 0 ≤ u/2)
  have hL : 1/2 ≤ Real.log T := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hT)
  have hX : 0 ≤ X := div_nonneg hx₀.le hT₀.le
  have hY : 1/2 ≤ Y := hL.trans (le_mul_of_one_le_left (by linarith) hE₁)
  have hδ : 0 < 1/(2*T) := by positivity
  have hδ₁ : 1/(2*T) ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2*T)).mpr (by linarith)
  have H (k : ℝ) (hk : |k| = 1/(2*T)) : ‖(logarithmicMangoldtSlope u k:ℂ)-z‖ ≤ R := by
    have hk₀ := abs_pos.mp (hk ▸ hδ)
    have hk₁ := hk.le.trans hδ₁
    have hv : 1 ≤ u+k := by linarith [(abs_le.mp hk₁).1]
    let N := ∑' n, logarithmicPoleSlope (Z.zero n) u k
    let V := ∑' n, logarithmicPoleSlope (trivialZetaZero n) u k
    have hN := HM Z (by linarith : 0 ≤ u) (by linarith : 0 ≤ u+k) hT hk
    rw [he,hE] at hN
    have hN' : ‖N-sharpZetaZeroSum x T‖ ≤ M*Y := hN.trans_eq (by dsimp only [Y]; ring)
    have hV : ‖V‖ ≤ 2 := norm_tsum_logarithmicPoleSlope_trivial_le (by linarith) hv hk₀
    have hmain := norm_logarithmicPoleSlope_sub_residue_le (ω := (1:ℂ)) one_ne_zero u hk₀
      (by simpa only [one_mul,Complex.norm_real,Real.norm_eq_abs] using hk₁)
    simp only [one_mul,div_one,←Complex.ofReal_exp,Complex.one_re,he] at hmain
    have hmain' : ‖logarithmicPoleSlope 1 u k-(x:ℂ)‖ ≤ X := hmain.trans <| calc
      x*|k| = x/(2*T) := by rw [hk]; ring
      _ ≤ x/T := div_le_div_of_nonneg_left hx₀.le hT₀ (by linarith)
    have hid : (logarithmicMangoldtSlope u k:ℂ)-z =
        ((logarithmicPoleSlope 1 u k-(x:ℂ))-(N-sharpZetaZeroSum x T))-c-V := by
      rw [HZ (u := u) (h := k) (by linarith) (zero_le_one.trans hv) hk₀]
      dsimp only [N,V,c,z]
      ring
    rw [hid]
    calc
      _ ≤ ((‖logarithmicPoleSlope 1 u k-(x:ℂ)‖+‖N-sharpZetaZeroSum x T‖)+‖c‖)+‖V‖ :=
        (norm_sub_le ..).trans (add_le_add (norm_sub_le .. |>.trans (add_le_add (norm_sub_le ..) le_rfl)) le_rfl)
      _ ≤ (X+M*Y)+‖c‖+2 := by gcongr
      _ ≤ R := by
        dsimp only [R,A,d] at *
        nlinarith only [mul_le_mul_of_nonneg_left hY hd.le,mul_nonneg hM.le hX,
          mul_nonneg hd.le hX,hY]
  let h := 1/(2*T)
  have hp := H h (abs_of_pos hδ)
  have hm := H (-h) ((abs_neg _).trans (abs_of_pos hδ))
  have hb := logarithmicMangoldtSlope_brackets u hδ
  rw [he] at hb
  have hre (v : ℝ) (hv : ‖(v:ℂ)-z‖ ≤ R) : |v-z.re| ≤ R := (Complex.abs_re_le_norm _).trans hv
  have hr : |Chebyshev.psi x-z.re| ≤ R := abs_le.mpr ⟨by linarith [(abs_le.mp (hre _ hm)).1,hb.1],
    by linarith [(abs_le.mp (hre _ hp)).2,hb.2]⟩
  have hi : |z.im| ≤ R := by
    simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg] using (Complex.abs_im_le_norm _).trans hp
  rw [show (Chebyshev.psi x:ℂ)-(x:ℂ)+sharpZetaZeroSum x T = (Chebyshev.psi x:ℂ)-z by dsimp only [z]; ring]
  calc
    _ ≤ |Chebyshev.psi x-z.re|+|z.im| := by
      simpa only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg]
        using Complex.norm_le_abs_re_add_abs_im ((Chebyshev.psi x:ℂ)-z)
    _ ≤ R+R := add_le_add hr hi
    _ = _ := by dsimp only [R,X,Y]; ring

/-- At heights from √x/log x up to any fixed power of x the truncation error
is O(√x log x), uniformly in the choice of height. -/
theorem goldston_truncation_of_polynomial_height (hRH : RiemannHypothesisProp) {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ T : ℝ, Real.sqrt x/Real.log x ≤ T → T ≤ x^a →
      ‖(Chebyshev.psi x:ℂ)-(x:ℂ)+sharpZetaZeroSum x T‖ ≤ K*(Real.sqrt x*Real.log x) := by
  obtain ⟨C,hC,HC⟩ := goldston_truncated_explicit_formula_of_rh hRH
  refine ⟨C*(1+a),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 2),eventually_gt_atTop (1:ℝ),
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound (by norm_num : (0:ℝ) < 1/2)] with x hx hx₁ hs
  intro T hlo hhi
  have hx₀ := zero_lt_one.trans hx₁
  have hL := Real.log_pos hx₁
  have hroot := Real.sqrt_pos.mpr hx₀
  simp only [←Real.sqrt_eq_rpow,Real.norm_eq_abs,abs_of_pos hL,abs_of_pos hroot] at hs
  have hT : 2 ≤ T := ((le_div_iff₀ hL).mpr (by linarith)).trans hlo
  have hT₀ : 0 < T := by linarith
  have h₁ : x/T ≤ Real.sqrt x*Real.log x := by
    apply (div_le_iff₀ hT₀).mpr
    have H := mul_le_mul_of_nonneg_left ((div_le_iff₀ hL).mp hlo) hroot.le
    nlinarith only [H,Real.sq_sqrt hx₀.le]
  have h₂ : Real.log T ≤ a*Real.log x := (Real.log_le_log hT₀ hhi).trans_eq (Real.log_rpow hx₀ a)
  calc
    _ ≤ C*(x/T+Real.sqrt x*Real.log T) := HC hx hT
    _ ≤ C*(Real.sqrt x*Real.log x+Real.sqrt x*(a*Real.log x)) := by gcongr
    _ = _ := by ring

/-- Goldston's cutoff for a square-root logarithmic error under RH. Every height
above √x/log x is allowed, with one constant independent of both x and T. -/
theorem goldston_truncation_sqrt_log_of_rh (hRH : RiemannHypothesisProp) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ T : ℝ, Real.sqrt x/Real.log x ≤ T →
      ‖(Chebyshev.psi x:ℂ)-(x:ℂ)+sharpZetaZeroSum x T‖ ≤ K*(Real.sqrt x*Real.log x) := by
  obtain ⟨C,hC,HC⟩ := goldston_truncation_of_polynomial_height hRH (by norm_num : (0:ℝ)<8)
  obtain ⟨B,hB,HB⟩ := sharp_explicit_formula_high_truncation
  refine ⟨max C B,lt_max_of_lt_left hC,?_⟩
  filter_upwards [HC,HB,eventually_ge_atTop (1:ℝ)] with x hx hy hx₁
  intro T hT
  have hL := Real.log_nonneg hx₁
  have hroot : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx₁
  have hN := mul_nonneg (Real.sqrt_nonneg x) hL
  by_cases hp : T ≤ x^8
  · exact (hx T hT (by simpa only [Real.rpow_ofNat] using hp)).trans
      (mul_le_mul_of_nonneg_right (le_max_left ..) hN)
  · apply (hy (le_of_not_ge hp)).trans
    calc
      _ ≤ B*(Real.sqrt x*Real.log x) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hL hroot) hB.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) hN

end AnalyticNumberTheory.PrimeDistribution
