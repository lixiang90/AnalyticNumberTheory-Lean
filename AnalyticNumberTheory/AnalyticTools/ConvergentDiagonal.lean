import AnalyticNumberTheory.AnalyticTools.SquareMeanLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Mean squares with a convergent diagonal

Uniform finite-polynomial mean estimates pass to any linearly growing
cutoff. Square summability makes the contribution beyond a shorter
initial segment tend to zero.
-/

open Real Complex Filter MeasureTheory Set
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- Mean-square limit for a family of finite polynomials with convergent
diagonal and length comparable to the upper integration limit. -/
theorem tendsto_squareMean_of_convergent_diagonal
    (P : ℕ → ℝ → ℂ) (D : ℕ → ℝ) {c K L : ℝ} (N : ℝ → ℕ)
    (hP : ∀ n, Continuous (P n)) (hd : Tendsto D atTop (𝓝 c))
    (hK : 0≤K) (hL : 0≤L)
    (hsize : ∀ᶠ T : ℝ in atTop, ⌊T⌋₊+1≤N T ∧ (N T:ℝ)≤L*T)
    (hdiag : ∀ n : ℕ, 0<n → ∀ {T : ℝ}, 1≤T →
      |(∫ t in (1:ℝ)..T, ‖P n t‖^2)-(T-1)*D n| ≤ K*n*D n)
    (htail : ∀ m n : ℕ, m≤n → ∀ {T : ℝ}, 1≤T →
      (∫ t in (1:ℝ)..T, ‖(P m-P n) t‖^2) ≤ (T+K*n)*(D n-D m))
    (hmono : Monotone D) :
    Tendsto (fun T : ℝ => intervalSquareMean 1 T T (P (N T))) atTop (𝓝 c) := by
  let M (T : ℝ) := ⌊√T⌋₊+1
  have hM : Tendsto M atTop atTop := (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop)
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono' _ (hsize.mono fun T h => h.1)
    ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
  have hDM := hd.comp hM
  have hDN := hd.comp hN
  have hsmall : Tendsto (fun T : ℝ => (M T:ℝ)/T) atTop (𝓝 0) := by
    have hr := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).add (tendsto_const_nhds (x := (1:ℝ)) |>.div_atTop tendsto_id)
    simp only [zero_add] at hr
    apply squeeze_zero' _ _ hr
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht; positivity
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
      dsimp only [M,Function.comp_apply,id_eq]; push_cast
      rw [add_div,← Real.sqrt_div_self]
      exact add_le_add (div_le_div_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg T)) (by linarith)) le_rfl
  have hratio : Tendsto (fun T : ℝ => (T-1)/T) atTop (𝓝 1) := by
    have H := tendsto_const_nhds (x := (1:ℝ)) |>.sub ((tendsto_const_nhds (x := (1:ℝ))).div_atTop tendsto_id)
    simp only [sub_zero] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T ht
    simp only [id_eq]; field_simp
  have hmain : Tendsto (fun T : ℝ => intervalSquareMean 1 T T (P (M T))) atTop (𝓝 c) := by
    have hcenter := hratio.mul hDM
    have herr := (hsmall.mul hDM).const_mul K
    simp only [one_mul,zero_mul,mul_zero] at hcenter herr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hcenter.sub herr)
      (by simpa using hcenter.add herr)
    all_goals
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
      have h := abs_le.mp (hdiag (M T) (Nat.succ_pos _) ht)
      unfold intervalSquareMean
      first
      | apply (le_div_iff₀ (by linarith : 0<T)).mpr
        field_simp [show T ≠ 0 by linarith]; linarith [h.1]
      | apply (div_le_iff₀ (by linarith : 0<T)).mpr
        field_simp [show T ≠ 0 by linarith]; linarith [h.2]
  apply tendsto_squareMean_of_difference (F:=fun T => P (M T)) (G:=fun T => P (N T))
    (eventually_ge_atTop (1:ℝ)) (eventually_gt_atTop 0)
    (Eventually.of_forall fun T => (hP _).continuousOn)
    (Eventually.of_forall fun T => (hP _).continuousOn) hmain
  have hlim := (hDN.sub hDM).const_mul (1+K*L)
  simp only [sub_self,mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T ht
    exact div_nonneg (intervalIntegral.integral_nonneg ht fun _ _ => sq_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (1:ℝ),hsize] with T ht hs
    have hmn : M T≤N T := (Nat.succ_le_succ (Nat.floor_mono
      (Real.sqrt_le_self_iff.mpr (Or.inr ht)))).trans hs.1
    have hpos := sub_nonneg.mpr (hmono hmn)
    have hb := htail _ _ hmn ht
    apply (div_le_iff₀ (by linarith : 0<T)).mpr
    dsimp only [Function.comp_apply] at *
    nlinarith only [hb,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2 hK) hpos]

end AnalyticNumberTheory.AnalyticTools
