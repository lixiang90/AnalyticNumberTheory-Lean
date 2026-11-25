import AnalyticNumberTheory.DivisorProblems.DivisorCubeRoot
import AnalyticNumberTheory.DivisorProblems.CircleArc

/-!
# Exponential sums on an octant of a circle

The second derivative of `sqrt (x-t²)` has size comparable to `1/sqrt x`
throughout the first octant. Fourier smoothing and van der Corput's estimate give
a cube-root error without a dyadic loss.
-/

open Real Complex Finset Set Filter
open AnalyticNumberTheory.ExponentialSums AnalyticNumberTheory.AnalyticTools.Summation

namespace AnalyticNumberTheory.DivisorProblems

/-- A square-root frequency estimate yields an explicit smoothing bound for
the sawtooth sum of any finite family of real phases. -/
theorem abs_sum_sawtooth_of_sqrt_frequency {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) {K : ℕ} (hK : 2 ≤ K)
    (hS : ∀ n : ℕ, 0 < n → ‖∑ i ∈ S, e (n*p i)‖ ≤ C*(√n+1/√n)) :
    |∑ i ∈ S, sawtooth (p i)| ≤
      S.card/K*(1/Real.pi^2+1/2) + (C*((4*Real.pi+4)*√K)+C*(6*Real.pi))/(2*Real.pi^2) := by
  have hk : 1 < (K:ℝ) := by exact_mod_cast hK
  have hk0 : 0 < (K:ℝ) := by linarith
  let w (n : ℕ) := min 2 (2*Real.pi*n/K)
  have hf := abs_sum_sawtooth_le_exponential_sums S p (H := K^2) (by nlinarith) (inv_pos.mpr hk0) (inv_lt_one_of_one_lt₀ hk)
  have hw (n : ℕ) : ‖e (n*(K:ℝ)⁻¹)-1‖ ≤ w n := by
    rw [norm_sub_rev,norm_one_sub_e]
    have hd : distToInt (n*(K:ℝ)⁻¹) ≤ n*(K:ℝ)⁻¹ := by
      simpa [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr hk0.le))]
        using distToInt_le_abs_sub_int (n*(K:ℝ)⁻¹) 0
    apply le_min (by linarith only [Real.sin_le_one (Real.pi*distToInt (n*(K:ℝ)⁻¹))])
    calc 2*Real.sin (Real.pi*distToInt (n*(K:ℝ)⁻¹)) ≤ 2*(Real.pi*distToInt (n*(K:ℝ)⁻¹)) :=
           mul_le_mul_of_nonneg_left (Real.sin_le (by positivity [distToInt_nonneg (n*(K:ℝ)⁻¹)])) (by norm_num)
         _ ≤ 2*(Real.pi*(n*(K:ℝ)⁻¹)) := by gcongr
         _ = _ := by ring
  have hcomp := sum_smoothed_frequencies_le (K := K) (H := K^2) (by omega) (by nlinarith) hC hC
  have hsum : (K:ℝ)*∑ n ∈ Icc 1 (K^2), ‖e (n*(K:ℝ)⁻¹)-1‖*‖∑ i ∈ S, e (n*p i)‖/(n:ℝ)^2 ≤
      C*((4*Real.pi+4)*√K)+C*(6*Real.pi) := by
    apply le_trans _ hcomp
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have he := mul_le_mul (hw n) (hS n (mem_Icc.mp hn).1) (norm_nonneg _) ((norm_nonneg _).trans (hw n))
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (sq_nonneg (n:ℝ))) hk0.le
    apply hh.trans_eq
    dsimp [w]; ring
  have h := mul_le_mul_of_nonneg_left hf hk0.le
  rw [← mul_assoc,mul_inv_cancel₀ hk0.ne',one_mul,mul_add] at h
  apply h.trans
  have hr : (K:ℝ)*(S.card*((((K^2:ℕ):ℝ))⁻¹/Real.pi^2+(K:ℝ)⁻¹^2/2)) =
      (S.card:ℝ)/K*(1/Real.pi^2+1/2) := by push_cast; field_simp
  rw [hr,← mul_div_assoc]
  exact add_le_add (le_refl _) (div_le_div_of_nonneg_right hsum (by positivity))

/-- The exponential sum over every initial interval contained in the first octant. -/
theorem norm_circleArc_exponential_sum_le {x A : ℝ} (hx : 0 < x) (hA : 0 < A)
    {N : ℕ} (hN : 1 ≤ N) (hNx : (N:ℝ) ≤ √(x/2)) :
    ‖∑ n ∈ Icc 1 N, e (A*√(x-(n:ℝ)^2))‖ ≤ 180*√(√x)*(√A+1/√A) := by
  let r := √x
  let f (t : ℝ) := A*√(x-t^2)
  let d (t : ℝ) := -A*t/√(x-t^2)
  let j (t : ℝ) := -A*x/(√(x-t^2))^3
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have ht2 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) N) : t^2 ≤ x/2 :=
    (pow_le_pow_left₀ ht.1 (ht.2.trans hNx) 2).trans_eq (Real.sq_sqrt (by positivity))
  have harg {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) N) : 0 < x-t^2 := by linarith [ht2 ht]
  have hf {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) N) : HasDerivAt f (d t) t := by
    apply ((circleArc_hasDerivAt (sub_pos.mp (harg ht))).const_mul A).congr_deriv
    dsimp only [d,circleArc]; ring
  have hd {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) N) : HasDerivAt d (j t) t := by
    convert (circleArc_deriv_hasDerivAt (sub_pos.mp (harg ht))).const_mul A using 1
    · funext u; dsimp only [d,circleArc]; ring
    · dsimp only [j,circleArc]; ring
  have hj : ContinuousOn j (Set.Icc (0:ℝ) N) :=
    (show ContinuousOn (fun _ : ℝ => -A*x) _ from continuousOn_const).div
      (show ContinuousOn (fun t : ℝ => (√(x-t^2))^3) _ from
        ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn.pow 3))
      (fun t ht => pow_ne_zero 3 (Real.sqrt_pos.mpr (harg ht)).ne')
  have bounds (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) N) : A/r ≤ |j t| ∧ |j t| ≤ 8*(A/r) := by
    let s := √(x-t^2)
    have hs : 0 < s := Real.sqrt_pos.mpr (harg ht)
    have hs2 : s^2 = x-t^2 := Real.sq_sqrt (harg ht).le
    have hsr : s ≤ r := Real.sqrt_le_sqrt (by linarith [sq_nonneg t])
    have hrs : r ≤ 2*s := by nlinarith [ht2 ht,hr2,hs2,sq_nonneg (r-2*s)]
    have hlow := pow_le_pow_left₀ hs.le hsr 3
    have hupp := pow_le_pow_left₀ hr.le hrs 3
    have h₁ : s^3 ≤ x*r := hlow.trans_eq (by rw [← hr2]; ring)
    have h₂ : x*r ≤ 8*s^3 := by calc x*r = r^3 := by rw [← hr2]; ring
                                     _ ≤ _ := hupp.trans_eq (by ring)
    change A/r ≤ |-A*x/s^3| ∧ |-A*x/s^3| ≤ 8*(A/r)
    rw [abs_of_neg (by exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hA) hx) (pow_pos hs 3))]
    rw [show -(-A*x/s^3) = A*x/s^3 by ring]
    constructor
    · exact (div_le_div_iff₀ hr (pow_pos hs 3)).mpr (by linear_combination A*h₁)
    · rw [← mul_div_assoc]
      exact (div_le_div_iff₀ (pow_pos hs 3) hr).mpr (by linear_combination A*h₂)
  have H := vanDerCorput_second_deriv (a := 0) (b := N) hN (div_pos hA hr) (by norm_num : (1:ℝ)≤8)
    (fun t ht => hf (by simpa using ht)) (fun t ht => hd (by simpa using ht)) (by simpa using hj)
    (fun t ht => bounds t (by simpa using ht))
  rw [← Finset.Icc_add_one_left_eq_Ioc,zero_add] at H
  simp only [Nat.cast_zero,sub_zero,Real.rpow_neg (div_pos hA hr).le,← Real.sqrt_eq_rpow] at H
  change ‖∑ n ∈ Icc 1 N, e (A*√(x-(n:ℝ)^2))‖ ≤ _ at H
  have hNr : (N:ℝ) ≤ r := hNx.trans (Real.sqrt_le_sqrt (by linarith))
  have hs := Real.sq_sqrt hr.le
  rw [Real.sqrt_div hA.le] at H
  apply H.trans
  rw [show (20:ℝ)*8+20=180 by norm_num]
  have hb : (N:ℝ)*(√A/√r) ≤ √r*√A := by
    apply (mul_le_mul_of_nonneg_right hNr (by positivity : 0 ≤ √A/√r)).trans_eq
    field_simp [(Real.sqrt_pos.mpr hr).ne']; nlinarith only [hs,congrArg (fun y : ℝ => √A*y) hs]
  rw [inv_div]
  calc 180*((N:ℝ)*(√A/√r)+√r/√A) ≤ 180*(√r*√A+√r/√A) := by gcongr
       _ = _ := by dsimp only [r]; ring

/-- The sawtooth sum over the first octant of a circle is uniformly `O(x^(1/3))`.
Here `x` is the squared radius. -/
theorem abs_circleArc_sawtooth_le_cubeRoot : ∃ C > (0:ℝ), ∀ {x : ℝ}, 2 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊Real.sqrt (x/2)⌋₊, sawtooth (Real.sqrt (x-(n:ℝ)^2))| ≤ C*x^(1/3:ℝ) := by
  let A := (1/Real.pi^2+1/2) + (180*((4*Real.pi+4)*2+6*Real.pi))/(2*Real.pi^2)
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro x hx
  let N := ⌊√(x/2)⌋₊
  let S := Finset.Icc 1 N
  let v := x^(1/6:ℝ)
  let q := x^(1/3:ℝ)
  let W := √(√x)
  let K := ⌈v⌉₊+1
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hv : 1 ≤ v := Real.one_le_rpow hx1 (by norm_num)
  have hq : 0 ≤ q := Real.rpow_nonneg hx0.le _
  have hv0 : 0 ≤ v := by linarith
  have hK : 2 ≤ K := by
    have h := Nat.one_le_ceil_iff.mpr (by linarith : 0 < v)
    dsimp [K]; omega
  have hK0 : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hvK : v ≤ (K:ℝ) := by dsimp [K]; push_cast; linarith [Nat.le_ceil v]
  have hKv : (K:ℝ) ≤ 4*v := by dsimp [K]; push_cast; linarith [Nat.ceil_lt_add_one hv0]
  have hsK : √(K:ℝ) ≤ 2*√v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hK0.le,mul_pow,Real.sq_sqrt hv0]
    linarith
  have hN : 1 ≤ N := Nat.le_floor (by push_cast; apply (Real.le_sqrt (by norm_num) (by positivity)).mpr; linarith)
  have hNx : (N:ℝ) ≤ √(x/2) := Nat.floor_le (Real.sqrt_nonneg _)
  have hNr : (N:ℝ) ≤ √x := hNx.trans (Real.sqrt_le_sqrt (by linarith))
  have hW : W = x^(1/4:ℝ) := by dsimp [W]; rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx0.le]; norm_num
  have hWv : W*√v = q := by
    rw [hW]; dsimp [v,q]; rw [Real.sqrt_eq_rpow,← Real.rpow_mul hx0.le,← Real.rpow_add hx0]; norm_num
  have hWq : W ≤ q := by rw [hW]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hWK : W*√K ≤ 2*q := by
    rw [← hWv]; nlinarith only [mul_le_mul_of_nonneg_left hsK (show 0 ≤ W by dsimp [W]; positivity)]
  have hqv : q*v = √x := by dsimp [q,v]; rw [← Real.rpow_add hx0,Real.sqrt_eq_rpow]; norm_num
  have hlen : (N:ℝ)/K ≤ q := (div_le_iff₀ hK0).mpr (hNr.trans (hqv ▸ mul_le_mul_of_nonneg_left hvK hq))
  have h := abs_sum_sawtooth_of_sqrt_frequency S (fun n : ℕ => √(x-(n:ℝ)^2))
    (C := 180*W) (by dsimp [W]; positivity) hK (fun n hn =>
      norm_circleArc_exponential_sum_le hx0 (by exact_mod_cast hn) hN hNx)
  have hcard : S.card = N := by simp [S,Nat.card_Icc]
  rw [hcard] at h
  apply h.trans
  let c := 4*Real.pi+4
  let d := 6*Real.pi
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hnum : 180*W*((4*Real.pi+4)*√K)+180*W*(6*Real.pi) ≤ 180*(c*2+d)*q := by
    have h₁ := mul_le_mul_of_nonneg_left hWK hc
    have h₂ := mul_le_mul_of_nonneg_left hWq hd
    change 180*W*(c*√K)+180*W*d ≤ _
    linarith only [h₁,h₂]
  exact (add_le_add (mul_le_mul_of_nonneg_right hlen (by positivity)) (div_le_div_of_nonneg_right hnum (by positivity))).trans_eq
    (by dsimp [A,c,d]; ring)

end AnalyticNumberTheory.DivisorProblems
