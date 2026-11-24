import AnalyticNumberTheory.ModularAndPartitions.Partitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Minor arcs of the partition generating function

For each two consecutive powers, the triangle inequality forces one of their
Euler denominators to be at least half the distance from the nome to one.
The first four pairs give a fourth-power saving relative to the radial product.
-/

open Finset Filter Real MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.ModularAndPartitions

private noncomputable def factorRatio (z : ℂ) (j : ℕ) : ℝ :=
  (1 - ‖z‖^j) / ‖1-z^j‖

private lemma factorRatio_nonneg {z : ℂ} (hz : ‖z‖ < 1) (j : ℕ) :
    0 ≤ factorRatio z j :=
  div_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) hz.le)) (norm_nonneg _)

private lemma factorRatio_le_one {z : ℂ} (hz : ‖z‖ < 1) {j : ℕ} (hj : j ≠ 0) :
    factorRatio z j ≤ 1 := by
  have hd : 0 < 1-‖z‖^j := sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) hz hj)
  have h := norm_sub_norm_le (1:ℂ) (z^j)
  simp only [norm_one, norm_pow] at h
  exact (div_le_one (hd.trans_le h)).mpr h

/-- Any initial block of Euler factors bounds the loss of modulus relative to
the radial partition product. -/
theorem norm_partitionGenFun_le_prod_ratios {z : ℂ} (hz : ‖z‖ < 1) (M : ℕ) :
    ‖partitionGenFun z‖ ≤ partitionGenFunReal ‖z‖ *
      ∏ j ∈ range M, ((1-‖z‖^(j+1)) / ‖1-z^(j+1)‖) := by
  have hm := multipliable_one_sub_pow_real (by simpa using hz : |‖z‖| < 1)
  have hh := (partitionGenFun_eq_tprod_inv hz).norm.mul hm.hasProd
  have hlim : Tendsto (fun N : ℕ => ∏ j ∈ range N, factorRatio z (j+1)) atTop
      (𝓝 (‖partitionGenFun z‖ / partitionGenFunReal ‖z‖)) := by
    simpa only [factorRatio, partitionGenFunReal, div_inv_eq_mul, norm_inv, div_eq_mul_inv,
      inv_inv, mul_comm] using hh.tendsto_prod_nat
  have hle : ‖partitionGenFun z‖ / partitionGenFunReal ‖z‖ ≤ ∏ j ∈ range M, factorRatio z (j+1) := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop M] with N hN
    obtain ⟨L,rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [prod_range_add]
    apply mul_le_of_le_one_right (prod_nonneg fun _ _ => factorRatio_nonneg hz _)
    apply prod_le_one₀ (fun _ _ => factorRatio_nonneg hz _) (fun _ _ => factorRatio_le_one hz (Nat.succ_ne_zero _))
  exact (div_le_iff₀ (partitionGenFunReal_pos (norm_nonneg z) hz)).mp hle |>.trans_eq (mul_comm _ _)

private theorem one_sub_pow_norm_le {z : ℂ} (hz : ‖z‖ < 1) (j : ℕ) :
    1-‖z‖^j ≤ j*(1-‖z‖) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj := pow_le_one₀ (norm_nonneg z) hz.le (n := j)
    rw [pow_succ, Nat.cast_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hj) (sub_nonneg.mpr hz.le)]

private theorem factorRatio_pair {z : ℂ} (hz : ‖z‖ < 1) {j : ℕ} (hj : 0 < j) (hj8 : j+1 ≤ 8) :
    factorRatio z j * factorRatio z (j+1) ≤ 16*(1-‖z‖)/‖1-z‖ := by
  have hden (m : ℕ) (hm : m ≠ 0) : 0 < ‖1-z^m‖ := by
    have h := norm_sub_norm_le (1:ℂ) (z^m)
    simp only [norm_one, norm_pow] at h
    exact (sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) hz hm)).trans_le h
  have hd : 0 < ‖1-z‖ := by simpa using hden 1 one_ne_zero
  have hpair : ‖1-z‖ ≤ ‖1-z^j‖ + ‖1-z^(j+1)‖ := by
    calc
      _ = ‖(1-z^(j+1)) - z*(1-z^j)‖ := by rw [pow_succ]; ring_nf
      _ ≤ ‖1-z^(j+1)‖ + ‖z*(1-z^j)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; nlinarith [mul_le_of_le_one_left (norm_nonneg (1-z^j)) hz.le]
  have hsave (m : ℕ) (hm : m ≠ 0) (hm8 : m ≤ 8) (hdm : ‖1-z‖ ≤ 2*‖1-z^m‖) :
      factorRatio z m ≤ 16*(1-‖z‖)/‖1-z‖ := by
    apply (div_le_div_iff₀ (hden m hm) hd).mpr
    have hnum : 1-‖z‖^m ≤ 8*(1-‖z‖) := (one_sub_pow_norm_le hz m).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hm8) (sub_nonneg.mpr hz.le))
    calc
      _ ≤ (8*(1-‖z‖)) * (2*‖1-z^m‖) :=
        mul_le_mul hnum hdm hd.le (by positivity)
      _ = _ := by ring
  by_cases h : ‖1-z‖ ≤ 2*‖1-z^j‖
  · exact (mul_le_of_le_one_right (factorRatio_nonneg hz j) (factorRatio_le_one hz (Nat.succ_ne_zero _))).trans
      (hsave j hj.ne' (by omega) h)
  · exact (mul_le_of_le_one_left (factorRatio_nonneg hz (j+1)) (factorRatio_le_one hz hj.ne')).trans
      (hsave _ (Nat.succ_ne_zero _) hj8 (by linarith))

/-- Four consecutive pairs of Euler factors give fourth-power attenuation.
The estimate holds throughout the open unit disk. -/
theorem norm_partitionGenFun_le_four_pairs {z : ℂ} (hz : ‖z‖ < 1) :
    ‖partitionGenFun z‖ ≤ partitionGenFunReal ‖z‖ * (16*(1-‖z‖)/‖1-z‖)^4 := by
  apply (norm_partitionGenFun_le_prod_ratios hz 8).trans
  apply mul_le_mul_of_nonneg_left _ (partitionGenFunReal_pos (norm_nonneg z) hz).le
  let f := factorRatio z
  change (∏ j ∈ range 8, f (j+1)) ≤ _
  calc
    _ = (f 1 * f 2) * (f 3 * f 4) * (f 5 * f 6) * (f 7 * f 8) := by
      simp [prod_range_succ]; ring
    _ ≤ _ := by
      rw [show (16*(1-‖z‖)/‖1-z‖)^4 = (16*(1-‖z‖)/‖1-z‖)*(16*(1-‖z‖)/‖1-z‖)*
        (16*(1-‖z‖)/‖1-z‖)*(16*(1-‖z‖)/‖1-z‖) by ring]
      have h1 := factorRatio_pair hz (j := 1) (by decide) (by decide)
      have h3 := factorRatio_pair hz (j := 3) (by decide) (by decide)
      have h5 := factorRatio_pair hz (j := 5) (by decide) (by decide)
      have h7 := factorRatio_pair hz (j := 7) (by decide) (by decide)
      have hpos (i : ℕ) : 0 ≤ f i := factorRatio_nonneg hz i
      gcongr <;> exact mul_nonneg (hpos _) (hpos _)

/-- On the standard period `[-1/2,1/2]`, the radial contraction of a point
of the unit circle stays at distance at least `2|x|` from one. -/
theorem two_abs_le_norm_one_sub_nome {r x : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : |x| ≤ 1/2) :
    2*|x| ≤ ‖(1:ℂ) - (r:ℂ)*Complex.exp (2*Real.pi*x*Complex.I)‖ := by
  let w := Complex.exp (2*Real.pi*(x:ℂ)*Complex.I)
  have hw : ‖w‖ = 1 := by
    change ‖Complex.exp (2*Real.pi*(x:ℂ)*Complex.I)‖ = _
    rw [show 2*Real.pi*(x:ℂ)*Complex.I = (((2*Real.pi*x : ℝ):ℂ))*Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsin := Real.mul_abs_le_abs_sin (x := Real.pi*x) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left hx Real.pi_pos.le])
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hs : 2*|x| ≤ |Real.sin (Real.pi*x)| := by
    convert hsin using 1
    field_simp
  have hcircle : ‖1-w‖ = 2*|Real.sin (Real.pi*x)| := by
    have h := norm_one_sub_mul_cexp_sq 1 x
    simp only [Complex.ofReal_one, one_mul, sub_self, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add, mul_one] at h
    change ‖1-w‖^2 = _ at h
    nlinarith [sq_abs (Real.sin (Real.pi*x)), norm_nonneg (1-w), abs_nonneg (Real.sin (Real.pi*x))]
  have hrad : 1-r ≤ ‖1-(r:ℂ)*w‖ := by
    simpa [norm_mul, hw, Complex.norm_real, abs_of_nonneg hr] using norm_sub_norm_le (1:ℂ) ((r:ℂ)*w)
  have htri : ‖1-w‖ ≤ ‖1-(r:ℂ)*w‖ + (1-r) := by
    have he : (1:ℂ)-w = (1-(r:ℂ)*w) + ((r:ℂ)-1)*w := by ring
    rw [he]
    apply (norm_add_le _ _).trans_eq
    rw [norm_mul, hw, mul_one, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  change 2*|x| ≤ ‖1-(r:ℂ)*w‖
  linarith

/-- An `O(y²)` relative bound on the outer arcs for the nome of radius
`exp(-2πy)`. The constant and the threshold are independent of the angle. -/
theorem norm_partitionGenFun_minorArc_le {y x : ℝ} (hy : 0 < y)
    (hyx : √y ≤ |x|) (hx : |x| ≤ 1/2) :
    ‖partitionGenFun ((Real.exp (-(2*Real.pi*y)) : ℝ) * Complex.exp (2*Real.pi*x*Complex.I))‖ ≤
      ((16*Real.pi)^4 * y^2) * partitionGenFunReal (Real.exp (-(2*Real.pi*y))) := by
  let r := Real.exp (-(2*Real.pi*y))
  let z := (r:ℂ) * Complex.exp (2*Real.pi*(x:ℂ)*Complex.I)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hy])
  have hnorm : ‖z‖ = r := by
    dsimp only [z]
    rw [norm_mul, show 2*Real.pi*(x:ℂ)*Complex.I = (((2*Real.pi*x : ℝ):ℂ))*Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have ht : 1-r ≤ 2*Real.pi*y := by linarith [Real.add_one_le_exp (-(2*Real.pi*y))]
  have hlow : 2*√y ≤ ‖1-z‖ := (by gcongr : 2*√y ≤ 2*|x|).trans (two_abs_le_norm_one_sub_nome hr.le hr1.le hx)
  have hd : 0 < ‖1-z‖ := (by positivity : 0 < 2*√y).trans_le hlow
  have hs : 16*(1-r)/‖1-z‖ ≤ 16*Real.pi*√y := by
    rw [div_le_iff₀ hd]
    calc
      _ ≤ 16*(2*Real.pi*y) := by gcongr
      _ = (16*Real.pi*√y)*(2*√y) := by nlinarith [Real.sq_sqrt hy.le, congrArg (fun v => Real.pi*v) (Real.sq_sqrt hy.le)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have H := norm_partitionGenFun_le_four_pairs (z := z) (hnorm ▸ hr1)
  rw [hnorm] at H
  apply H.trans
  calc
    _ ≤ partitionGenFunReal r * (16*Real.pi*√y)^4 := by
      apply mul_le_mul_of_nonneg_left _ (partitionGenFunReal_pos hr.le hr1).le
      exact pow_le_pow_left₀ (div_nonneg (by positivity) hd.le) hs _
    _ = _ := by
      rw [mul_pow, show (√y)^4 = y^2 by rw [show (4:ℕ) = 2*2 by decide, pow_mul, Real.sq_sqrt hy.le]]
      ring

/-- The minor-arc bound in the single-exponential parametrization
`exp(-2π(y-ix))`. -/
theorem norm_partitionGenFun_exp_minorArc_le {y x : ℝ} (hy : 0 < y)
    (hyx : √y ≤ |x|) (hx : |x| ≤ 1/2) :
    ‖partitionGenFun (Complex.exp (-2*(Real.pi:ℂ)*((y:ℂ)-x*Complex.I)))‖ ≤
      ((16*Real.pi)^4 * y^2) * partitionGenFunReal (Real.exp (-2*Real.pi*y)) := by
  have he : Complex.exp (-2*(Real.pi:ℂ)*((y:ℂ)-x*Complex.I)) =
      (Real.exp (-(2*Real.pi*y)) : ℝ) * Complex.exp (2*Real.pi*x*Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  simpa only [neg_mul] using norm_partitionGenFun_minorArc_le hy hyx hx

/-- Integration over any subset of the outer arcs, against any weight of
modulus at most one, preserves the same bound since the period has length one. -/
theorem norm_setIntegral_partitionGenFun_minorArcs_le {y : ℝ} (hy : 0 < y) (E : Set ℝ)
    (hE : ∀ x ∈ E, √y ≤ |x| ∧ |x| ≤ 1/2) (w : ℝ → ℂ) (hw : ∀ x ∈ E, ‖w x‖ ≤ 1) :
    ‖∫ x in E, partitionGenFun (Complex.exp (-2*(Real.pi:ℂ)*((y:ℂ)-x*Complex.I))) * w x‖ ≤
      ((16*Real.pi)^4 * y^2) * partitionGenFunReal (Real.exp (-2*Real.pi*y)) := by
  have hsub : E ⊆ Set.Icc (-(1/2:ℝ)) (1/2) := fun x hx => abs_le.mp (hE x hx).2
  have hvol : volume.real E ≤ 1 := by
    apply (measureReal_mono (μ := volume) hsub measure_Icc_lt_top.ne).trans
    norm_num [measureReal_def, Real.volume_Icc]
  apply (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub).trans_lt measure_Icc_lt_top) (fun x hx => ?_)).trans
  · apply mul_le_of_le_one_right _ hvol
    have ht : Real.exp (-2*Real.pi*y) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hy])
    exact mul_nonneg (by positivity) (partitionGenFunReal_pos (Real.exp_pos _).le ht).le
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hw x hx)).trans
      (norm_partitionGenFun_exp_minorArc_le hy (hE x hx).1 (hE x hx).2)

end AnalyticNumberTheory.ModularAndPartitions
