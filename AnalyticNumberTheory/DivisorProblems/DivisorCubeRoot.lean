import AnalyticNumberTheory.DivisorProblems.DyadicDivisorEstimates

/-!
# The cube-root bound in the divisor problem

The low-frequency sum of reciprocal square roots grows at most as `2 √K`.
The high-frequency sum of inverse three-halves powers has tail at most `2 / √K`.
These estimates control the two parts of the Fourier weight in the reciprocal-phase
bound. Choosing the smoothing scale in each dyadic block gives an error at most
`700 x^(1/3)` per block. Summing the blocks proves `Δ(x) = O(x^(1/3) log x)`.
-/

noncomputable section
open Finset
namespace AnalyticNumberTheory.DivisorProblems

theorem sum_Icc_inv_sqrt_le (K : ℕ) :
    ∑ n ∈ Icc 1 K, (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * Real.sqrt K := by
  rw [show Icc 1 K = Ioc 0 K by rw [← Icc_add_one_left_eq_Ioc, zero_add]]
  induction K with
  | zero => simp
  | succ k ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _)]
    have hs : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hstep : (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt k) := by
      rw [← one_div, div_le_iff₀ hs]
      have hnew := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))
      have hold := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      push_cast at *
      nlinarith only [hnew, hold, sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k)]
    linarith only [ih, hstep]

theorem sum_Ioc_inv_mul_sqrt_le {K H : ℕ} (hK : 1 ≤ K) (hKH : K ≤ H) :
    ∑ n ∈ Ioc K H, 1 / ((n : ℝ) * Real.sqrt n) ≤ 2 / Real.sqrt K - 2 / Real.sqrt H := by
  induction H, hKH using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_Ioc_succ_top hm]
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (hK.trans hm)
    let a := Real.sqrt ((m + 1 : ℕ) : ℝ)
    let b := Real.sqrt (m : ℝ)
    have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
    have hb : 0 < b := Real.sqrt_pos.2 hm'
    have hab : b ≤ a := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
    have ha2 : a ^ 2 = ((m + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (m : ℝ) := Real.sq_sqrt hm'.le
    have hstep : 1 / (((m + 1 : ℕ) : ℝ) * a) ≤ 2 / b - 2 / a := by
      rw [← ha2]
      have hdiff : (a - b) * (a + b) = 1 := by
        push_cast at ha2
        nlinarith only [ha2, hb2]
      field_simp [ha.ne', hb.ne']
      nlinarith only [show 0 ≤ (a - b) * ((a - b) * (2 * a + b)) by positivity,
        congrArg (fun r : ℝ => r * b) hdiff, sub_nonneg.mpr hab]
    change _ + 1 / (((m + 1 : ℕ) : ℝ) * a) ≤ 2 / Real.sqrt K - 2 / a
    change _ ≤ 2 / Real.sqrt K - 2 / b at ih
    linarith only [ih, hstep]

/-- The low- and high-frequency terms in the smoothed second derivative estimate.
The bound is uniform in the upper Fourier cutoff once `H ≥ K`. -/
theorem sum_smoothed_frequencies_le {K H : ℕ} (hK : 1 ≤ K) (hKH : K ≤ H)
    {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ n ∈ Icc 1 H, (K : ℝ) * min 2 (2 * Real.pi * n / K) *
      (U * Real.sqrt n + V / Real.sqrt n) / (n : ℝ) ^ 2) ≤
      U * ((4 * Real.pi + 4) * Real.sqrt K) + V * (6 * Real.pi) := by
  let w (n : ℕ) := (K : ℝ) * min 2 (2 * Real.pi * n / K)
  let f (n : ℕ) := w n * Real.sqrt n / (n : ℝ) ^ 2
  let g (n : ℕ) := w n / Real.sqrt n / (n : ℝ) ^ 2
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hw (n : ℕ) : w n ≤ 2 * Real.pi * n := by
    calc w n ≤ K * (2 * Real.pi * n / K) := mul_le_mul_of_nonneg_left (min_le_right ..) hKpos.le
         _ = _ := by field_simp
  have hfsmall (n : ℕ) (hn : 1 ≤ n) : f n ≤ 2 * Real.pi * (Real.sqrt n)⁻¹ := by
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hs := Real.sq_sqrt hn0.le
    calc f n ≤ (2 * Real.pi * n) * Real.sqrt n / (n : ℝ) ^ 2 := by
           dsimp only [f]; gcongr; exact hw n
         _ = _ := by field_simp; exact hs
  have hflarge (n : ℕ) (hn : 1 ≤ n) : f n ≤ (2 * K) * (1 / ((n : ℝ) * Real.sqrt n)) := by
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hs := Real.sq_sqrt hn0.le
    calc f n ≤ ((K : ℝ) * 2) * Real.sqrt n / (n : ℝ) ^ 2 := by
           dsimp only [f, w]; gcongr; exact min_le_left ..
         _ = _ := by field_simp; exact hs
  have hg (n : ℕ) (hn : 1 ≤ n) : g n ≤ (2 * Real.pi) * (1 / ((n : ℝ) * Real.sqrt n)) := by
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    calc g n ≤ (2 * Real.pi * n) / Real.sqrt n / (n : ℝ) ^ 2 := by
           dsimp only [g]; gcongr; exact hw n
         _ = _ := by field_simp
  have hsplit : (∑ n ∈ Icc 1 K, f n) + ∑ n ∈ Ioc K H, f n = ∑ n ∈ Icc 1 H, f n := by
    simpa only [← Icc_add_one_left_eq_Ioc, zero_add] using sum_Ioc_consecutive f (Nat.zero_le K) hKH
  have hf1 : (∑ n ∈ Icc 1 K, f n) ≤ 2 * Real.pi * (2 * Real.sqrt K) := by
    calc _ ≤ ∑ n ∈ Icc 1 K, 2 * Real.pi * (Real.sqrt n)⁻¹ :=
           sum_le_sum fun n hn => hfsmall n (mem_Icc.mp hn).1
         _ ≤ _ := by rw [← mul_sum]; gcongr; exact sum_Icc_inv_sqrt_le K
  have hf2 : (∑ n ∈ Ioc K H, f n) ≤ 4 * Real.sqrt K := by
    calc _ ≤ ∑ n ∈ Ioc K H, (2 * K : ℝ) * (1 / ((n : ℝ) * Real.sqrt n)) :=
           sum_le_sum fun n hn => hflarge n (hK.trans (mem_Ioc.mp hn).1.le)
         _ ≤ (2 * K : ℝ) * (2 / Real.sqrt K) := by
           rw [← mul_sum]
           gcongr
           exact (sum_Ioc_inv_mul_sqrt_le hK hKH).trans (sub_le_self _ (by positivity))
         _ = _ := by field_simp; nlinarith only [Real.sq_sqrt hKpos.le]
  have hf : ∑ n ∈ Icc 1 H, f n ≤ (4 * Real.pi + 4) * Real.sqrt K := by
    rw [← hsplit]
    linarith only [hf1, hf2]
  have hg' : ∑ n ∈ Icc 1 H, g n ≤ 6 * Real.pi := by
    calc _ ≤ ∑ n ∈ Icc 1 H, 2 * Real.pi * (1 / ((n : ℝ) * Real.sqrt n)) :=
           sum_le_sum fun n hn => hg n (mem_Icc.mp hn).1
         _ ≤ (2 * Real.pi) * 3 := by
           rw [← mul_sum]
           gcongr
           rw [← add_sum_Ioc_eq_sum_Icc (hK.trans hKH)]
           have htail := sum_Ioc_inv_mul_sqrt_le (K := 1) le_rfl (hK.trans hKH)
           norm_num at htail ⊢
           linarith only [htail, show (0 : ℝ) ≤ 2 / Real.sqrt H by positivity]
         _ = _ := by ring
  calc _ = U * (∑ n ∈ Icc 1 H, f n) + V * ∑ n ∈ Icc 1 H, g n := by
         rw [mul_sum, mul_sum, ← sum_add_distrib]
         exact sum_congr rfl fun n _ => by dsimp [f, g, w]; ring
       _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hf hU) (mul_le_mul_of_nonneg_left hg' hV)

/-- Smooth at scale `1/K` and truncate the Fourier series at `K²`. The two terms in the
square brackets come respectively from the two terms of the second derivative estimate. -/
theorem abs_sum_reciprocal_sawtooth_le_sqrt_frequency {x : ℝ} (hx : 0 < x) {D a b K : ℕ}
    (hD : 0 < D) (hDa : D ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * D) (hK : 2 ≤ K) :
    let r := Real.sqrt (x / (4 * (D : ℝ) ^ 3))
    |∑ n ∈ Ioc a b, AnalyticTools.Summation.sawtooth (x / n)| ≤
      ((b : ℝ) - a) / K * (1 / Real.pi ^ 2 + 1 / 2) +
        (180 / (2 * Real.pi ^ 2)) *
        ((((b : ℝ) - a) * r) * ((4 * Real.pi + 4) * Real.sqrt K) + r⁻¹ * (6 * Real.pi)) := by
  dsimp only
  let r := Real.sqrt (x / (4 * (D : ℝ) ^ 3))
  have hK' : (1 : ℝ) < K := by exact_mod_cast hK
  have hK0 := zero_lt_one.trans hK'
  have h := abs_sum_reciprocal_sawtooth_dyadic_le hx (inv_pos.mpr hK0)
    (inv_lt_one_of_one_lt₀ hK') hD hDa hab hb (H := K ^ 2) (by nlinarith)
  have hr : 0 < r := by dsimp [r]; positivity
  let U := ((b : ℝ) - a) * r
  let V := r⁻¹
  have hweights := sum_smoothed_frequencies_le (K := K) (H := K ^ 2)
    (by omega) (by nlinarith) (show 0 ≤ U from mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hab)) hr.le)
    (show 0 ≤ V from inv_nonneg.mpr hr.le)
  let w (n : ℕ) := min 2 (2 * Real.pi * n / K)
  have hterm (n : ℕ) :
      K * (min 2 (2 * Real.pi * n * (K : ℝ)⁻¹) * (180 * (((b : ℝ) - a) *
        Real.sqrt (n * x / (4 * (D : ℝ) ^ 3)) + (Real.sqrt (n * x / (4 * (D : ℝ) ^ 3)))⁻¹)) /
          (n : ℝ) ^ 2) =
      180 * (K * w n * (U * Real.sqrt n + V / Real.sqrt n) / (n : ℝ) ^ 2) := by
    rw [mul_div_assoc (n : ℝ) x, Real.sqrt_mul (Nat.cast_nonneg _)]
    dsimp [w, U, V, r, div_eq_mul_inv]
    rw [mul_inv_rev]
    ring
  have hcount : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  have hscale : (K : ℝ) * ((↑(K ^ 2 : ℕ) : ℝ)⁻¹ / Real.pi ^ 2 + (K : ℝ)⁻¹ ^ 2 / 2) =
      (1 / Real.pi ^ 2 + 1 / 2) / K := by push_cast; field_simp
  calc _ = K * ((K : ℝ)⁻¹ * |∑ n ∈ Ioc a b, AnalyticTools.Summation.sawtooth (x / n)|) := by
         field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_left h hK0.le
       _ = ((b : ℝ) - a) / K * (1 / Real.pi ^ 2 + 1 / 2) +
            180 * (∑ n ∈ Icc 1 (K ^ 2), K * w n * (U * Real.sqrt n + V / Real.sqrt n) / (n : ℝ) ^ 2) /
              (2 * Real.pi ^ 2) := by
         rw [mul_add, hcount, mul_left_comm (K : ℝ), hscale]
         congr 1
         · ring
         · rw [← mul_div_assoc, mul_sum, sum_congr rfl (fun n _ => hterm n), ← mul_sum]
       _ ≤ _ := by
         have hc := mul_le_mul_of_nonneg_left hweights (by norm_num : (0 : ℝ) ≤ 180)
         have hd := div_le_div_of_nonneg_right hc (by positivity : 0 ≤ 2 * Real.pi ^ 2)
         rw [div_mul_eq_mul_div (180 : ℝ)]
         exact add_le_add le_rfl hd

/-- Each dyadic block below `√x` contributes `O(x^(1/3))` to the divisor sawtooth sum.
The variable `y` denotes the positive cube root of `x`. -/
theorem abs_sum_reciprocal_sawtooth_le_cubeRoot {x y : ℝ} (hy : 1 ≤ y) (hyx : y ^ 3 = x)
    {D a b : ℕ} (hD : 0 < D) (hDa : D ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * D) (hDsq : (D : ℝ) ^ 2 ≤ x) :
    |∑ n ∈ Ioc a b, AnalyticTools.Summation.sawtooth (x / n)| ≤ 700 * y := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hx : 0 < x := hyx ▸ pow_pos hy0 _
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hlen : (b : ℝ) - a ≤ D := by
    apply sub_le_iff_le_add.mpr
    exact_mod_cast (by omega : b ≤ D + a)
  by_cases hsmall : (D : ℝ) ≤ y
  · calc _ ≤ ∑ _n ∈ Ioc a b, (1 / 2 : ℝ) :=
           (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => AnalyticTools.Summation.sawtooth_abs_le _)
         _ = ((b : ℝ) - a) * (1 / 2) := by simp [Nat.cast_sub hab]
         _ ≤ _ := by linarith only [hlen, hsmall, hy]
  let K := ⌈2 * (D : ℝ) / y⌉₊
  have hKlow : 2 * (D : ℝ) ≤ K * y := (div_le_iff₀ hy0).mp (Nat.le_ceil _)
  have hK : 2 ≤ K := by
    apply (Nat.add_one_le_ceil_iff (n := 1)).mpr
    rw [lt_div_iff₀ hy0]
    push_cast
    linarith
  have hKhigh : (K : ℝ) * y ≤ 3 * D := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (D : ℝ) / y)
    have hh := mul_lt_mul_of_pos_right hceil hy0
    rw [add_mul, div_mul_cancel₀ _ hy0.ne', one_mul] at hh
    change (⌈2 * (D : ℝ) / y⌉₊ : ℝ) * y ≤ 3 * D
    linarith
  let r := Real.sqrt (x / (4 * (D : ℝ) ^ 3))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsq : r ^ 2 = x / (4 * (D : ℝ) ^ 3) := Real.sq_sqrt (by positivity)
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hfirst : ((b : ℝ) - a) * r * Real.sqrt K ≤ y := by
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlen hr.le) (Real.sqrt_nonneg _))
    apply (sq_le_sq₀ (by positivity) hy0.le).mp
    rw [mul_pow, mul_pow, hrsq, Real.sq_sqrt hK0.le]
    have hKx : (K : ℝ) * x ≤ 3 * D * y ^ 2 := by
      rw [← hyx]
      calc (K : ℝ) * y ^ 3 = (K * y) * y ^ 2 := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_right hKhigh (sq_nonneg _)
    calc _ = K * x / (4 * D) := by field_simp
         _ ≤ y ^ 2 := by
           apply (div_le_iff₀ (by positivity : 0 < 4 * (D : ℝ))).2
           nlinarith only [hKx, mul_nonneg hD0.le (sq_nonneg y)]
  have hDle : (D : ℝ) ≤ y ^ 2 := by
    apply (sq_le_sq₀ hD0.le (sq_nonneg y)).mp
    rw [← hyx] at hDsq
    nlinarith only [hDsq, mul_nonneg (pow_nonneg hy0.le 3) (sub_nonneg.mpr hy)]
  have hsecond : r⁻¹ ≤ 2 * y := by
    apply (sq_le_sq₀ (inv_nonneg.mpr hr.le) (by positivity)).mp
    rw [inv_pow, hrsq, inv_div]
    apply (div_le_iff₀ hx).2
    have h := mul_le_mul hDsq hDle hD0.le hx.le
    rw [← hyx] at h ⊢
    nlinarith only [h]
  have hfrac : ((b : ℝ) - a) / K ≤ y := (div_le_iff₀ hK0).mpr (by linarith only [hlen, hKlow, hD0])
  have hpi : 180 / (2 * Real.pi ^ 2) ≤ 10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have hone : 1 / Real.pi ^ 2 + 1 / 2 ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show 1 ≤ Real.pi ^ 2 by nlinarith [Real.pi_gt_three])
    linarith
  have hbound := abs_sum_reciprocal_sawtooth_le_sqrt_frequency hx hD hDa hab hb hK
  apply hbound.trans
  change _ + _ * (((b : ℝ) - a) * r * ((4 * Real.pi + 4) * Real.sqrt K) + r⁻¹ * (6 * Real.pi)) ≤ _
  rw [mul_comm (4 * Real.pi + 4) (Real.sqrt K), ← mul_assoc]
  have hlen0 : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (Nat.cast_le.mpr hab)
  calc _ ≤ y * 2 + 10 * (y * 20 + (2 * y) * 24) := by
         gcongr <;> linarith only [Real.pi_lt_four]
       _ ≤ _ := by linarith only [hy]

/-- Van der Corput's cube-root bound for the divisor error, with an explicit constant.
The logarithmic factor counts dyadic blocks up to the square-root cutoff. -/
theorem abs_divisorError_le_cubeRoot_mul_log {x : ℝ} (hx : 2 ≤ x) :
    |divisorError x| ≤ (2810 / Real.log 2) * (x ^ (1 / 3 : ℝ) * Real.log x) := by
  let y := x ^ (1 / 3 : ℝ)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hyx : y ^ 3 = x := by
    dsimp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  let N := ⌊Real.sqrt x⌋₊
  have hN : 1 ≤ N := Nat.floor_pos.mpr (Real.one_le_sqrt.mpr hx1)
  have hNx : (N : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg _)
  let K := N.log2 + 1
  have hbound := abs_divisorError_le_dyadic_sawtooth hx1 (K := K) (Nat.lt_log2_self.le)
  have hblock (j : ℕ) :
      |∑ n ∈ dyadicBlock N j, AnalyticTools.Summation.sawtooth (x / n)| ≤ 700 * y := by
    let D : ℕ := 2 ^ j
    let b := min N (2 ^ (j + 1))
    change |∑ n ∈ Ioc D b, _| ≤ _
    by_cases hDb : D ≤ b
    · have hDN : D ≤ N := hDb.trans (min_le_left ..)
      have hs : (D : ℝ) ≤ Real.sqrt x := (Nat.cast_le.mpr hDN).trans hNx
      apply abs_sum_reciprocal_sawtooth_le_cubeRoot hy hyx (pow_pos (by decide) _) le_rfl hDb
      · simpa only [b, D, pow_succ, Nat.mul_comm] using (min_le_right N (2 ^ (j + 1)))
      · exact (pow_le_pow_left₀ (Nat.cast_nonneg D) hs 2).trans_eq (Real.sq_sqrt hx0.le)
    · simp [Ioc_eq_empty_of_le (Nat.le_of_not_ge hDb), show 0 ≤ y by linarith]
  have hblocks := sum_le_sum (s := range K) (fun j _ => hblock j)
  rw [sum_const, card_range, nsmul_eq_mul] at hblocks
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let t := Real.log x / Real.log 2
  have ht : 1 ≤ t := (one_le_div hlog2).mpr (Real.log_le_log (by norm_num) hx)
  have hKt : (K : ℝ) ≤ 2 * t := by
    have hpow := Nat.log2_self_le (n := N) (by omega)
    have hlt : (2 : ℝ) ^ N.log2 ≤ (N : ℝ) := by exact_mod_cast hpow
    have hsx : Real.sqrt x ≤ x := by
      nlinarith only [Real.one_le_sqrt.mpr hx1, Real.sq_sqrt hx0.le,
        mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr (Real.one_le_sqrt.mpr hx1))]
    have hlog := Real.log_le_log (by positivity) (hlt.trans (hNx.trans hsx))
    rw [Real.log_pow] at hlog
    have hlt' : (N.log2 : ℝ) ≤ t := (le_div_iff₀ hlog2).mpr hlog
    dsimp [K]
    push_cast
    linarith only [ht, hlt']
  calc |divisorError x| ≤ 9 + 2 * (K * (700 * y)) :=
         hbound.trans (by gcongr)
       _ ≤ 9 + 2 * ((2 * t) * (700 * y)) := by gcongr
       _ ≤ 2810 * (y * t) := by
         nlinarith only [one_le_mul_of_one_le_of_one_le hy ht]
       _ = _ := by dsimp [y, t]; ring

/-- The divisor error is `O(x^(1/3) log x)` as `x → +∞`. -/
theorem divisorError_isBigO_cubeRoot_mul_log :
    divisorError =O[Filter.atTop] (fun x : ℝ => x ^ (1 / 3 : ℝ) * Real.log x) := by
  refine Asymptotics.IsBigO.of_bound (2810 / Real.log 2) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.log_nonneg (by linarith)))]
  exact abs_divisorError_le_cubeRoot_mul_log hx

end AnalyticNumberTheory.DivisorProblems
