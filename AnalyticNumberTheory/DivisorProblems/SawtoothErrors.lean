import Mathlib.Analysis.Real.Pi.Leibniz
import AnalyticNumberTheory.DivisorProblems.TwoSquares

/-!
# Sawtooth formulas for the divisor and circle errors

The symmetric hyperbola formula expresses the divisor error as a short sum of
the centered fractional parts of `x / d`, with an absolute remainder at most eight.
For the disk, Jacobi's character sum introduces two shifted sawtooth terms. An
estimate for the alternating Leibniz series controls the remaining contribution
and yields an absolute remainder at most fifty-five.
-/

open scoped BigOperators
open Filter Topology MeasureTheory

namespace AnalyticNumberTheory.DivisorProblems

section ExactSawtoothIdentities

open AnalyticNumberTheory.AnalyticTools.Summation

private theorem natFloor_cast_eq_intFloor {y : ℝ} (hy : 0 ≤ y) :
    (⌊y⌋₊ : ℝ) = (⌊y⌋ : ℝ) := by
  have hiff : (⌊y⌋₊ : ℤ) = ⌊y⌋ := by
    rw [eq_comm, Int.floor_eq_iff]
    constructor
    · exact_mod_cast Nat.floor_le hy
    · exact_mod_cast Nat.lt_floor_add_one y
  exact_mod_cast hiff

/-- Sawtooth decomposition of the natural-number floor for `0 ≤ y`:
`(⌊y⌋₊ : ℝ) = y - 1 / 2 - sawtooth y`. -/
theorem nat_floor_eq_sub_half_sub_sawtooth {y : ℝ} (hy : 0 ≤ y) :
    (⌊y⌋₊ : ℝ) = y - 1 / 2 - sawtooth y := by
  rw [sawtooth, Int.fract]
  have h := natFloor_cast_eq_intFloor hy
  linarith

private theorem log_one_add_sub_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - Real.log (1 + t) ∧ t - Real.log (1 + t) ≤ t ^ 2 / 2 := by
  refine ⟨?_, ?_⟩
  · have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t)
    linarith
  · let g : ℝ → ℝ := fun u => Real.log (1 + u) - (u - u ^ 2 / 2)
    have hderiv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt g (u ^ 2 / (1 + u)) u := by
      intro u hu
      have hu1 : (1 + u : ℝ) ≠ 0 := by linarith [Set.mem_Ici.mp hu]
      have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 u := (hasDerivAt_id u).const_add 1
      have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + u)) u := by
        simpa [one_div] using h1.log hu1
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 2) u u := by
        have h := (hasDerivAt_pow 2 u).div_const 2
        simpa using h
      have h3 : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - u) u := (hasDerivAt_id u).sub hsq
      convert h2.sub h3 using 1
      field_simp [hu1]
      ring
    have hmono : MonotoneOn g (Set.Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt)
        (fun u hu => by
          have hu0 : 0 ≤ u := by rw [interior_Ici] at hu; exact hu.le
          exact (hderiv u hu0).differentiableAt.differentiableWithinAt)
        (fun u hu => by
          have hu0 : 0 ≤ u := by rw [interior_Ici] at hu; exact hu.le
          rw [(hderiv u hu0).deriv]
          exact div_nonneg (sq_nonneg u) (by linarith))
    have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
    have hg := hmono h0mem ht ht
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0] at hg
    dsimp only [g] at hg
    linarith

/-- Exact sawtooth error identity for the Dirichlet divisor problem:
`|divisorError x + 2 * ∑ d ∈ Finset.Icc 1 ⌊√x⌋₊, sawtooth (x / d)| ≤ 8` for all `1 ≤ x`. -/
theorem abs_divisorError_add_two_sum_sawtooth_le {x : ℝ} (hx : 1 ≤ x) :
    |divisorError x + 2 * ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, sawtooth (x / (d : ℝ))| ≤ 8 := by
  have hx0 : 0 ≤ x := by linarith
  let u : ℝ := Real.sqrt x
  have hu1 : 1 ≤ u := Real.one_le_sqrt.mpr hx
  have hu0 : 0 < u := by linarith
  have husq : u ^ 2 = x := Real.sq_sqrt hx0
  let M : ℕ := ⌊u⌋₊
  have hM1 : 1 ≤ M := Nat.floor_pos.mpr hu1
  have hMR : (M : ℝ) ≤ u := Nat.floor_le hu0.le
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  let δ : ℝ := u - (M : ℝ)
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hMR
  have hδ1 : δ < 1 := by linarith [Nat.lt_floor_add_one u]
  have hu_eq : u = (M : ℝ) + δ := by dsimp [δ]; ring
  have hx_expand : x = (M : ℝ) ^ 2 + 2 * (M : ℝ) * δ + δ ^ 2 := by
    rw [← husq, hu_eq]; ring
  have hsum_floor :
      divisorSum x =
        2 * x * (harmonic M : ℝ) - (M : ℝ) - (M : ℝ) ^ 2 -
          2 * ∑ d ∈ Finset.Icc 1 M, sawtooth (x / (d : ℝ)) := by
    rw [divisorSum_eq_two_sum_floor_sub_sq x]
    have hfl :
        ∑ d ∈ Finset.Icc 1 M, (⌊x / (d : ℝ)⌋₊ : ℝ) =
          x * ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ - (M : ℝ) / 2 -
            ∑ d ∈ Finset.Icc 1 M, sawtooth (x / (d : ℝ)) := by
      have hterm :
          ∀ d ∈ Finset.Icc 1 M,
            (⌊x / (d : ℝ)⌋₊ : ℝ) = x * (d : ℝ)⁻¹ - 1 / 2 - sawtooth (x / (d : ℝ)) := by
        intro d hd
        have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
        rw [nat_floor_eq_sub_half_sub_sawtooth (div_nonneg hx0 hd0.le), div_eq_mul_inv]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    have hharm : ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ = (harmonic M : ℝ) := by
      simpa [M, u] using sum_inv_eq_harmonic u
    rw [hfl, hharm]
    ring
  have hharm_approx := abs_harmonic_sub_log_sub_gamma_sub_half_inv_le hM1
  let ε_H : ℝ :=
    (harmonic M : ℝ) - (Real.log (M : ℝ) + Real.eulerMascheroniConstant + 1 / (2 * (M : ℝ)))
  have hεH : |ε_H| ≤ 1 / (6 * (M : ℝ) ^ 2) := hharm_approx
  have hlog_u : Real.log u = Real.log (M : ℝ) + Real.log (1 + δ / (M : ℝ)) := by
    have harg : u = (M : ℝ) * (1 + δ / (M : ℝ)) := by
      field_simp [hMpos.ne']
      linarith
    rw [harg, Real.log_mul hMpos.ne' (by positivity)]
  have hlog_x : Real.log x = 2 * Real.log u := by
    rw [← husq, Real.log_pow]
    norm_num
  let ε_L : ℝ := δ / (M : ℝ) - Real.log (1 + δ / (M : ℝ))
  have hεL_bd := log_one_add_sub_bounds (div_nonneg hδ0 hMpos.le)
  have hεL_abs : |ε_L| ≤ (δ / (M : ℝ)) ^ 2 / 2 := by
    rw [abs_of_nonneg hεL_bd.1]
    exact hεL_bd.2
  have hcomb :
      divisorError x + 2 * ∑ d ∈ Finset.Icc 1 M, sawtooth (x / (d : ℝ)) =
        2 * x * ε_H + 2 * x * ε_L + 2 * δ - 3 * δ ^ 2 + (δ ^ 2 - 2 * δ ^ 3) / (M : ℝ) := by
    rw [divisorError, hsum_floor]
    have hharm_eq :
        (harmonic M : ℝ) = Real.log (M : ℝ) + Real.eulerMascheroniConstant + 1 / (2 * (M : ℝ)) + ε_H := by
      dsimp [ε_H]; ring
    have hlog_M : Real.log (M : ℝ) = Real.log x / 2 - δ / (M : ℝ) + ε_L := by
      dsimp [ε_L]; linarith
    rw [hharm_eq, hlog_M]
    rw [hx_expand]
    field_simp [hMpos.ne']
    ring
  rw [hcomb]
  have hx_le : x ≤ 4 * (M : ℝ) ^ 2 := by
    have hu_le : u ≤ 2 * (M : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      linarith
    rw [← husq]
    nlinarith
  have h1 : |2 * x * ε_H| ≤ 4 / 3 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    calc
      2 * x * |ε_H| ≤ 2 * (4 * (M : ℝ) ^ 2) * (1 / (6 * (M : ℝ) ^ 2)) :=
        mul_le_mul (by linarith) hεH (abs_nonneg _) (by positivity)
      _ = 4 / 3 := by
        field_simp [hMpos.ne']
        ring
  have h2 : |2 * x * ε_L| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    have hεL' : |ε_L| ≤ 1 / (2 * (M : ℝ) ^ 2) := by
      refine hεL_abs.trans ?_
      have hδsq : δ ^ 2 ≤ 1 := by nlinarith
      rw [div_pow]
      calc
        δ ^ 2 / (M : ℝ) ^ 2 / 2 = δ ^ 2 / (2 * (M : ℝ) ^ 2) := by ring
        _ ≤ 1 / (2 * (M : ℝ) ^ 2) := div_le_div_of_nonneg_right hδsq (by positivity)
    calc
      2 * x * |ε_L| ≤ 2 * (4 * (M : ℝ) ^ 2) * (1 / (2 * (M : ℝ) ^ 2)) :=
        mul_le_mul (by linarith) hεL' (abs_nonneg _) (by positivity)
      _ = 4 := by field_simp [hMpos.ne']
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith only [hδ0, hδ1, mul_nonneg hδ0 (sub_nonneg.mpr hδ1.le)]
  have h3 : |2 * δ - 3 * δ ^ 2| ≤ 1 := abs_le.mpr
    ⟨by nlinarith only [mul_nonneg (sub_nonneg.mpr hδ1.le) (show 0 ≤ 3 * δ + 1 by linarith only [hδ0])],
     by nlinarith only [sq_nonneg (3 * δ - 1)]⟩
  have h4 : |(δ ^ 2 - 2 * δ ^ 3) / (M : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hMpos]
    have hnum : |δ ^ 2 - 2 * δ ^ 3| ≤ 1 := by
      rw [show δ ^ 2 - 2 * δ ^ 3 = δ ^ 2 * (1 - 2 * δ) by ring, abs_mul,
        abs_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hδsq (abs_nonneg _)).trans
        (by rw [one_mul]; exact abs_le.mpr ⟨by linarith only [hδ1], by linarith only [hδ0]⟩)
    have hM_ge : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    exact (div_le_one hMpos).mpr (hnum.trans hM_ge)
  have ht1 :
      |(2 * x * ε_H + 2 * x * ε_L + 2 * δ - 3 * δ ^ 2) + (δ ^ 2 - 2 * δ ^ 3) / (M : ℝ)| ≤
        |2 * x * ε_H + 2 * x * ε_L + 2 * δ - 3 * δ ^ 2| + |(δ ^ 2 - 2 * δ ^ 3) / (M : ℝ)| :=
    abs_add_le _ _
  have ht2 :
      |(2 * x * ε_H + 2 * x * ε_L) + (2 * δ - 3 * δ ^ 2)| ≤
        |2 * x * ε_H + 2 * x * ε_L| + |2 * δ - 3 * δ ^ 2| :=
    abs_add_le _ _
  have ht3 : |2 * x * ε_H + 2 * x * ε_L| ≤ |2 * x * ε_H| + |2 * x * ε_L| := abs_add_le _ _
  rw [show 2 * x * ε_H + 2 * x * ε_L + 2 * δ - 3 * δ ^ 2 =
      (2 * x * ε_H + 2 * x * ε_L) + (2 * δ - 3 * δ ^ 2) by ring] at ht1 ⊢
  linarith only [ht1, ht2, ht3, h1, h2, h3, h4]

/-- Asymptotic sawtooth identity for `divisorError`: `Δ(x) = -2 * ∑_{d ≤ √x} ψ(x / d) + O(1)`. -/
theorem divisorError_add_two_sum_sawtooth_isBigO :
    (fun x => divisorError x + 2 * ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, sawtooth (x / (d : ℝ))) =O[atTop]
      (fun _ : ℝ => (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 8 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simpa [Real.norm_eq_abs] using abs_divisorError_add_two_sum_sawtooth_le hx

/-- Character sum `S₄(y) = ∑_{1 ≤ k ≤ y} χ₄(k)` expressed as `⌊y/4 + 3/4⌋₊ - ⌊y/4 + 1/4⌋₊`. -/
theorem sum_Icc_chi4_eq_floor_sub {y : ℝ} (hy : 0 ≤ y) :
    ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (ZMod.χ₄ (k : ℕ) : ℝ) =
      (⌊y / 4 + 3 / 4⌋₊ : ℝ) - (⌊y / 4 + 1 / 4⌋₊ : ℝ) := by
  have hfl3 : ⌊y / 4 + 3 / 4⌋₊ = (⌊y⌋₊ + 3) / 4 := by
    have hiff : ∀ m : ℕ, m ≤ ⌊y / 4 + 3 / 4⌋₊ ↔ m ≤ (⌊y⌋₊ + 3) / 4 := fun m => by
      rw [Nat.le_floor_iff (by linarith), Nat.le_div_iff_mul_le (by norm_num)]
      rcases eq_or_ne m 0 with rfl | hm0
      · simp; linarith
      · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
        constructor
        · intro h
          have hy_ge : ((4 * m - 3 : ℕ) : ℝ) ≤ y := by
            rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num; linarith
          have : 4 * m - 3 ≤ ⌊y⌋₊ := Nat.le_floor hy_ge
          omega
        · intro h
          have hfl : 4 * m - 3 ≤ ⌊y⌋₊ := by omega
          have hcast : ((4 * m - 3 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfl
          have hy_ge := hcast.trans (Nat.floor_le hy)
          rw [Nat.cast_sub (by omega), Nat.cast_mul] at hy_ge
          norm_num at hy_ge
          linarith
    exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)
  have hfl1 : ⌊y / 4 + 1 / 4⌋₊ = (⌊y⌋₊ + 1) / 4 := by
    have hiff : ∀ m : ℕ, m ≤ ⌊y / 4 + 1 / 4⌋₊ ↔ m ≤ (⌊y⌋₊ + 1) / 4 := fun m => by
      rw [Nat.le_floor_iff (by linarith), Nat.le_div_iff_mul_le (by norm_num)]
      rcases eq_or_ne m 0 with rfl | hm0
      · simp; linarith
      · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
        constructor
        · intro h
          have hy_ge : ((4 * m - 1 : ℕ) : ℝ) ≤ y := by
            rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num; linarith
          have : 4 * m - 1 ≤ ⌊y⌋₊ := Nat.le_floor hy_ge
          omega
        · intro h
          have hfl : 4 * m - 1 ≤ ⌊y⌋₊ := by omega
          have hcast : ((4 * m - 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfl
          have hy_ge := hcast.trans (Nat.floor_le hy)
          rw [Nat.cast_sub (by omega), Nat.cast_mul] at hy_ge
          norm_num at hy_ge
          linarith
    exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)
  rw [hfl3, hfl1]
  have hnat : ∀ N : ℕ,
      ∑ k ∈ Finset.Icc 1 N, (ZMod.χ₄ (k : ℕ) : ℤ) = ((N + 3) / 4 : ℕ) - ((N + 1) / 4 : ℕ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hsplit : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp), ih]
      have hmod : (N + 1) % 4 = 0 ∨ (N + 1) % 4 = 1 ∨ (N + 1) % 4 = 2 ∨ (N + 1) % 4 = 3 := by omega
      rcases hmod with h | h | h | h
      · have hchi : ZMod.χ₄ ((N + 1 : ℕ) : ℕ) = 0 := by
          rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show (N + 1) % 2 = 0 by omega]
        rw [hchi]; omega
      · rw [ZMod.χ₄_nat_one_mod_four h]; omega
      · have hchi : ZMod.χ₄ ((N + 1 : ℕ) : ℕ) = 0 := by
          rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show (N + 1) % 2 = 0 by omega]
        rw [hchi]; omega
      · rw [ZMod.χ₄_nat_three_mod_four h]; omega
  exact_mod_cast hnat ⌊y⌋₊

/-- Sawtooth evaluation of `S₄(y)`:
`∑_{1 ≤ k ≤ y} χ₄(k) = 1 / 2 - sawtooth (y / 4 + 3 / 4) + sawtooth (y / 4 + 1 / 4)`. -/
theorem sum_Icc_chi4_eq_sawtooth {y : ℝ} (hy : 0 ≤ y) :
    ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (ZMod.χ₄ (k : ℕ) : ℝ) =
      1 / 2 - sawtooth (y / 4 + 3 / 4) + sawtooth (y / 4 + 1 / 4) := by
  rw [sum_Icc_chi4_eq_floor_sub hy,
    nat_floor_eq_sub_half_sub_sawtooth (by linarith),
    nat_floor_eq_sub_half_sub_sawtooth (by linarith)]
  ring

private theorem sum_Icc_chi4_bounds (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (ZMod.χ₄ (k : ℕ) : ℝ)) = 0 ∨
      (∑ k ∈ Finset.Icc 1 M, (ZMod.χ₄ (k : ℕ) : ℝ)) = 1 := by
  have hflM : ⌊(M : ℝ)⌋₊ = M := Nat.floor_natCast M
  rw [← hflM, sum_Icc_chi4_eq_floor_sub (Nat.cast_nonneg M)]
  have h1 : ⌊(M : ℝ) / 4 + 3 / 4⌋₊ = (M + 3) / 4 := by
    have hiff : ∀ m : ℕ, m ≤ ⌊(M : ℝ) / 4 + 3 / 4⌋₊ ↔ m ≤ (M + 3) / 4 := fun m => by
      rw [Nat.le_floor_iff (by positivity), Nat.le_div_iff_mul_le (by norm_num)]
      constructor
      · intro h; have : (m * 4 : ℝ) ≤ (M : ℝ) + 3 := by linarith
        exact_mod_cast this
      · intro h; have : (m * 4 : ℝ) ≤ (M : ℝ) + 3 := by exact_mod_cast h
        linarith
    exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)
  have h2 : ⌊(M : ℝ) / 4 + 1 / 4⌋₊ = (M + 1) / 4 := by
    have hiff : ∀ m : ℕ, m ≤ ⌊(M : ℝ) / 4 + 1 / 4⌋₊ ↔ m ≤ (M + 1) / 4 := fun m => by
      rw [Nat.le_floor_iff (by positivity), Nat.le_div_iff_mul_le (by norm_num)]
      constructor
      · intro h; have : (m * 4 : ℝ) ≤ (M : ℝ) + 1 := by linarith
        exact_mod_cast this
      · intro h; have : (m * 4 : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast h
        linarith
    exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)
  rw [h1, h2]
  have hcases : (M + 3) / 4 = (M + 1) / 4 ∨ (M + 3) / 4 = (M + 1) / 4 + 1 := by omega
  rcases hcases with h | h <;> [left; right] <;> [rw [h, sub_self]; (rw [h]; push_cast; ring)]

/-- Explicit bound on the alternating Leibniz tail `π / 4 - ∑_{1 ≤ d ≤ M} χ₄(d) / d`:
for `1 ≤ M`, comparing the tail against `(1 - 2 * S₄(M)) / (2 * M)` yields `O(M⁻²)` error. -/
theorem abs_leibniz_tail_sub_inv_le {M : ℕ} (hM : 1 ≤ M) :
    |(Real.pi / 4 - ∑ d ∈ Finset.Icc 1 M, (ZMod.χ₄ (d : ℕ) : ℝ) / (d : ℝ)) -
        (1 - 2 * ∑ k ∈ Finset.Icc 1 M, (ZMod.χ₄ (k : ℕ) : ℝ)) / (2 * (M : ℝ))| ≤
      3 / (M : ℝ) ^ 2 := by
  let L : ℕ := (M + 1) / 2
  have hL1 : 1 ≤ L := by omega
  let S4 : ℝ := ∑ k ∈ Finset.Icc 1 M, (ZMod.χ₄ (k : ℕ) : ℝ)
  have hsum_eq :
      ∑ d ∈ Finset.Icc 1 M, (ZMod.χ₄ (d : ℕ) : ℝ) / (d : ℝ) =
        ∑ i ∈ Finset.range L, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) := by
    have hbij :
        Finset.sum (Finset.range L) (fun i => (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1)) =
          Finset.sum ((Finset.Icc 1 M).filter Odd) (fun d => (ZMod.χ₄ (d : ℕ) : ℝ) / (d : ℝ)) := by
      refine Finset.sum_bij (fun i _ => 2 * i + 1) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_range] at hi
        dsimp only [L] at hi
        exact ⟨⟨by omega, by omega⟩, ⟨i, rfl⟩⟩
      · intro i₁ _ i₂ _ h; omega
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        rcases hd.2 with ⟨i, rfl⟩
        dsimp only [L]
        exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      · intro i _
        have hodd : (2 * i + 1) % 2 = 1 := by omega
        have hchi : ZMod.χ₄ ((2 * i + 1 : ℕ) : ℕ) = (-1 : ℤ) ^ ((2 * i + 1) / 2) :=
          ZMod.χ₄_eq_neg_one_pow hodd
        rw [hchi]
        have hdiv : (2 * i + 1) / 2 = i := by omega
        rw [hdiv]
        push_cast
        ring
    rw [hbij]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) Odd]
    have heven0 : ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬Odd d), (ZMod.χ₄ (d : ℕ) : ℝ) / (d : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [Finset.mem_filter] at hd
      have hev : d % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hd.2)
      have hchi : ZMod.χ₄ (d : ℕ) = 0 := by rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [hev]
      rw [hchi]
      simp
    rw [heven0, add_zero]
  have hsign : (-1 : ℝ) ^ L = 1 - 2 * S4 := by
    have hS4_int : S4 = (if Odd L then 1 else 0) := by
      have hind : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, (ZMod.χ₄ (k : ℕ) : ℝ) =
          if Odd ((m + 1) / 2) then 1 else 0 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          have hsp : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsp, Finset.sum_insert (by simp), ih]
          have hm4 : (m + 1) % 4 = 0 ∨ (m + 1) % 4 = 1 ∨ (m + 1) % 4 = 2 ∨ (m + 1) % 4 = 3 := by omega
          rcases hm4 with hm4 | hm4 | hm4 | hm4
          · have hchi : ZMod.χ₄ ((m + 1 : ℕ) : ℕ) = 0 := by
              rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show (m + 1) % 2 = 0 by omega]
            have hq : ((m + 1 + 1) / 2) = (m + 1) / 2 := by omega
            rw [hchi, Int.cast_zero, zero_add, hq]
          · rw [ZMod.χ₄_nat_one_mod_four hm4]
            have ho1 : ¬Odd ((m + 1) / 2) := by rw [Nat.odd_iff]; omega
            have ho2 : Odd ((m + 1 + 1) / 2) := by rw [Nat.odd_iff]; omega
            simp [ho1, ho2]
          · have hchi : ZMod.χ₄ ((m + 1 : ℕ) : ℕ) = 0 := by
              rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show (m + 1) % 2 = 0 by omega]
            have hq : ((m + 1 + 1) / 2) = (m + 1) / 2 := by omega
            rw [hchi, Int.cast_zero, zero_add, hq]
          · rw [ZMod.χ₄_nat_three_mod_four hm4]
            have ho1 : Odd ((m + 1) / 2) := by rw [Nat.odd_iff]; omega
            have ho2 : ¬Odd ((m + 1 + 1) / 2) := by rw [Nat.odd_iff]; omega
            simp [ho1, ho2]

      exact hind M
    rw [hS4_int]
    by_cases hodd : Odd L
    · rw [ite_eq_left hodd, hodd.neg_one_pow]; norm_num
    · rw [ite_eq_right hodd, (Nat.not_odd_iff_even.mp hodd).neg_one_pow]; norm_num
  let V : ℕ → ℝ := fun K =>
    (-1 : ℝ) ^ K * (Real.pi / 4 - ∑ i ∈ Finset.range K, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1))
  have hV_step : ∀ K : ℕ, V K + V (K + 1) = 1 / (2 * (K : ℝ) + 1) := by
    intro K
    dsimp only [V]
    rw [Finset.sum_range_succ, pow_succ]
    have hpow : (-1 : ℝ) ^ K * (-1 : ℝ) ^ K = 1 := by rw [← mul_pow]; simp
    calc
      (-1 : ℝ) ^ K * (Real.pi / 4 - ∑ i ∈ Finset.range K, (-1 : ℝ) ^ i / (2 * ↑i + 1)) +
          (-1 : ℝ) ^ K * (-1) *
            (Real.pi / 4 - (∑ i ∈ Finset.range K, (-1 : ℝ) ^ i / (2 * ↑i + 1) + (-1 : ℝ) ^ K / (2 * ↑K + 1)))
          = ((-1 : ℝ) ^ K * (-1 : ℝ) ^ K) / (2 * (K : ℝ) + 1) := by ring
      _ = 1 / (2 * (K : ℝ) + 1) := by rw [hpow]
  have h2r_top : Tendsto (fun r : ℕ => 2 * r) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have h2r1_top : Tendsto (fun r : ℕ => 2 * r + 1) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hV_tendsto : ∀ K : ℕ,
      Tendsto (fun n => ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j / (2 * ((K + j : ℕ) : ℝ) + 1))
        atTop (𝓝 (V K)) := by
    intro K
    have h1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + K), (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1))
        atTop (𝓝 (Real.pi / 4)) :=
      Real.tendsto_sum_pi_div_four.comp (tendsto_add_atTop_nat K)
    have ht := (h1.sub_const (∑ i ∈ Finset.range K, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1))).const_mul
      ((-1 : ℝ) ^ K)
    refine ht.congr fun n => ?_
    rw [add_comm n K, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    have hpow : (-1 : ℝ) ^ K * (-1 : ℝ) ^ K = 1 := by rw [← mul_pow]; simp
    calc
      (-1 : ℝ) ^ K * ((-1 : ℝ) ^ K * (-1 : ℝ) ^ j / (2 * ↑(K + j) + 1))
          = ((-1 : ℝ) ^ K * (-1 : ℝ) ^ K) * (-1 : ℝ) ^ j / (2 * ↑(K + j) + 1) := by ring
      _ = (-1 : ℝ) ^ j / (2 * ↑(K + j) + 1) := by rw [hpow, one_mul]
  have hV_nonneg_and_le : ∀ K : ℕ, 0 ≤ V K ∧ V K ≤ 1 / (2 * (K : ℝ) + 1) := by
    intro K
    have hshift := hV_tendsto K
    have heven_ge : ∀ r : ℕ,
        0 ≤ ∑ j ∈ Finset.range (2 * r), (-1 : ℝ) ^ j / (2 * ((K + j : ℕ) : ℝ) + 1) := by
      intro r
      induction r with
      | zero => simp
      | succ r ihr =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        have hp0 : (-1 : ℝ) ^ (2 * r) = 1 := (even_two_mul r).neg_one_pow
        have hp1 : (-1 : ℝ) ^ (2 * r + 1) = -1 :=
          (Nat.odd_iff.mpr (by omega : (2 * r + 1) % 2 = 1)).neg_one_pow
        rw [hp0, hp1]
        have hd1 : (0 : ℝ) < 2 * ((K + 2 * r : ℕ) : ℝ) + 1 := by positivity
        have hd2 : 2 * ((K + 2 * r : ℕ) : ℝ) + 1 ≤ 2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1 := by
          push_cast; linarith
        have hdiv := one_div_le_one_div_of_le hd1 hd2
        simp only [neg_div]
        linarith
    have hodd_le : ∀ r : ℕ,
        ∑ j ∈ Finset.range (2 * r + 1), (-1 : ℝ) ^ j / (2 * ((K + j : ℕ) : ℝ) + 1) ≤
          1 / (2 * (K : ℝ) + 1) := by
      intro r
      induction r with
      | zero => simp
      | succ r ihr =>
        rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 from by ring, Finset.sum_range_succ,
          Finset.sum_range_succ]
        have hp1 : (-1 : ℝ) ^ (2 * r + 1) = -1 :=
          (Nat.odd_iff.mpr (by omega : (2 * r + 1) % 2 = 1)).neg_one_pow
        have hp2 : (-1 : ℝ) ^ (2 * r + 2) = 1 :=
          (Nat.even_iff.mpr (by omega : (2 * r + 2) % 2 = 0)).neg_one_pow
        rw [hp1, hp2]
        have hd1 : (0 : ℝ) < 2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1 := by positivity
        have hd2 : 2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1 ≤ 2 * ((K + (2 * r + 2) : ℕ) : ℝ) + 1 := by
          push_cast; linarith
        have hdiv := one_div_le_one_div_of_le hd1 hd2
        simp only [neg_div]
        linarith
    exact ⟨ge_of_tendsto (hshift.comp h2r_top) (Filter.Eventually.of_forall heven_ge),
      le_of_tendsto (hshift.comp h2r1_top) (Filter.Eventually.of_forall hodd_le)⟩
  have hV_mono : ∀ K : ℕ, V (K + 1) ≤ V K := by
    intro K
    have hV1 := hV_tendsto K
    have hV2 : Tendsto (fun n => ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j / (2 * ((K + j + 1 : ℕ) : ℝ) + 1))
        atTop (𝓝 (V (K + 1))) := by
      refine (hV_tendsto (K + 1)).congr fun n => Finset.sum_congr rfl fun j _ => ?_
      rw [show K + 1 + j = K + j + 1 from by ring]
    have hdiff_tendsto :
        Tendsto (fun n => ∑ j ∈ Finset.range n,
          (-1 : ℝ) ^ j * (1 / (2 * ((K + j : ℕ) : ℝ) + 1) - 1 / (2 * ((K + j + 1 : ℕ) : ℝ) + 1)))
          atTop (𝓝 (V K - V (K + 1))) := by
      refine (hV1.sub hV2).congr fun n => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have heven_ge : ∀ r : ℕ,
        0 ≤ ∑ j ∈ Finset.range (2 * r),
          (-1 : ℝ) ^ j * (1 / (2 * ((K + j : ℕ) : ℝ) + 1) - 1 / (2 * ((K + j + 1 : ℕ) : ℝ) + 1)) := by
      intro r
      induction r with
      | zero => simp
      | succ r ihr =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        have hp0 : (-1 : ℝ) ^ (2 * r) = 1 := (even_two_mul r).neg_one_pow
        have hp1 : (-1 : ℝ) ^ (2 * r + 1) = -1 :=
          (Nat.odd_iff.mpr (by omega : (2 * r + 1) % 2 = 1)).neg_one_pow
        rw [hp0, hp1]
        have hinc :
            2 / ((2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1) * (2 * ((K + (2 * r + 1) + 1 : ℕ) : ℝ) + 1)) ≤
              2 / ((2 * ((K + 2 * r : ℕ) : ℝ) + 1) * (2 * ((K + 2 * r + 1 : ℕ) : ℝ) + 1)) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          have h1 : 2 * ((K + 2 * r : ℕ) : ℝ) + 1 ≤ 2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1 := by
            push_cast; linarith
          have h2 : 2 * ((K + 2 * r + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((K + (2 * r + 1) + 1 : ℕ) : ℝ) + 1 := by
            push_cast; linarith
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
        have halg1 :
            1 / (2 * ((K + 2 * r : ℕ) : ℝ) + 1) - 1 / (2 * ((K + 2 * r + 1 : ℕ) : ℝ) + 1) =
              2 / ((2 * ((K + 2 * r : ℕ) : ℝ) + 1) * (2 * ((K + 2 * r + 1 : ℕ) : ℝ) + 1)) := by
          have ha : (2 * ((K + 2 * r : ℕ) : ℝ) + 1) ≠ 0 := by positivity
          have hb : (2 * ((K + 2 * r + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
          field_simp [ha, hb]; push_cast; ring
        have halg2 :
            1 / (2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1) - 1 / (2 * ((K + (2 * r + 1) + 1 : ℕ) : ℝ) + 1) =
              2 / ((2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1) * (2 * ((K + (2 * r + 1) + 1 : ℕ) : ℝ) + 1)) := by
          have ha : (2 * ((K + (2 * r + 1) : ℕ) : ℝ) + 1) ≠ 0 := by positivity
          have hb : (2 * ((K + (2 * r + 1) + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
          field_simp [ha, hb]; push_cast; ring
        rw [one_mul, halg1, neg_one_mul, halg2]
        linarith
    have hge := ge_of_tendsto (hdiff_tendsto.comp h2r_top) (Filter.Eventually.of_forall heven_ge)
    linarith
  have hV_tight :
      |V L - 1 / (2 * (2 * (L : ℝ) + 1))| ≤ 1 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3)) := by
    have h0 : 0 ≤ V L - V (L + 1) := sub_nonneg.mpr (hV_mono L)
    have h1 : 0 ≤ V (L + 1) - V (L + 2) := sub_nonneg.mpr (hV_mono (L + 1))
    have hs1 := hV_step L
    have hs2 := hV_step (L + 1)
    have hgap : V L - V (L + 2) = 2 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3)) := by
      have hcast : 2 * ((L + 1 : ℕ) : ℝ) + 1 = 2 * (L : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hs2
      have ha : (2 * (L : ℝ) + 1) ≠ 0 := by positivity
      have hb : (2 * (L : ℝ) + 3) ≠ 0 := by positivity
      calc
        V L - V (L + 2) = (V L + V (L + 1)) - (V (L + 1) + V (L + 2)) := by ring
        _ = 1 / (2 * (L : ℝ) + 1) - 1 / (2 * (L : ℝ) + 3) := by rw [hs1, hs2]
        _ = 2 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3)) := by field_simp [ha, hb]; ring
    have h2VL_lo : 0 ≤ 2 * V L - 1 / (2 * (L : ℝ) + 1) := by linarith
    have h2VL_hi : 2 * V L - 1 / (2 * (L : ℝ) + 1) ≤ 2 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3)) := by
      linarith
    have hscaled : 2 * (V L - 1 / (2 * (2 * (L : ℝ) + 1))) = 2 * V L - 1 / (2 * (L : ℝ) + 1) := by
      field_simp
    have hscaled' : 2 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3)) =
        2 * (1 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3))) := by ring
    rw [← hscaled] at h2VL_lo h2VL_hi
    rw [hscaled'] at h2VL_hi
    rw [abs_of_nonneg (by linarith only [h2VL_lo])]
    linarith only [h2VL_hi]
  have hshift_M :
      |1 / (2 * (2 * (L : ℝ) + 1)) - 1 / (2 * (M : ℝ))| ≤ 2 / (M : ℝ) ^ 2 := by
    have hML1 : (M : ℝ) ≤ 2 * (L : ℝ) + 1 := by exact_mod_cast (by omega : M ≤ 2 * L + 1)
    have hML2 : 2 * (L : ℝ) + 1 ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 2 * L + 1 ≤ M + 2)
    have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
    have h2Lpos : (0 : ℝ) < 2 * (L : ℝ) + 1 := by positivity
    have hdiff :
        1 / (2 * (M : ℝ)) - 1 / (2 * (2 * (L : ℝ) + 1)) =
          ((2 * (L : ℝ) + 1) - (M : ℝ)) / (2 * (M : ℝ) * (2 * (L : ℝ) + 1)) := by
      field_simp [hMpos.ne', h2Lpos.ne']

    have hnonneg : 0 ≤ 1 / (2 * (M : ℝ)) - 1 / (2 * (2 * (L : ℝ) + 1)) := by
      rw [hdiff]
      exact div_nonneg (by linarith) (by positivity)
    have hle : 1 / (2 * (M : ℝ)) - 1 / (2 * (2 * (L : ℝ) + 1)) ≤ 2 / (M : ℝ) ^ 2 := by
      rw [hdiff]
      have hnum : (2 * (L : ℝ) + 1) - (M : ℝ) ≤ 2 := by linarith
      have hden : 2 * (M : ℝ) ^ 2 ≤ 2 * (M : ℝ) * (2 * (L : ℝ) + 1) := by nlinarith
      calc
        ((2 * (L : ℝ) + 1) - (M : ℝ)) / (2 * (M : ℝ) * (2 * (L : ℝ) + 1))
            ≤ 2 / (2 * (M : ℝ) ^ 2) := div_le_div₀ (by norm_num) hnum (by positivity) hden
        _ ≤ 2 / (M : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    rw [abs_sub_comm, abs_of_nonneg hnonneg]
    exact hle
  have hMsq_le : 1 / ((2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 3)) ≤ 1 / (M : ℝ) ^ 2 := by
    have hML : (M : ℝ) ≤ 2 * (L : ℝ) + 1 := by exact_mod_cast (by omega : M ≤ 2 * L + 1)
    have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hV_M : |V L - 1 / (2 * (M : ℝ))| ≤ 3 / (M : ℝ) ^ 2 := by
    have htri :
        |V L - 1 / (2 * (M : ℝ))| ≤
          |V L - 1 / (2 * (2 * (L : ℝ) + 1))| + |1 / (2 * (2 * (L : ℝ) + 1)) - 1 / (2 * (M : ℝ))| :=
      abs_sub_le _ _ _
    calc _ ≤ _ := htri
         _ ≤ _ := add_le_add hV_tight hshift_M
         _ ≤ 1 / (M : ℝ) ^ 2 + 2 / (M : ℝ) ^ 2 := add_le_add_left hMsq_le _
         _ = 3 / (M : ℝ) ^ 2 := by ring
  have hmain_eq :
      (Real.pi / 4 - ∑ d ∈ Finset.Icc 1 M, (ZMod.χ₄ (d : ℕ) : ℝ) / (d : ℝ)) -
          (1 - 2 * S4) / (2 * (M : ℝ)) =
        (-1 : ℝ) ^ L * (V L - 1 / (2 * (M : ℝ))) := by
    rw [hsum_eq, ← hsign]
    have hpow : (-1 : ℝ) ^ L * (-1 : ℝ) ^ L = 1 := by rw [← mul_pow]; simp
    calc
      (Real.pi / 4 - ∑ i ∈ Finset.range L, (-1 : ℝ) ^ i / (2 * ↑i + 1)) -
          (-1 : ℝ) ^ L / (2 * ↑M)
          = ((-1 : ℝ) ^ L * (-1 : ℝ) ^ L) *
              (Real.pi / 4 - ∑ i ∈ Finset.range L, (-1 : ℝ) ^ i / (2 * ↑i + 1)) -
              (-1 : ℝ) ^ L / (2 * ↑M) := by rw [hpow, one_mul]
      _ = (-1 : ℝ) ^ L * (V L - 1 / (2 * (M : ℝ))) := by dsimp [V]; ring
  rw [hmain_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact hV_M

/-- Exact sawtooth identity for the Gauss circle error term `P(x)`:
for all `1 ≤ x`, setting `M = ⌊√x⌋₊`,
`|P(x) + 4 * (∑ d ∈ Icc 1 M, χ₄(d) * ψ(x / d) + ∑ m ∈ Icc 1 M, (ψ(x / (4 m) + 3 / 4) - ψ(x / (4 m) + 1 / 4)))| ≤ 55`. -/
theorem abs_gaussCircleError_add_four_sum_sawtooth_le {x : ℝ} (hx : 1 ≤ x) :
    |gaussCircleError x +
        4 * (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (ZMod.χ₄ (d : ℕ) : ℝ) * sawtooth (x / (d : ℝ)) +
          ∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
            (sawtooth (x / (4 * (m : ℝ)) + 3 / 4) - sawtooth (x / (4 * (m : ℝ)) + 1 / 4)))| ≤ 55 := by
  have hx0 : 0 ≤ x := by linarith
  let u : ℝ := Real.sqrt x
  have hu1 : 1 ≤ u := Real.one_le_sqrt.mpr hx
  have hu0 : 0 < u := by linarith
  have husq : u ^ 2 = x := Real.sq_sqrt hx0
  let M : ℕ := ⌊u⌋₊
  have hM1 : 1 ≤ M := Nat.floor_pos.mpr hu1
  have hMR : (M : ℝ) ≤ u := Nat.floor_le hu0.le
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  let δ : ℝ := u - (M : ℝ)
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hMR
  have hδ1 : δ < 1 := by linarith [Nat.lt_floor_add_one u]
  have hu_eq : u = (M : ℝ) + δ := by dsimp [δ]; ring
  have hx_expand : x = (M : ℝ) ^ 2 + 2 * (M : ℝ) * δ + δ ^ 2 := by
    rw [← husq, hu_eq]; ring
  let χ : ℕ → ℝ := fun d => (ZMod.χ₄ (d : ℕ) : ℝ)
  let S4 : ℝ := ∑ d ∈ Finset.Icc 1 M, χ d
  have hS4_bd : S4 = 0 ∨ S4 = 1 := sum_Icc_chi4_bounds M
  have hS4_abs : |1 - 2 * S4| ≤ 1 := by
    rcases hS4_bd with h0 | h1 <;> [rw [h0]; rw [h1]] <;> norm_num
  have hhyp := dirichlet_hyperbola_sqrt χ (fun _ => (1 : ℝ)) x
  have hconv :
      gaussCircleCount x =
        1 + 4 * ((∑ d ∈ Finset.Icc 1 M, χ d * (⌊x / (d : ℝ)⌋₊ : ℝ)) +
          (∑ m ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 ⌊x / (m : ℝ)⌋₊, χ k) -
          S4 * (M : ℝ)) := by
    rw [gaussCircleCount_eq_one_add_four_sum_chi4 hx0]
    congr 2
    have hps :
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, χ d = partialSum (LSeries.convolution χ (fun _ => (1 : ℝ))) x := by
      rw [partialSum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LSeries.convolution_def]
      symm
      simpa [mul_one] using Nat.sum_divisorsAntidiagonal (f := fun d _ => χ d * (1 : ℝ)) (n := n)
    rw [hps, hhyp]
    simp [partialSum, M, u, S4]
  have hpart1 :
      ∑ d ∈ Finset.Icc 1 M, χ d * (⌊x / (d : ℝ)⌋₊ : ℝ) =
        x * (∑ d ∈ Finset.Icc 1 M, χ d / (d : ℝ)) - S4 / 2 -
          ∑ d ∈ Finset.Icc 1 M, χ d * sawtooth (x / (d : ℝ)) := by
    have hterm :
        ∀ d ∈ Finset.Icc 1 M,
          χ d * (⌊x / (d : ℝ)⌋₊ : ℝ) =
            x * (χ d / (d : ℝ)) - χ d / 2 - χ d * sawtooth (x / (d : ℝ)) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
      rw [nat_floor_eq_sub_half_sub_sawtooth (div_nonneg hx0 hd0.le)]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_div]
  have hpart2 :
      ∑ m ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 ⌊x / (m : ℝ)⌋₊, χ k =
        (M : ℝ) / 2 -
          ∑ m ∈ Finset.Icc 1 M,
            (sawtooth (x / (4 * (m : ℝ)) + 3 / 4) - sawtooth (x / (4 * (m : ℝ)) + 1 / 4)) := by
    have hterm :
        ∀ m ∈ Finset.Icc 1 M,
          ∑ k ∈ Finset.Icc 1 ⌊x / (m : ℝ)⌋₊, χ k =
            1 / 2 - (sawtooth (x / (4 * (m : ℝ)) + 3 / 4) - sawtooth (x / (4 * (m : ℝ)) + 1 / 4)) := by
      intro m hm
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
      rw [sum_Icc_chi4_eq_sawtooth (div_nonneg hx0 hm0.le)]
      have hdiv : (x / (m : ℝ)) / 4 = x / (4 * (m : ℝ)) := by ring
      rw [hdiv]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  let tail : ℝ :=
    (Real.pi / 4 - ∑ d ∈ Finset.Icc 1 M, χ d / (d : ℝ)) - (1 - 2 * S4) / (2 * (M : ℝ))
  have htail_bd : |tail| ≤ 3 / (M : ℝ) ^ 2 := abs_leibniz_tail_sub_inv_le hM1
  have hsum_chi_inv :
      Real.pi / 4 - ∑ d ∈ Finset.Icc 1 M, χ d / (d : ℝ) = (1 - 2 * S4) / (2 * (M : ℝ)) + tail := by
    dsimp [tail]; ring
  have hcombine :
      gaussCircleError x +
          4 * (∑ d ∈ Finset.Icc 1 M, χ d * sawtooth (x / (d : ℝ)) +
            ∑ m ∈ Finset.Icc 1 M,
              (sawtooth (x / (4 * (m : ℝ)) + 3 / 4) - sawtooth (x / (4 * (m : ℝ)) + 1 / 4))) =
        1 - 2 * S4 - 4 * x * tail -
          (1 - 2 * S4) * (4 * δ + 2 * δ ^ 2 / (M : ℝ)) := by
    rw [gaussCircleError, hconv, hpart1, hpart2]
    have hpi_tail :
        ∑ d ∈ Finset.Icc 1 M, χ d / (d : ℝ) = Real.pi / 4 - (1 - 2 * S4) / (2 * (M : ℝ)) - tail := by
      linarith
    rw [hpi_tail]
    have hcancel :
        1 + 4 * (x * (Real.pi / 4 - (1 - 2 * S4) / (2 * ↑M) - tail) - S4 / 2 -
            ∑ d ∈ Finset.Icc 1 M, χ d * sawtooth (x / ↑d) +
            (↑M / 2 - ∑ m ∈ Finset.Icc 1 M,
              (sawtooth (x / (4 * ↑m) + 3 / 4) - sawtooth (x / (4 * ↑m) + 1 / 4))) -
            S4 * ↑M) - Real.pi * x +
          4 * (∑ d ∈ Finset.Icc 1 M, χ d * sawtooth (x / ↑d) +
            ∑ m ∈ Finset.Icc 1 M,
              (sawtooth (x / (4 * ↑m) + 3 / 4) - sawtooth (x / (4 * ↑m) + 1 / 4))) =
          1 - 2 * S4 - 4 * x * tail - (1 - 2 * S4) * (2 * x / (M : ℝ) - 2 * (M : ℝ)) := by
      ring
    rw [hcancel]
    have hrem : 2 * x / (M : ℝ) - 2 * (M : ℝ) = 4 * δ + 2 * δ ^ 2 / (M : ℝ) := by
      nth_rw 1 [hx_expand]
      field_simp [hMpos.ne']
      ring
    rw [hrem]
  rw [hcombine]
  have hx_le : x ≤ 4 * (M : ℝ) ^ 2 := by
    have hu_le : u ≤ 2 * (M : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      linarith
    rw [← husq]
    nlinarith
  have h1 : |4 * x * tail| ≤ 48 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    calc
      4 * x * |tail| ≤ 4 * (4 * (M : ℝ) ^ 2) * (3 / (M : ℝ) ^ 2) :=
        mul_le_mul (by linarith) htail_bd (abs_nonneg _) (by positivity)
      _ = 48 := by field_simp [hMpos.ne']; ring
  have h2 : |(1 - 2 * S4) * (4 * δ + 2 * δ ^ 2 / (M : ℝ))| ≤ 6 := by
    rw [abs_mul]
    have hlin : |4 * δ + 2 * δ ^ 2 / (M : ℝ)| ≤ 6 := by
      have hnonneg : 0 ≤ 4 * δ + 2 * δ ^ 2 / (M : ℝ) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hM_ge : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      have hdiv_le : 2 * δ ^ 2 / (M : ℝ) ≤ 2 * δ ^ 2 := div_le_self (by positivity) hM_ge
      nlinarith
    calc
      |1 - 2 * S4| * |4 * δ + 2 * δ ^ 2 / ↑M| ≤ 1 * 6 :=
        mul_le_mul hS4_abs hlin (abs_nonneg _) zero_le_one
      _ = 6 := one_mul 6
  have htri1 :
      |1 - 2 * S4 - 4 * x * tail - (1 - 2 * S4) * (4 * δ + 2 * δ ^ 2 / (M : ℝ))| ≤
        |1 - 2 * S4| + |4 * x * tail| + |(1 - 2 * S4) * (4 * δ + 2 * δ ^ 2 / (M : ℝ))| := by
    have t1 := abs_sub (1 - 2 * S4 - 4 * x * tail) ((1 - 2 * S4) * (4 * δ + 2 * δ ^ 2 / (M : ℝ)))
    have t2 := abs_sub (1 - 2 * S4) (4 * x * tail)
    linarith
  linarith

/-- Asymptotic sawtooth identity for the Gauss circle error term `P(x)`. -/
theorem gaussCircleError_add_four_sum_sawtooth_isBigO :
    (fun x => gaussCircleError x +
        4 * (∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (ZMod.χ₄ (d : ℕ) : ℝ) * sawtooth (x / (d : ℝ)) +
          ∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
            (sawtooth (x / (4 * (m : ℝ)) + 3 / 4) - sawtooth (x / (4 * (m : ℝ)) + 1 / 4)))) =O[atTop]
      (fun _ : ℝ => (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 55 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simpa [Real.norm_eq_abs] using abs_gaussCircleError_add_four_sum_sawtooth_le hx

end ExactSawtoothIdentities

end AnalyticNumberTheory.DivisorProblems
