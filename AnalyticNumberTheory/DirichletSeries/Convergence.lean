import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Order.LiminfLimsup

/-!
# Convergence of Dirichlet Series

This file develops the convergence theory of Dirichlet series `∑_{n ≥ 1} f n * n ^ (-s)`:

- Partial sums `dirichletPartialSum`, conditional convergence `DirichletConvergesAt`,
  sum function `dirichletSum`, and the abscissa of convergence `abscissaOfConvergence` (`σ_c`),
  alongside Mathlib's absolute convergence abscissa `LSeries.abscissaOfAbsConv` (`σ_a`).
- Discrete Abel summation and complex power difference bounds.
- Half-plane convergence (`σ_c < Re s`), uniform convergence on compact subsets of `{s | σ_c < Re s}`,
  locally uniform convergence, holomorphicity (`DifferentiableOn` / `AnalyticOnNhd` / `AnalyticOn`),
  and termwise differentiation `deriv (dirichletSum f) s = dirichletSum (fun n ↦ -log n * f n) s`
  as well as `deriv (LSeries f) s = LSeries (fun n ↦ -log n * f n) s`.
- The classical abscissa bounds `σ_c ≤ σ_a ≤ σ_c + 1`.
- Cahen's formula expressing `σ_c` as `limsup (log ‖∑_{n ≤ N} f n‖ / log N)` when `σ_c ≥ 0`.
-/

open Complex Filter Topology

namespace AnalyticNumberTheory.DirichletSeries

/-! ### Partial sums, conditional convergence, and abscissae -/

/-- The `N`-th partial sum `∑_{1 ≤ n ≤ N} f n / n ^ s` of the Dirichlet series attached to `f`. -/
noncomputable def dirichletPartialSum (f : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, LSeries.term f s n

/-- The Dirichlet series of `f` converges conditionally at `s` if its partial sums converge. -/
def DirichletConvergesAt (f : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (dirichletPartialSum f s) atTop (𝓝 L)

/-- The conditional sum of the Dirichlet series of `f` at `s` (chosen `0` when divergent). -/
noncomputable def dirichletSum (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  by classical exact if h : DirichletConvergesAt f s then Classical.choose h else 0

/-- The abscissa of conditional convergence `σ_c` of the Dirichlet series of `f`. -/
noncomputable def abscissaOfConvergence (f : ℕ → ℂ) : EReal :=
  sInf (Real.toEReal '' {x : ℝ | DirichletConvergesAt f x})

/-- Re-export of Mathlib's abscissa of absolute convergence `σ_a` for convenience. -/
noncomputable abbrev abscissaOfAbsConv (f : ℕ → ℂ) : EReal :=
  LSeries.abscissaOfAbsConv f

/-- The zero-th partial sum of any Dirichlet series is `0`. -/
@[simp]
theorem dirichletPartialSum_zero (f : ℕ → ℂ) (s : ℂ) : dirichletPartialSum f s 0 = 0 := by
  simp [dirichletPartialSum]

/-- Recurrence relating the `(N + 1)`-th and `N`-th partial sums of a Dirichlet series. -/
theorem dirichletPartialSum_succ (f : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    dirichletPartialSum f s (N + 1) =
      dirichletPartialSum f s N + LSeries.term f s (N + 1) := by
  have hinsert : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext x; simp; omega
  have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
  rw [dirichletPartialSum, hinsert, Finset.sum_insert hnot, add_comm, dirichletPartialSum]

/-- Difference of two partial sums expressed as a sum over `Finset.Ioc M N`. -/
theorem dirichletPartialSum_sub_eq_sum_Ioc (f : ℕ → ℂ) (s : ℂ) {M N : ℕ} (hMN : M ≤ N) :
    dirichletPartialSum f s N - dirichletPartialSum f s M =
      ∑ n ∈ Finset.Ioc M N, LSeries.term f s n := by
  have hunion : Finset.Icc 1 N = Finset.Icc 1 M ∪ Finset.Ioc M N := by
    ext x; simp; omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Ioc M N) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
    omega
  rw [dirichletPartialSum, dirichletPartialSum, hunion, Finset.sum_union hdisj, add_sub_cancel_left]

/-- If `DirichletConvergesAt f s`, the partial sums converge to `dirichletSum f s`. -/
theorem DirichletConvergesAt.tendsto {f : ℕ → ℂ} {s : ℂ} (h : DirichletConvergesAt f s) :
    Tendsto (dirichletPartialSum f s) atTop (𝓝 (dirichletSum f s)) := by
  simp only [dirichletSum, h, ↓reduceDIte]
  exact Classical.choose_spec h

/-- If `DirichletConvergesAt f s`, the partial sums form a Cauchy sequence. -/
theorem DirichletConvergesAt.cauchySeq {f : ℕ → ℂ} {s : ℂ} (h : DirichletConvergesAt f s) :
    CauchySeq (dirichletPartialSum f s) :=
  h.tendsto.cauchySeq

/-- A convergent sequence in a normed space has uniformly bounded norms. -/
private theorem exists_norm_bound_of_tendsto {u : ℕ → ℂ} {L : ℂ}
    (hu : Tendsto u atTop (𝓝 L)) : ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, ‖u N‖ ≤ B := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hu 1 zero_lt_one
  refine ⟨max (‖L‖ + 1) (∑ k ∈ Finset.range N₀, ‖u k‖) + 1, by positivity, fun N ↦ ?_⟩
  rcases le_or_gt N₀ N with hN | hN
  · have hdist : ‖u N - L‖ < 1 := by
      simpa [dist_eq_norm] using hN₀ N hN
    have hnorm : ‖u N‖ ≤ ‖L‖ + 1 := by
      calc
        ‖u N‖ = ‖(u N - L) + L‖ := by ring_nf
        _ ≤ ‖u N - L‖ + ‖L‖ := norm_add_le _ _
        _ ≤ 1 + ‖L‖ := by linarith
        _ = ‖L‖ + 1 := add_comm _ _
    linarith [le_max_left (‖L‖ + 1) (∑ k ∈ Finset.range N₀, ‖u k‖)]
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr hN
    have hle : ‖u N‖ ≤ ∑ k ∈ Finset.range N₀, ‖u k‖ :=
      Finset.single_le_sum (fun k _ ↦ norm_nonneg (u k)) hmem
    linarith [le_max_right (‖L‖ + 1) (∑ k ∈ Finset.range N₀, ‖u k‖)]

/-- If `DirichletConvergesAt f s`, the partial sums are uniformly bounded in norm. -/
theorem DirichletConvergesAt.exists_bound {f : ℕ → ℂ} {s : ℂ} (h : DirichletConvergesAt f s) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, ‖dirichletPartialSum f s N‖ ≤ B :=
  exists_norm_bound_of_tendsto h.tendsto

/-- Absolute convergence of `LSeries` implies conditional convergence. -/
theorem _root_.LSeriesSummable.dirichletConvergesAt {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : DirichletConvergesAt f s := by
  refine ⟨LSeries f s, ?_⟩
  have hnat : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, LSeries.term f s n)
      atTop (𝓝 (LSeries f s)) := h.hasSum.tendsto_sum_nat
  have hshift : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), LSeries.term f s n)
      atTop (𝓝 (LSeries f s)) := hnat.comp (tendsto_add_atTop_nat 1)
  refine hshift.congr fun N ↦ ?_
  have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext x; simp; omega
  have h0 : 0 ∉ Finset.Icc 1 N := by simp
  rw [hsplit, Finset.sum_insert h0, LSeries.term_zero, zero_add, dirichletPartialSum]

/-- When `LSeriesSummable f s`, `dirichletSum f s` coincides with `LSeries f s`. -/
theorem _root_.LSeriesSummable.dirichletSum_eq_LSeries {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) : dirichletSum f s = LSeries f s := by
  have hnat : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), LSeries.term f s n)
      atTop (𝓝 (LSeries f s)) := h.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hpart : Tendsto (dirichletPartialSum f s) atTop (𝓝 (LSeries f s)) := by
    refine hnat.congr fun N ↦ ?_
    have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext x; simp; omega
    rw [hsplit, Finset.sum_insert (by simp), LSeries.term_zero, zero_add, dirichletPartialSum]
  exact tendsto_nhds_unique h.dirichletConvergesAt.tendsto hpart

/-! ### Discrete Abel summation and complex power difference bounds -/

private theorem sum_Ico_telescope {α : Type*} [AddCommGroup α] (g : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (g n - g (n + 1)) = g a - g b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hsplit : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp; omega
    have hnot : b ∉ Finset.Ico a b := by simp
    rw [hsplit, Finset.sum_insert hnot, ih]
    abel

/-- Discrete Abel summation (summation by parts) for partial sums starting at `n = 1`. -/
theorem abel_summation (a g : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    let S : ℕ → ℂ := fun k ↦ ∑ n ∈ Finset.Icc 1 k, a n
    ∑ n ∈ Finset.Ioc M N, a n * g n =
      (S N - S M) * g N + ∑ n ∈ Finset.Ico (M + 1) N, (S n - S M) * (g n - g (n + 1)) := by
  intro S
  induction N, hMN using Nat.le_induction with
  | base =>
    simp
  | succ N hMN ih =>
    have hIoc : Finset.Ioc M (N + 1) = insert (N + 1) (Finset.Ioc M N) := by
      ext x; simp; omega
    have hS : S (N + 1) = S N + a (N + 1) := by
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x; simp; omega
      dsimp [S]
      rw [hIcc, Finset.sum_insert (by simp), add_comm]
    rw [hIoc, Finset.sum_insert (by simp), ih]
    rcases eq_or_lt_of_le hMN with rfl | hlt
    · have hSM : S (M + 1) - S M = a (M + 1) := by
        rw [hS]; ring
      simp [hSM, mul_comm]
    · have hIco : Finset.Ico (M + 1) (N + 1) = insert N (Finset.Ico (M + 1) N) := by
        ext x; simp; omega
      rw [hIco, Finset.sum_insert (by simp), hS]
      ring

/-- Alternative form of discrete Abel summation for `M < N` separating the endpoint
`S M * g (M + 1)`. -/
theorem abel_summation_of_lt (a g : ℕ → ℂ) {M N : ℕ} (hMN : M < N) :
    let S : ℕ → ℂ := fun k ↦ ∑ n ∈ Finset.Icc 1 k, a n
    ∑ n ∈ Finset.Ioc M N, a n * g n =
      S N * g N - S M * g (M + 1) + ∑ n ∈ Finset.Ico (M + 1) N, S n * (g n - g (n + 1)) := by
  intro S
  have h1 := abel_summation a g hMN.le
  dsimp only at h1
  have hmul : ∑ n ∈ Finset.Ico (M + 1) N, (S n - S M) * (g n - g (n + 1)) =
      (∑ n ∈ Finset.Ico (M + 1) N, S n * (g n - g (n + 1))) -
        S M * ∑ n ∈ Finset.Ico (M + 1) N, (g n - g (n + 1)) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h1, hmul, sum_Ico_telescope g hMN]
  ring

/-- Upper bound for `‖n ^ (-z) - (n + 1) ^ (-z)‖` when `n ≥ 1` and `Re z > 0`. -/
theorem norm_cpow_neg_sub_succ_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : 0 < z.re) :
    ‖(n : ℂ) ^ (-z) - ((n + 1 : ℕ) : ℂ) ^ (-z)‖ ≤
      (‖z‖ / z.re) * ((n : ℝ) ^ (-z.re) - ((n + 1 : ℕ) : ℝ) ^ (-z.re)) := by
  have hz_ne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have h0_not_mem : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    intro h0
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ n)] at h0
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    linarith [h0.1]
  have hint_c :
      (∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), (x : ℂ) ^ (-z - 1)) =
        (((n + 1 : ℕ) : ℂ) ^ (-z) - (n : ℂ) ^ (-z)) / (-z) := by
    have hr : -z - 1 ≠ -1 := by
      intro h
      apply hz_ne
      linear_combination -h
    simpa [sub_add_cancel] using
      integral_cpow (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ)) (r := -z - 1)
        (Or.inr ⟨hr, h0_not_mem⟩)
  have heq : (n : ℂ) ^ (-z) - ((n + 1 : ℕ) : ℂ) ^ (-z) =
      z * ∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), (x : ℂ) ^ (-z - 1) := by
    rw [hint_c]
    field_simp [hz_ne]
    ring
  have hnorm_le :
      ‖∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), (x : ℂ) ^ (-z - 1)‖ ≤
        ∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-z - 1)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by exact_mod_cast Nat.le_succ n)
  have hcongr :
      (∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-z - 1)‖) =
        ∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), x ^ (-z.re - 1) := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ n)] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast hn) hx.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    simp
  have hint_r :
      (∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), x ^ (-z.re - 1)) =
        ((n : ℝ) ^ (-z.re) - ((n + 1 : ℕ) : ℝ) ^ (-z.re)) / z.re := by
    have hr : -z.re - 1 ≠ -1 := by linarith
    have h := integral_rpow (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ))
      (r := -z.re - 1) (Or.inr ⟨hr, h0_not_mem⟩)
    have hexp : -z.re - 1 + 1 = -z.re := by ring
    rw [hexp] at h
    rw [h]
    field_simp [hz.ne']
    ring
  calc
    ‖(n : ℂ) ^ (-z) - ((n + 1 : ℕ) : ℂ) ^ (-z)‖
        = ‖z‖ * ‖∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), (x : ℂ) ^ (-z - 1)‖ := by
      rw [heq, norm_mul]
    _ ≤ ‖z‖ * ∫ x : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), ‖(x : ℂ) ^ (-z - 1)‖ := by
      gcongr
    _ = ‖z‖ * (((n : ℝ) ^ (-z.re) - ((n + 1 : ℕ) : ℝ) ^ (-z.re)) / z.re) := by
      rw [hcongr, hint_r]
    _ = (‖z‖ / z.re) * ((n : ℝ) ^ (-z.re) - ((n + 1 : ℕ) : ℝ) ^ (-z.re)) := by
      ring

/-- Abel-summation Cauchy estimate: for `M ≤ N` and `Re s₀ < Re s`, differences of partial sums
at `s` are controlled by differences of partial sums at `s₀` multiplied by `‖s - s₀‖ / Re (s - s₀)`. -/
theorem norm_dirichletPartialSum_sub_le (f : ℕ → ℂ) {s₀ s : ℂ} (hs : s₀.re < s.re)
    {M N : ℕ} (hMN : M ≤ N) {B : ℝ}
    (hB : ∀ k ∈ Finset.Icc M N, ‖dirichletPartialSum f s₀ k - dirichletPartialSum f s₀ M‖ ≤ B) :
    ‖dirichletPartialSum f s N - dirichletPartialSum f s M‖ ≤
      B * (‖s - s₀‖ / (s.re - s₀.re)) * ((M + 1 : ℕ) : ℝ) ^ (s₀.re - s.re) := by
  let z : ℂ := s - s₀
  have hz : 0 < z.re := by simpa [z] using sub_pos.mpr hs
  have hB_nonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB M (Finset.left_mem_Icc.mpr hMN))
  have hK_ge_one : 1 ≤ ‖z‖ / z.re := by
    rw [one_le_div hz]
    exact Complex.re_le_norm z
  have hterm (n : ℕ) (hn : 1 ≤ n) :
      LSeries.term f s n = LSeries.term f s₀ n * (n : ℂ) ^ (-z) := by
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0, Complex.cpow_neg,
      div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    congr 1
    rw [← _root_.mul_inv_rev, mul_comm ((n : ℂ) ^ z),
      ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn0)]
    simp [z]
  have hab :
      dirichletPartialSum f s N - dirichletPartialSum f s M =
        (dirichletPartialSum f s₀ N - dirichletPartialSum f s₀ M) * (N : ℂ) ^ (-z) +
          ∑ n ∈ Finset.Ico (M + 1) N,
            (dirichletPartialSum f s₀ n - dirichletPartialSum f s₀ M) *
              ((n : ℂ) ^ (-z) - ((n + 1 : ℕ) : ℂ) ^ (-z)) := by
    rw [dirichletPartialSum_sub_eq_sum_Ioc f s hMN]
    have hcongr :
        (∑ n ∈ Finset.Ioc M N, LSeries.term f s n) =
          ∑ n ∈ Finset.Ioc M N, LSeries.term f s₀ n * (n : ℂ) ^ (-z) := by
      refine Finset.sum_congr rfl fun n hn ↦ hterm n ?_
      simp only [Finset.mem_Ioc] at hn
      omega
    rw [hcongr]
    simpa [dirichletPartialSum] using
      abel_summation (LSeries.term f s₀) (fun n ↦ (n : ℂ) ^ (-z)) hMN
  rcases eq_or_lt_of_le hMN with rfl | hlt
  · simp only [sub_self, norm_zero]
    positivity
  · have hN1 : 1 ≤ N := by omega
    have hN_norm : ‖(N : ℂ) ^ (-z)‖ = (N : ℝ) ^ (-z.re) := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (by omega : 0 < N))]
      simp
    have hN_nonneg : 0 ≤ (N : ℝ) ^ (-z.re) := Real.rpow_nonneg N.cast_nonneg _
    have hsum_le :
        ‖∑ n ∈ Finset.Ico (M + 1) N,
            (dirichletPartialSum f s₀ n - dirichletPartialSum f s₀ M) *
              ((n : ℂ) ^ (-z) - ((n + 1 : ℕ) : ℂ) ^ (-z))‖ ≤
          ∑ n ∈ Finset.Ico (M + 1) N,
            B * (‖z‖ / z.re) * ((n : ℝ) ^ (-z.re) - ((n + 1 : ℕ) : ℝ) ^ (-z.re)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
      simp only [Finset.mem_Ico] at hn
      rw [norm_mul]
      refine mul_le_mul (hB n (Finset.mem_Icc.mpr ⟨by omega, hn.2.le⟩))
        (norm_cpow_neg_sub_succ_le (by omega) hz) (norm_nonneg _) hB_nonneg |>.trans ?_
      ring_nf
      rfl
    have htel :
        (∑ n ∈ Finset.Ico (M + 1) N,
            B * (‖z‖ / z.re) * ((n : ℝ) ^ (-z.re) - ((n + 1 : ℕ) : ℝ) ^ (-z.re))) =
          B * (‖z‖ / z.re) * (((M + 1 : ℕ) : ℝ) ^ (-z.re) - (N : ℝ) ^ (-z.re)) := by
      rw [← Finset.mul_sum, sum_Ico_telescope (fun n ↦ (n : ℝ) ^ (-z.re)) hlt]
    have hmain :
        ‖(dirichletPartialSum f s₀ N - dirichletPartialSum f s₀ M) * (N : ℂ) ^ (-z)‖ ≤
          B * (‖z‖ / z.re) * (N : ℝ) ^ (-z.re) := by
      rw [norm_mul, hN_norm]
      calc
        ‖dirichletPartialSum f s₀ N - dirichletPartialSum f s₀ M‖ * (N : ℝ) ^ (-z.re)
            ≤ B * (N : ℝ) ^ (-z.re) :=
          mul_le_mul_of_nonneg_right (hB N (Finset.right_mem_Icc.mpr hlt.le)) hN_nonneg
        _ = B * 1 * (N : ℝ) ^ (-z.re) := by ring
        _ ≤ B * (‖z‖ / z.re) * (N : ℝ) ^ (-z.re) := by
          gcongr
    calc
      ‖dirichletPartialSum f s N - dirichletPartialSum f s M‖
          ≤ ‖(dirichletPartialSum f s₀ N - dirichletPartialSum f s₀ M) * (N : ℂ) ^ (-z)‖ +
              ‖∑ n ∈ Finset.Ico (M + 1) N,
                (dirichletPartialSum f s₀ n - dirichletPartialSum f s₀ M) *
                  ((n : ℂ) ^ (-z) - ((n + 1 : ℕ) : ℂ) ^ (-z))‖ := by
        rw [hab]
        exact norm_add_le _ _
      _ ≤ B * (‖z‖ / z.re) * (N : ℝ) ^ (-z.re) +
            B * (‖z‖ / z.re) * (((M + 1 : ℕ) : ℝ) ^ (-z.re) - (N : ℝ) ^ (-z.re)) :=
        add_le_add hmain (hsum_le.trans_eq htel)
      _ = B * (‖s - s₀‖ / (s.re - s₀.re)) * ((M + 1 : ℕ) : ℝ) ^ (s₀.re - s.re) := by
        simp only [z, Complex.sub_re]
        have hneg : -(s.re - s₀.re) = s₀.re - s.re := by ring
        rw [hneg]
        ring

/-- Simplified Abel-summation Cauchy estimate dropping the factor
`((M + 1 : ℕ) : ℝ) ^ (s₀.re - s.re) ≤ 1`. -/
theorem norm_dirichletPartialSum_sub_le_of_re_lt (f : ℕ → ℂ) {s₀ s : ℂ} (hs : s₀.re < s.re)
    {M N : ℕ} (hMN : M ≤ N) {B : ℝ}
    (hB : ∀ k ∈ Finset.Icc M N, ‖dirichletPartialSum f s₀ k - dirichletPartialSum f s₀ M‖ ≤ B) :
    ‖dirichletPartialSum f s N - dirichletPartialSum f s M‖ ≤
      B * (‖s - s₀‖ / (s.re - s₀.re)) := by
  have hB_nonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB M (Finset.left_mem_Icc.mpr hMN))
  have hpow : ((M + 1 : ℕ) : ℝ) ^ (s₀.re - s.re) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
    exact_mod_cast Nat.succ_pos M
  have hfac : 0 ≤ B * (‖s - s₀‖ / (s.re - s₀.re)) := by
    have : 0 < s.re - s₀.re := sub_pos.mpr hs
    positivity
  calc
    ‖dirichletPartialSum f s N - dirichletPartialSum f s M‖
        ≤ B * (‖s - s₀‖ / (s.re - s₀.re)) * ((M + 1 : ℕ) : ℝ) ^ (s₀.re - s.re) :=
      norm_dirichletPartialSum_sub_le f hs hMN hB
    _ ≤ B * (‖s - s₀‖ / (s.re - s₀.re)) * 1 := by gcongr
    _ = B * (‖s - s₀‖ / (s.re - s₀.re)) := mul_one _

/-! ### Half-plane convergence, uniform convergence, holomorphicity, and differentiation -/

/-- Uniform Cauchy property on any bounded set `K` inside a half-plane `Re s ≥ σ₁ > Re s₀`
when the series converges at `s₀`. -/
private theorem uniformCauchySeqOn_of_dirichletConvergesAt {f : ℕ → ℂ} {s₀ : ℂ}
    (h₀ : DirichletConvergesAt f s₀) {K : Set ℂ} {σ₁ R : ℝ} (hσ₁ : s₀.re < σ₁)
    (hK_re : ∀ s ∈ K, σ₁ ≤ s.re) (hK_norm : ∀ s ∈ K, ‖s - s₀‖ ≤ R) :
    UniformCauchySeqOn (fun N s ↦ dirichletPartialSum f s N) atTop K := by
  by_cases hKne : K.Nonempty
  · obtain ⟨s_wit, hs_wit⟩ := hKne
    have hR_nonneg : 0 ≤ R := (norm_nonneg _).trans (hK_norm s_wit hs_wit)
    let C : ℝ := R / (σ₁ - s₀.re)
    have hC_nonneg : 0 ≤ C := div_nonneg hR_nonneg (sub_pos.mpr hσ₁).le
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hcauchy := Metric.cauchySeq_iff.mp h₀.cauchySeq
    obtain ⟨N₀, hN₀⟩ := hcauchy (ε / (2 * (C + 1))) (by positivity)
    refine ⟨N₀, fun m hm n hn s hs ↦ ?_⟩
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]
      exact this n hn m hm (le_of_not_ge hmn)
    have hs_re : s₀.re < s.re := lt_of_lt_of_le hσ₁ (hK_re s hs)
    have hbound : ∀ k ∈ Finset.Icc m n,
        ‖dirichletPartialSum f s₀ k - dirichletPartialSum f s₀ m‖ ≤ ε / (2 * (C + 1)) := by
      intro k hk
      have hk_ge : N₀ ≤ k := hm.trans (Finset.mem_Icc.mp hk).1
      simpa [dist_eq_norm] using (hN₀ k hk_ge m hm).le
    have hdiff := norm_dirichletPartialSum_sub_le_of_re_lt f hs_re hmn hbound
    have hfac : ‖s - s₀‖ / (s.re - s₀.re) ≤ C := by
      refine div_le_div₀ hR_nonneg (hK_norm s hs) (sub_pos.mpr hσ₁) ?_
      linarith [hK_re s hs]
    have hdist_le : dist (dirichletPartialSum f s m) (dirichletPartialSum f s n) ≤
        (ε / (2 * (C + 1))) * C := by
      rw [dist_comm, dist_eq_norm]
      exact hdiff.trans (mul_le_mul_of_nonneg_left hfac (by positivity))
    have hlt : (ε / (2 * (C + 1))) * C < ε := by
      have hC1 : C < 2 * (C + 1) := by linarith
      calc
        (ε / (2 * (C + 1))) * C < (ε / (2 * (C + 1))) * (2 * (C + 1)) := by
          gcongr
        _ = ε := div_mul_cancel₀ ε (by positivity)
    exact lt_of_le_of_lt hdist_le hlt
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    subst hKne
    simp [UniformCauchySeqOn]

/-- If a Dirichlet series converges at `s₀`, then it converges at every `s` with `Re s₀ < Re s`. -/
theorem dirichletConvergesAt_of_re_lt_re {f : ℕ → ℂ} {s₀ s : ℂ}
    (h₀ : DirichletConvergesAt f s₀) (hs : s₀.re < s.re) : DirichletConvergesAt f s := by
  have huc := uniformCauchySeqOn_of_dirichletConvergesAt h₀ (K := {s}) (σ₁ := s.re)
    (R := ‖s - s₀‖) hs (fun z hz ↦ by simp at hz; subst hz; exact le_rfl)
    (fun z hz ↦ by simp at hz; subst hz; exact le_rfl)
  have hcauchy : CauchySeq (dirichletPartialSum f s) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp huc) ε hε
    exact ⟨N, fun m hm n hn ↦ hN m hm n hn s rfl⟩
  exact cauchySeq_tendsto_of_complete hcauchy

/-- If `abscissaOfConvergence f < (σ₁ : EReal)`, there is a real `x₀ < σ₁` where the series converges. -/
private theorem exists_real_lt_of_abscissaOfConvergence_lt {f : ℕ → ℂ} {σ₁ : ℝ}
    (h : abscissaOfConvergence f < (σ₁ : EReal)) :
    ∃ x₀ : ℝ, DirichletConvergesAt f x₀ ∧ x₀ < σ₁ := by
  by_contra hnone
  push Not at hnone
  have hle : (σ₁ : EReal) ≤ abscissaOfConvergence f := by
    refine le_sInf ?_
    rintro y ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hnone x hx)
  exact (h.trans_le hle).false

/-- Convergence of the Dirichlet series everywhere in the open half-plane `σ_c < Re s`. -/
theorem dirichletConvergesAt_of_abscissaOfConvergence_lt_re {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfConvergence f < (s.re : EReal)) : DirichletConvergesAt f s := by
  obtain ⟨x₀, hx₀, hx₀_lt⟩ := exists_real_lt_of_abscissaOfConvergence_lt h
  exact dirichletConvergesAt_of_re_lt_re hx₀ (by simpa using hx₀_lt)

/-- If the Dirichlet series converges at `s`, then `abscissaOfConvergence f ≤ Re s`. -/
theorem abscissaOfConvergence_le_of_dirichletConvergesAt {f : ℕ → ℂ} {s : ℂ}
    (h : DirichletConvergesAt f s) : abscissaOfConvergence f ≤ (s.re : EReal) := by
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hx' : s.re < x := EReal.coe_lt_coe_iff.mp hx
  have hxconv : DirichletConvergesAt f (x : ℂ) :=
    dirichletConvergesAt_of_re_lt_re h (by simpa using hx')
  exact sInf_le ⟨x, hxconv, rfl⟩

/-- The open half-plane `{s : ℂ | σ < Re s}` is open for every `σ : EReal`. -/
private theorem isOpen_re_gt_EReal (σ : EReal) : IsOpen {s : ℂ | σ < (s.re : EReal)} := by
  induction σ using EReal.rec with
  | bot =>
    have huniv : {s : ℂ | (⊥ : EReal) < (s.re : EReal)} = Set.univ := by
      ext s
      simp [EReal.bot_lt_coe]
    rw [huniv]
    exact isOpen_univ
  | coe r =>
    simpa [EReal.coe_lt_coe_iff] using isOpen_lt continuous_const Complex.continuous_re
  | top =>
    have hempty : {s : ℂ | (⊤ : EReal) < (s.re : EReal)} = ∅ := by
      ext s
      simp
    rw [hempty]
    exact isOpen_empty

/-- The partial sums of a Dirichlet series converge uniformly on every compact subset of the
half-plane of convergence `{s : ℂ | σ_c < Re s}`. -/
theorem tendstoUniformlyOn_dirichletPartialSum (f : ℕ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (hK_sub : K ⊆ {s : ℂ | abscissaOfConvergence f < (s.re : EReal)}) :
    TendstoUniformlyOn (fun N s ↦ dirichletPartialSum f s N) (dirichletSum f) atTop K := by
  by_cases hKne : K.Nonempty
  · obtain ⟨s₁, hs₁K, hs₁_min⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
    obtain ⟨x₀, hx₀, hx₀_lt⟩ := exists_real_lt_of_abscissaOfConvergence_lt (hK_sub hs₁K)
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
      ((continuous_id.sub continuous_const).continuousOn :
        ContinuousOn (fun s : ℂ ↦ s - (x₀ : ℂ)) K)
    have huc : UniformCauchySeqOn (fun N s ↦ dirichletPartialSum f s N) atTop K :=
      uniformCauchySeqOn_of_dirichletConvergesAt hx₀ (by simpa using hx₀_lt)
        (fun s hs ↦ hs₁_min hs) hR
    refine huc.tendstoUniformlyOn_of_tendsto fun s hs ↦ ?_
    exact (dirichletConvergesAt_of_abscissaOfConvergence_lt_re (hK_sub hs)).tendsto
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    subst hKne
    simp [TendstoUniformlyOn]

/-- The partial sums of a Dirichlet series converge locally uniformly on `{s : ℂ | σ_c < Re s}`. -/
theorem tendstoLocallyUniformlyOn_dirichletPartialSum (f : ℕ → ℂ) :
    TendstoLocallyUniformlyOn (fun N s ↦ dirichletPartialSum f s N) (dirichletSum f)
      atTop {s : ℂ | abscissaOfConvergence f < (s.re : EReal)} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_re_gt_EReal _)]
  intro K hK_sub hK
  exact tendstoUniformlyOn_dirichletPartialSum f hK hK_sub

private theorem hasDerivAt_LSeries_term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    HasDerivAt (fun z ↦ LSeries.term f z n) (LSeries.term (fun m ↦ -Complex.log m * f m) s n) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [LSeries.term_zero] using hasDerivAt_const s (0 : ℂ)
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hfun : (fun z ↦ LSeries.term f z n) = fun z ↦ f n * Complex.exp (Complex.log n * (-z)) := by
      funext z
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
        Complex.cpow_def_of_ne_zero hn0]
    rw [hfun]
    have hd : HasDerivAt (fun z ↦ f n * Complex.exp (Complex.log n * (-z)))
        (f n * (Complex.exp (Complex.log n * (-s)) * (Complex.log n * -1))) s :=
      ((hasDerivAt_neg s).const_mul (Complex.log n)).cexp.const_mul (f n)
    refine hd.congr_deriv ?_
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.cpow_def_of_ne_zero hn0]
    ring

/-- Each partial sum `z ↦ dirichletPartialSum f z N` is entire, with derivative equal to the
partial sum of `-log n * f n`. -/
theorem hasDerivAt_dirichletPartialSum (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ dirichletPartialSum f z N)
      (dirichletPartialSum (fun m ↦ -Complex.log m * f m) s N) s := by
  simpa [dirichletPartialSum] using
    HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_LSeries_term f s n

/-- Each partial sum `z ↦ dirichletPartialSum f z N` is entire (`Differentiable ℂ`). -/
theorem dirichletPartialSum_differentiable (f : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (fun z ↦ dirichletPartialSum f z N) := fun s ↦
  (hasDerivAt_dirichletPartialSum f N s).differentiableAt

/-- `dirichletSum f` is complex-differentiable on `{s : ℂ | σ_c < Re s}`. -/
theorem dirichletSum_differentiableOn (f : ℕ → ℂ) :
    DifferentiableOn ℂ (dirichletSum f) {s : ℂ | abscissaOfConvergence f < (s.re : EReal)} :=
  (tendstoLocallyUniformlyOn_dirichletPartialSum f).differentiableOn
    (Eventually.of_forall fun N ↦ (dirichletPartialSum_differentiable f N).differentiableOn)
    (isOpen_re_gt_EReal _)

/-- `dirichletSum f` is analytic at every point of `{s : ℂ | σ_c < Re s}`. -/
theorem dirichletSum_analyticOnNhd (f : ℕ → ℂ) :
    AnalyticOnNhd ℂ (dirichletSum f) {s : ℂ | abscissaOfConvergence f < (s.re : EReal)} :=
  (dirichletSum_differentiableOn f).analyticOnNhd (isOpen_re_gt_EReal _)

/-- `dirichletSum f` is analytic on `{s : ℂ | σ_c < Re s}`. -/
theorem dirichletSum_analyticOn (f : ℕ → ℂ) :
    AnalyticOn ℂ (dirichletSum f) {s : ℂ | abscissaOfConvergence f < (s.re : EReal)} :=
  (dirichletSum_analyticOnNhd f).analyticOn

/-- The locally uniform convergence of the termwise-differentiated Dirichlet series. -/
private theorem tendsto_deriv_dirichletPartialSum {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfConvergence f < (s.re : EReal)) :
    Tendsto (dirichletPartialSum (fun m ↦ -Complex.log m * f m) s)
      atTop (𝓝 (deriv (dirichletSum f) s)) := by
  have hloc :
      TendstoLocallyUniformlyOn (deriv ∘ fun N z ↦ dirichletPartialSum f z N)
        (deriv (dirichletSum f)) atTop {z : ℂ | abscissaOfConvergence f < (z.re : EReal)} :=
    (tendstoLocallyUniformlyOn_dirichletPartialSum f).deriv
      (Eventually.of_forall fun N ↦ (dirichletPartialSum_differentiable f N).differentiableOn)
      (isOpen_re_gt_EReal _)
  have ht := hloc.tendsto_at hs
  refine ht.congr fun N ↦ ?_
  change deriv (fun z ↦ dirichletPartialSum f z N) s =
    dirichletPartialSum (fun m ↦ -Complex.log m * f m) s N
  exact (hasDerivAt_dirichletPartialSum f N s).deriv

/-- The termwise-differentiated Dirichlet series `∑ (-log n * f n) n ^ (-s)` converges everywhere
in `{s : ℂ | σ_c < Re s}`. -/
theorem dirichletConvergesAt_neg_log_mul {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfConvergence f < (s.re : EReal)) :
    DirichletConvergesAt (fun m ↦ -Complex.log m * f m) s :=
  ⟨deriv (dirichletSum f) s, tendsto_deriv_dirichletPartialSum hs⟩

/-- Differentiation does not increase the abscissa of conditional convergence. -/
theorem abscissaOfConvergence_neg_log_mul_le (f : ℕ → ℂ) :
    abscissaOfConvergence (fun m ↦ -Complex.log m * f m) ≤ abscissaOfConvergence f := by
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hs : abscissaOfConvergence f < ((x : ℂ).re : EReal) := by
    simpa using hx
  exact abscissaOfConvergence_le_of_dirichletConvergesAt (dirichletConvergesAt_neg_log_mul hs)

/-- Termwise differentiation of a conditionally convergent Dirichlet series:
for `σ_c < Re s`, `deriv (dirichletSum f) s = dirichletSum (fun n ↦ -Complex.log n * f n) s`. -/
theorem deriv_dirichletSum {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfConvergence f < (s.re : EReal)) :
    deriv (dirichletSum f) s = dirichletSum (fun m ↦ -Complex.log m * f m) s :=
  tendsto_nhds_unique (tendsto_deriv_dirichletPartialSum hs)
    (dirichletConvergesAt_neg_log_mul hs).tendsto

/-- `HasDerivAt` version of termwise differentiation for `dirichletSum`. -/
theorem hasDerivAt_dirichletSum {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfConvergence f < (s.re : EReal)) :
    HasDerivAt (dirichletSum f) (dirichletSum (fun m ↦ -Complex.log m * f m) s) s := by
  have hdiff : DifferentiableAt ℂ (dirichletSum f) s :=
    (dirichletSum_differentiableOn f).differentiableAt ((isOpen_re_gt_EReal _).mem_nhds hs)
  rw [← deriv_dirichletSum hs]
  exact hdiff.hasDerivAt

/-- Termwise differentiation of `LSeries` for `σ_a < Re s`:
`deriv (LSeries f) s = LSeries (fun n ↦ -Complex.log n * f n) s`. -/
theorem deriv_LSeries {f : ℕ → ℂ} {s : ℂ} (hs : LSeries.abscissaOfAbsConv f < (s.re : EReal)) :
    deriv (LSeries f) s = LSeries (fun m ↦ -Complex.log m * f m) s := by
  rw [LSeries_deriv hs, ← LSeries_neg]
  congr 1
  ext m
  simp [LSeries.logMul, neg_mul]

/-- `HasDerivAt` version of termwise differentiation for `LSeries`. -/
theorem hasDerivAt_LSeries {f : ℕ → ℂ} {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv f < (s.re : EReal)) :
    HasDerivAt (LSeries f) (LSeries (fun m ↦ -Complex.log m * f m) s) s := by
  have h := LSeries_hasDerivAt hs
  rw [← LSeries_neg] at h
  refine h.congr_deriv ?_
  congr 1
  ext m
  simp [LSeries.logMul, neg_mul]

/-! ### Relationship between `σ_c` and `σ_a`: `σ_c ≤ σ_a ≤ σ_c + 1` -/

/-- The abscissa of conditional convergence is at most the abscissa of absolute convergence:
`σ_c ≤ σ_a`. -/
theorem abscissaOfConvergence_le_abscissaOfAbsConv (f : ℕ → ℂ) :
    abscissaOfConvergence f ≤ LSeries.abscissaOfAbsConv f := by
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hsum : LSeriesSummable f (x : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hx)
  exact sInf_le ⟨x, hsum.dirichletConvergesAt, rfl⟩

/-- If a Dirichlet series converges at `s`, then `σ_a ≤ Re s + 1`. -/
theorem abscissaOfAbsConv_le_re_add_one_of_dirichletConvergesAt {f : ℕ → ℂ} {s : ℂ}
    (h : DirichletConvergesAt f s) :
    LSeries.abscissaOfAbsConv f ≤ ((s.re + 1 : ℝ) : EReal) := by
  obtain ⟨B, hB_pos, hB⟩ := h.exists_bound
  refine LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (x := s.re) ?_
  refine ⟨2 * B, fun n hn ↦ ?_⟩
  have hterm : LSeries.term f s n =
      dirichletPartialSum f s n - dirichletPartialSum f s (n - 1) := by
    have hsucc := dirichletPartialSum_succ f s (n - 1)
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)] at hsucc
    rw [hsucc]
    ring
  have hterm_norm : ‖LSeries.term f s n‖ ≤ 2 * B := by
    rw [hterm]
    calc
      ‖dirichletPartialSum f s n - dirichletPartialSum f s (n - 1)‖
          ≤ ‖dirichletPartialSum f s n‖ + ‖dirichletPartialSum f s (n - 1)‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB n) (hB (n - 1))
      _ = 2 * B := by ring
  rw [LSeries.term_of_ne_zero hn, norm_div] at hterm_norm
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpow_norm : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hn_pos s
  rw [hpow_norm] at hterm_norm
  have hpow_pos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn_pos s.re
  exact (div_le_iff₀ hpow_pos).mp hterm_norm

/-- The abscissa of absolute convergence exceeds the abscissa of conditional convergence by
at most `1`: `σ_a ≤ σ_c + 1`. -/
theorem abscissaOfAbsConv_le_abscissaOfConvergence_add_one (f : ℕ → ℂ) :
    LSeries.abscissaOfAbsConv f ≤ abscissaOfConvergence f + 1 := by
  refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
  have hlt : abscissaOfConvergence f < ((z - 1 : ℝ) : EReal) := by
    induction hσ : abscissaOfConvergence f using EReal.rec with
    | bot => exact EReal.bot_lt_coe (z - 1)
    | coe c =>
      rw [hσ] at hz
      have hz' : c + 1 < z := by exact_mod_cast hz
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    | top =>
      rw [hσ] at hz
      exact absurd hz (not_top_lt)
  obtain ⟨x₀, hx₀, hx₀_lt⟩ := exists_real_lt_of_abscissaOfConvergence_lt hlt
  have ha := abscissaOfAbsConv_le_re_add_one_of_dirichletConvergesAt hx₀
  have hre : ((x₀ : ℂ).re + 1 : ℝ) ≤ z := by
    simp only [Complex.ofReal_re]
    linarith
  exact ha.trans (EReal.coe_le_coe_iff.mpr hre)

/-! ### Cahen's formula for nonnegative convergence abscissa -/

/-- Partial sums of coefficients `∑_{1 ≤ n ≤ N} f n`. -/
def coeffPartialSum (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f n

/-- `coeffPartialSum f N` equals the partial sum of the Dirichlet series at `s = 0`. -/
theorem coeffPartialSum_eq_dirichletPartialSum_zero (f : ℕ → ℂ) (N : ℕ) :
    coeffPartialSum f N = dirichletPartialSum f 0 N := by
  rw [coeffPartialSum, dirichletPartialSum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn0 : n ≠ 0 := by
    simp only [Finset.mem_Icc] at hn
    omega
  simp [LSeries.term_of_ne_zero hn0]

private theorem norm_rpow_neg_sub_succ_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |(n : ℝ) ^ (-x) - ((n + 1 : ℕ) : ℝ) ^ (-x)| ≤
      |x| * max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h0_not_mem : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    intro h0
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ n)] at h0
    linarith [h0.1]
  have hint :
      (∫ t : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), t ^ (-x - 1)) =
        (((n + 1 : ℕ) : ℝ) ^ (-x) - (n : ℝ) ^ (-x)) / (-x) := by
    have hr : -x - 1 ≠ -1 := by
      intro h
      apply hx
      linarith
    simpa [sub_add_cancel] using
      integral_rpow (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ))
        (r := -x - 1) (Or.inr ⟨hr, h0_not_mem⟩)
  have heq : (n : ℝ) ^ (-x) - ((n + 1 : ℕ) : ℝ) ^ (-x) =
      x * ∫ t : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), t ^ (-x - 1) := by
    rw [hint]
    field_simp [hx]
    ring
  have hle_ab : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hint_nonneg : 0 ≤ ∫ t : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), t ^ (-x - 1) := by
    refine intervalIntegral.integral_nonneg hle_ab fun t ht ↦ ?_
    exact Real.rpow_nonneg (hn_pos.le.trans ht.1) _
  have hint_le :
      (∫ t : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), t ^ (-x - 1)) ≤
        max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1) := by
    have hconst :
        (∫ _ : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ),
            max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1)) =
          max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      push_cast
      ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on hle_ab ?_ intervalIntegrable_const fun t ht ↦ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hle_ab]
      exact ContinuousOn.rpow continuousOn_id continuousOn_const
        (fun t ht ↦ Or.inl (lt_of_lt_of_le hn_pos ht.1).ne')
    · rcases le_or_gt (-x - 1) 0 with hneg | hpos
      · have hrpow : t ^ (-x - 1) ≤ (n : ℝ) ^ (-x - 1) :=
          Real.rpow_le_rpow_of_nonpos hn_pos ht.1 hneg
        calc
          t ^ (-x - 1) ≤ 1 * (n : ℝ) ^ (-x - 1) := by simpa using hrpow
          _ ≤ max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1) := by
            gcongr
            exact le_max_left _ _
      · have ht_le : t ≤ (2 : ℝ) * n := by
          have h1 : t ≤ (n : ℝ) + 1 := by exact_mod_cast ht.2
          have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hrpow : t ^ (-x - 1) ≤ ((2 : ℝ) * n) ^ (-x - 1) :=
          Real.rpow_le_rpow (hn_pos.le.trans ht.1) ht_le hpos.le
        rw [Real.mul_rpow (by norm_num) hn_pos.le] at hrpow
        calc
          t ^ (-x - 1) ≤ (2 : ℝ) ^ (-x - 1) * (n : ℝ) ^ (-x - 1) := hrpow
          _ ≤ max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1) := by
            gcongr
            exact le_max_right _ _
  rw [heq, abs_mul, abs_of_nonneg hint_nonneg]
  calc
    |x| * ∫ t : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ), t ^ (-x - 1)
        ≤ |x| * (max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1)) := by gcongr
    _ = |x| * max 1 ((2 : ℝ) ^ (-x - 1)) * (n : ℝ) ^ (-x - 1) := by ring

/-- If eventually `‖coeffPartialSum f N‖ ≤ N ^ θ` and `θ < x`, then `DirichletConvergesAt f x`. -/
private theorem dirichletConvergesAt_of_eventually_norm_coeffPartialSum_le {f : ℕ → ℂ}
    {θ x : ℝ} (hθx : θ < x) (hbound : ∀ᶠ N : ℕ in atTop, ‖coeffPartialSum f N‖ ≤ (N : ℝ) ^ θ) :
    DirichletConvergesAt f (x : ℂ) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
  let N₁ := max N₀ 1
  let K₁ : ℝ := max 1 ((2 : ℝ) ^ (-x))
  let K₂ : ℝ := |x| * max 1 ((2 : ℝ) ^ (-x - 1))
  have hK₁_pos : 0 < K₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK₂_nonneg : 0 ≤ K₂ := mul_nonneg (abs_nonneg x) (le_trans zero_le_one (le_max_left _ _))
  have hlim1 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(x - θ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hθx)).comp tendsto_natCast_atTop_atTop
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ (θ - x - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcauchy_tail : CauchySeq (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (n : ℝ) ^ (θ - x - 1)) :=
    hsum.hasSum.tendsto_sum_nat.cauchySeq
  have hcauchy : CauchySeq (dirichletPartialSum f (x : ℂ)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M₁, hM₁⟩ := (Metric.tendsto_atTop.mp hlim1 (ε / (3 * (K₁ + 1))) (by positivity))
    obtain ⟨M₂, hM₂⟩ := (Metric.cauchySeq_iff.mp hcauchy_tail) (ε / (3 * (K₂ + 1))) (by positivity)
    refine ⟨max N₁ (max M₁ M₂), fun m hm n hn ↦ ?_⟩
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]
      exact this n hn m hm (le_of_not_ge hmn)
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · simpa using hε
    have hm_N₁ : N₁ ≤ m := (le_max_left _ _).trans hm
    have hm_N₀ : N₀ ≤ m := (le_max_left _ _).trans hm_N₁
    have hm_1 : 1 ≤ m := (le_max_right _ _).trans hm_N₁
    have hn_N₀ : N₀ ≤ n := hm_N₀.trans hlt.le
    have hm_M₁ : M₁ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
    have hn_M₁ : M₁ ≤ n := hm_M₁.trans hlt.le
    have hm_M₂ : M₂ ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
    have hn_M₂ : M₂ ≤ n := hm_M₂.trans hlt.le
    have hdiff_eq :
        dirichletPartialSum f (x : ℂ) n - dirichletPartialSum f (x : ℂ) m =
          coeffPartialSum f n * (((n : ℝ) ^ (-x) : ℝ) : ℂ) -
            coeffPartialSum f m * ((((m + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) +
              ∑ k ∈ Finset.Ico (m + 1) n,
                coeffPartialSum f k *
                  ((((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ)) := by
      rw [dirichletPartialSum_sub_eq_sum_Ioc f (x : ℂ) hlt.le]
      have hterm_congr :
          (∑ k ∈ Finset.Ioc m n, LSeries.term f (x : ℂ) k) =
            ∑ k ∈ Finset.Ioc m n, f k * (((k : ℝ) ^ (-x) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk1 : 1 ≤ k := by simp only [Finset.mem_Ioc] at hk; omega
        have hk0 : k ≠ 0 := Nat.ne_of_gt hk1
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
        rw [LSeries.term_of_ne_zero hk0, div_eq_mul_inv, ← Complex.cpow_neg,
          ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
          ← Complex.ofReal_cpow hk_pos.le]
      rw [hterm_congr]
      simpa [coeffPartialSum] using
        abel_summation_of_lt f (fun k ↦ (((k : ℝ) ^ (-x) : ℝ) : ℂ)) hlt
    have hn_term : ‖coeffPartialSum f n * (((n : ℝ) ^ (-x) : ℝ) : ℂ)‖ < ε / 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)]
      have h1 : ‖coeffPartialSum f n‖ * (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ θ * (n : ℝ) ^ (-x) :=
        mul_le_mul_of_nonneg_right (hN₀ n hn_N₀) (Real.rpow_nonneg n.cast_nonneg _)
      have h2 : (n : ℝ) ^ θ * (n : ℝ) ^ (-x) = (n : ℝ) ^ (-(x - θ)) := by
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le hm_1 hlt.le
        rw [← Real.rpow_add hn_pos, show θ + -x = -(x - θ) by ring]
      have h3 : (n : ℝ) ^ (-(x - θ)) < ε / (3 * (K₁ + 1)) := by
        have hd := hM₁ n hn_M₁
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)] at hd
      have h4 : ε / (3 * (K₁ + 1)) ≤ ε / 3 := by
        refine div_le_div_of_nonneg_left hε.le (by norm_num) ?_
        linarith
      exact (h1.trans_eq h2).trans_lt (h3.trans_le h4)
    have hm_term : ‖coeffPartialSum f m * ((((m + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ)‖ < ε / 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (m + 1).cast_nonneg _)]
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm_1
      have hm_rpow : ((m + 1 : ℕ) : ℝ) ^ (-x) ≤ K₁ * (m : ℝ) ^ (-x) := by
        rcases le_or_gt (-x) 0 with hx_neg | hx_pos
        · have hr : ((m + 1 : ℕ) : ℝ) ^ (-x) ≤ (m : ℝ) ^ (-x) :=
            Real.rpow_le_rpow_of_nonpos hm_pos (by exact_mod_cast Nat.le_succ m) hx_neg
          calc
            ((m + 1 : ℕ) : ℝ) ^ (-x) ≤ 1 * (m : ℝ) ^ (-x) := by simpa using hr
            _ ≤ K₁ * (m : ℝ) ^ (-x) := by gcongr; exact le_max_left _ _
        · have hm2 : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * m := by
            have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_1
            push_cast
            linarith
          have hr : ((m + 1 : ℕ) : ℝ) ^ (-x) ≤ ((2 : ℝ) * m) ^ (-x) :=
            Real.rpow_le_rpow (m + 1).cast_nonneg hm2 hx_pos.le
          rw [Real.mul_rpow (by norm_num) hm_pos.le] at hr
          calc
            ((m + 1 : ℕ) : ℝ) ^ (-x) ≤ (2 : ℝ) ^ (-x) * (m : ℝ) ^ (-x) := hr
            _ ≤ K₁ * (m : ℝ) ^ (-x) := by gcongr; exact le_max_right _ _
      have h1 : ‖coeffPartialSum f m‖ * ((m + 1 : ℕ) : ℝ) ^ (-x) ≤
          K₁ * (m : ℝ) ^ (-(x - θ)) := by
        calc
          ‖coeffPartialSum f m‖ * ((m + 1 : ℕ) : ℝ) ^ (-x)
              ≤ (m : ℝ) ^ θ * (K₁ * (m : ℝ) ^ (-x)) :=
            mul_le_mul (hN₀ m hm_N₀) hm_rpow (Real.rpow_nonneg (m + 1).cast_nonneg _)
              (Real.rpow_nonneg m.cast_nonneg _)
          _ = K₁ * ((m : ℝ) ^ θ * (m : ℝ) ^ (-x)) := by ring
          _ = K₁ * (m : ℝ) ^ (-(x - θ)) := by
            rw [← Real.rpow_add hm_pos, show θ + -x = -(x - θ) by ring]
      have h3 : (m : ℝ) ^ (-(x - θ)) < ε / (3 * (K₁ + 1)) := by
        have hd := hM₁ m hm_M₁
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg m.cast_nonneg _)] at hd
      calc
        ‖coeffPartialSum f m‖ * ((m + 1 : ℕ) : ℝ) ^ (-x) ≤ K₁ * (m : ℝ) ^ (-(x - θ)) := h1
        _ < K₁ * (ε / (3 * (K₁ + 1))) := by gcongr
        _ < (K₁ + 1) * (ε / (3 * (K₁ + 1))) := by
          gcongr
          linarith
        _ = ε / 3 := by field_simp [K₁]
    have htail_term :
        ‖∑ k ∈ Finset.Ico (m + 1) n,
            coeffPartialSum f k *
              ((((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ))‖ < ε / 3 := by
      have hsum_le :
          ‖∑ k ∈ Finset.Ico (m + 1) n,
              coeffPartialSum f k *
                ((((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ))‖ ≤
            K₂ * ∑ k ∈ Finset.Ico (m + 1) n, (k : ℝ) ^ (θ - x - 1) := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
        simp only [Finset.mem_Ico] at hk
        have hk1 : 1 ≤ k := by omega
        have hk_N₀ : N₀ ≤ k := hm_N₀.trans (by omega)
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          ‖coeffPartialSum f k‖ * |(k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x)|
              ≤ (k : ℝ) ^ θ * (K₂ * (k : ℝ) ^ (-x - 1)) :=
            mul_le_mul (hN₀ k hk_N₀) (norm_rpow_neg_sub_succ_le hk1 x) (abs_nonneg _)
              (Real.rpow_nonneg k.cast_nonneg _)
          _ = K₂ * ((k : ℝ) ^ θ * (k : ℝ) ^ (-x - 1)) := by ring
          _ = K₂ * (k : ℝ) ^ (θ - x - 1) := by
            rw [← Real.rpow_add hk_pos, show θ + (-x - 1) = θ - x - 1 by ring]
      have htail_eq :
          (∑ k ∈ Finset.Ico (m + 1) n, (k : ℝ) ^ (θ - x - 1)) =
            (∑ k ∈ Finset.range n, (k : ℝ) ^ (θ - x - 1)) -
              (∑ k ∈ Finset.range (m + 1), (k : ℝ) ^ (θ - x - 1)) := by
        rw [Finset.sum_Ico_eq_sub _ hlt]
      have htail_lt :
          (∑ k ∈ Finset.Ico (m + 1) n, (k : ℝ) ^ (θ - x - 1)) < ε / (3 * (K₂ + 1)) := by
        have hm1_M₂ : M₂ ≤ m + 1 := hm_M₂.trans (Nat.le_succ m)
        have hd := hM₂ n hn_M₂ (m + 1) hm1_M₂
        rw [Real.dist_eq, ← htail_eq] at hd
        exact (le_abs_self _).trans_lt hd
      calc
        ‖∑ k ∈ Finset.Ico (m + 1) n,
            coeffPartialSum f k *
              ((((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ))‖
            ≤ K₂ * ∑ k ∈ Finset.Ico (m + 1) n, (k : ℝ) ^ (θ - x - 1) := hsum_le
        _ ≤ K₂ * (ε / (3 * (K₂ + 1))) :=
          mul_le_mul_of_nonneg_left htail_lt.le hK₂_nonneg
        _ < (K₂ + 1) * (ε / (3 * (K₂ + 1))) := by
          gcongr
          linarith
        _ = ε / 3 := by field_simp [K₂]
    rw [dist_comm, dist_eq_norm, hdiff_eq]
    have h12 :
        ‖coeffPartialSum f n * (((n : ℝ) ^ (-x) : ℝ) : ℂ) -
            coeffPartialSum f m * ((((m + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ)‖ <
          ε / 3 + ε / 3 :=
      (norm_sub_le _ _).trans_lt (add_lt_add hn_term hm_term)
    have htotal := (norm_add_le _ _).trans_lt (add_lt_add h12 htail_term)
    linarith
  exact cauchySeq_tendsto_of_complete hcauchy

private theorem norm_le_rpow_of_log_div_log_lt {z : ℂ} {N : ℕ} (hN : 2 ≤ N) {θ : ℝ}
    (hlt : Real.log ‖z‖ / Real.log N < θ) : ‖z‖ ≤ (N : ℝ) ^ θ := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  rcases eq_or_ne z 0 with rfl | hz
  · simpa using Real.rpow_nonneg N.cast_nonneg θ
  · have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hlog_lt : Real.log ‖z‖ < θ * Real.log N := (div_lt_iff₀ hlogN).mp hlt
    have hexp := Real.exp_lt_exp.mpr hlog_lt
    rw [Real.exp_log hnorm_pos, mul_comm θ, ← Real.rpow_def_of_pos (zero_lt_one.trans hN1)] at hexp
    exact hexp.le

/-- Upper bound for `σ_c` via Cahen's limsup formula (unconditional on the sign of `σ_c`):
`abscissaOfConvergence f ≤ limsup (log ‖∑_{n ≤ N} f n‖ / log N)`. -/
theorem abscissaOfConvergence_le_limsup (f : ℕ → ℂ) :
    abscissaOfConvergence f ≤
      limsup (fun N : ℕ ↦ ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal)) atTop := by
  let L := limsup (fun N : ℕ ↦ ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal)) atTop
  change abscissaOfConvergence f ≤ L
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hθ : ∃ θ : ℝ, L < (θ : EReal) ∧ θ < x := by
    induction hL : L using EReal.rec with
    | bot => exact ⟨x - 1, EReal.bot_lt_coe (x - 1), by linarith⟩
    | coe c =>
      rw [hL] at hx
      have hcx : c < x := EReal.coe_lt_coe_iff.mp hx
      exact ⟨(c + x) / 2, EReal.coe_lt_coe_iff.mpr (by linarith), by linarith⟩
    | top =>
      rw [hL] at hx
      exact absurd hx not_top_lt
  obtain ⟨θ, hLθ, hθx⟩ := hθ
  have hev : ∀ᶠ N : ℕ in atTop,
      ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal) < (θ : EReal) :=
    Filter.eventually_lt_of_limsup_lt hLθ
  have hbound : ∀ᶠ N : ℕ in atTop, ‖coeffPartialSum f N‖ ≤ (N : ℝ) ^ θ := by
    filter_upwards [hev, eventually_ge_atTop 2] with N hNlt hN2
    exact norm_le_rpow_of_log_div_log_lt hN2 (EReal.coe_lt_coe_iff.mp hNlt)
  have hxconv := dirichletConvergesAt_of_eventually_norm_coeffPartialSum_le hθx hbound
  simpa using abscissaOfConvergence_le_of_dirichletConvergesAt hxconv

/-- Lower bound for Cahen's limsup when `0 ≤ σ_c`:
`limsup (log ‖∑_{n ≤ N} f n‖ / log N) ≤ abscissaOfConvergence f`. -/
theorem limsup_le_abscissaOfConvergence_of_nonneg {f : ℕ → ℂ}
    (hnonneg : 0 ≤ abscissaOfConvergence f) :
    limsup (fun N : ℕ ↦ ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal)) atTop ≤
      abscissaOfConvergence f := by
  let L := limsup (fun N : ℕ ↦ ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal)) atTop
  change L ≤ abscissaOfConvergence f
  refine EReal.le_of_forall_lt_iff_le.mp fun x hx ↦ ?_
  have hx_pos : 0 < x := EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt hnonneg hx)
  have hxconv : DirichletConvergesAt f (x : ℂ) :=
    dirichletConvergesAt_of_abscissaOfConvergence_lt_re (by simpa using hx)
  obtain ⟨B, hB_pos, hB⟩ := hxconv.exists_bound
  have hA_bound : ∀ N : ℕ, 1 ≤ N → ‖coeffPartialSum f N‖ ≤ 2 * B * (N : ℝ) ^ x := by
    intro N hN
    have hcoeff_eq :
        coeffPartialSum f N =
          ∑ n ∈ Finset.Ioc 0 N, LSeries.term f (x : ℂ) n * ((((n : ℝ) ^ x : ℝ) : ℂ)) := by
      rw [coeffPartialSum]
      have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
      rw [hIoc]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : n ≠ 0 := Nat.ne_of_gt hn1
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [LSeries.term_of_ne_zero hn0, ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow hn_pos.le]
      have hpow_ne : ((((n : ℝ) ^ x : ℝ) : ℂ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hn_pos x).ne'
      exact (div_mul_cancel₀ (f n) hpow_ne).symm
    have hab := abel_summation_of_lt (LSeries.term f (x : ℂ))
      (fun n ↦ ((((n : ℝ) ^ x : ℝ) : ℂ))) (Nat.pos_of_ne_zero (by omega : N ≠ 0))
    dsimp only at hab
    have hS0 : (∑ n ∈ Finset.Icc 1 0, LSeries.term f (x : ℂ) n) = 0 := by simp
    rw [hS0, zero_mul, sub_zero] at hab
    have hnorm_sum :
        ‖coeffPartialSum f N‖ ≤
          B * (N : ℝ) ^ x +
            ∑ n ∈ Finset.Ico 1 N, B * (((n + 1 : ℕ) : ℝ) ^ x - (n : ℝ) ^ x) := by
      rw [hcoeff_eq, hab]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg N.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_right (by simpa [dirichletPartialSum] using hB N)
          (Real.rpow_nonneg N.cast_nonneg _)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have hle : (n : ℝ) ^ x ≤ ((n + 1 : ℕ) : ℝ) ^ x :=
          Real.rpow_le_rpow n.cast_nonneg (by exact_mod_cast Nat.le_succ n) hx_pos.le
        rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
        exact mul_le_mul_of_nonneg_right (by simpa [dirichletPartialSum] using hB n)
          (sub_nonneg.mpr hle)
    have htel :
        (∑ n ∈ Finset.Ico 1 N, B * (((n + 1 : ℕ) : ℝ) ^ x - (n : ℝ) ^ x)) =
          B * ((N : ℝ) ^ x - (1 : ℝ) ^ x) := by
      have htel_neg :
          (∑ n ∈ Finset.Ico 1 N, ((n : ℝ) ^ x - ((n + 1 : ℕ) : ℝ) ^ x)) =
            (1 : ℝ) ^ x - (N : ℝ) ^ x :=
        sum_Ico_telescope (fun n ↦ (n : ℝ) ^ x) hN
      calc
        ∑ n ∈ Finset.Ico 1 N, B * (((n + 1 : ℕ) : ℝ) ^ x - (n : ℝ) ^ x)
            = B * ∑ n ∈ Finset.Ico 1 N, -((n : ℝ) ^ x - ((n + 1 : ℕ) : ℝ) ^ x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          ring
        _ = B * (-∑ n ∈ Finset.Ico 1 N, ((n : ℝ) ^ x - ((n + 1 : ℕ) : ℝ) ^ x)) := by
          rw [Finset.sum_neg_distrib]
        _ = B * ((N : ℝ) ^ x - (1 : ℝ) ^ x) := by
          rw [htel_neg]
          ring
    rw [htel] at hnorm_sum
    have h1_pos : (0 : ℝ) ≤ B * (1 : ℝ) ^ x := by positivity
    linarith
  have hLe_eps : ∀ ε : ℝ, 0 < ε → L ≤ ((x + ε : ℝ) : EReal) := by
    intro ε hε
    have hlog_div : Tendsto (fun N : ℕ ↦ Real.log (2 * B) / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hev_log : ∀ᶠ N : ℕ in atTop, Real.log (2 * B) / Real.log N < ε :=
      hlog_div.eventually (gt_mem_nhds hε)
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev_log, eventually_ge_atTop 2] with N hN_log hN2
    rw [EReal.coe_le_coe_iff]
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlogN : 0 < Real.log N := Real.log_pos hN1
    rcases eq_or_ne (coeffPartialSum f N) 0 with h0 | hne
    · rw [h0, norm_zero, Real.log_zero, zero_div]
      linarith
    · have hpos : 0 < ‖coeffPartialSum f N‖ := norm_pos_iff.mpr hne
      have hboundN : ‖coeffPartialSum f N‖ ≤ 2 * B * (N : ℝ) ^ x := hA_bound N (by omega)
      have hlog_le : Real.log ‖coeffPartialSum f N‖ ≤ Real.log (2 * B) + x * Real.log N := by
        calc
          Real.log ‖coeffPartialSum f N‖
              ≤ Real.log (2 * B * (N : ℝ) ^ x) := Real.log_le_log hpos hboundN
          _ = Real.log (2 * B) + Real.log ((N : ℝ) ^ x) :=
            Real.log_mul (by positivity) (Real.rpow_pos_of_pos (zero_lt_one.trans hN1) x).ne'
          _ = Real.log (2 * B) + x * Real.log N := by
            rw [Real.log_rpow (zero_lt_one.trans hN1)]
      calc
        Real.log ‖coeffPartialSum f N‖ / Real.log N
            ≤ (Real.log (2 * B) + x * Real.log N) / Real.log N :=
          div_le_div_of_nonneg_right hlog_le hlogN.le
        _ = Real.log (2 * B) / Real.log N + x := by
          rw [add_div, mul_div_cancel_right₀ x hlogN.ne']
        _ ≤ x + ε := by linarith
  induction hyL : L using EReal.rec with
  | bot => exact bot_le
  | coe c =>
    have hc_le : ∀ ε : ℝ, 0 < ε → c ≤ x + ε := fun ε hε ↦ by
      have := hLe_eps ε hε
      rw [hyL, EReal.coe_le_coe_iff] at this
      exact this
    have hcx : c ≤ x := le_of_forall_pos_le_add fun ε hε ↦ by
      simpa [add_comm] using hc_le ε hε
    exact EReal.coe_le_coe_iff.mpr hcx
  | top =>
    have htop := hLe_eps 1 zero_lt_one
    rw [hyL, top_le_iff] at htop
    exact absurd htop (EReal.coe_ne_top _)

/-- **Cahen's Formula**: whenever `0 ≤ abscissaOfConvergence f`, the abscissa of conditional
convergence equals `limsup (log ‖∑_{1 ≤ n ≤ N} f n‖ / log N)`. -/
theorem abscissaOfConvergence_eq_limsup_of_nonneg {f : ℕ → ℂ}
    (hnonneg : 0 ≤ abscissaOfConvergence f) :
    abscissaOfConvergence f =
      limsup (fun N : ℕ ↦ ((Real.log ‖coeffPartialSum f N‖ / Real.log N : ℝ) : EReal)) atTop :=
  le_antisymm (abscissaOfConvergence_le_limsup f) (limsup_le_abscissaOfConvergence_of_nonneg hnonneg)

end AnalyticNumberTheory.DirichletSeries
