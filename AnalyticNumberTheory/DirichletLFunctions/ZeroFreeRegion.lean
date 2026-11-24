import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Meromorphic.Order
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.BorelCaratheodory
import AnalyticNumberTheory.DirichletSeries.EulerProduct
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation
import AnalyticNumberTheory.RiemannZeta.PoleAndBounds
import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DirichletLFunctions.CharacterSums
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation

/-!
# Zero-Free Regions, Landau's Theorem, Page's Theorem, and Siegel's Theorem

This file establishes the classical zero-free theory for Dirichlet L-functions
`DirichletCharacter.LFunction χ s` and the effective and ineffective bounds for real
exceptional zeros and `L(1, χ)`:

1. Boundary non-vanishing on `Re s ≥ 1` and elementary upper/inverse bounds in `Re s > 1`.
2. Logarithmic-derivative Dirichlet series identities and the 3-4-1 trigonometric inequality.
3. Real character symmetries (`L(s̄, χ) = conj (L(s, χ))`), positivity `L(1, χ) > 0`, and
   sign/bound estimates for `riemannZeta` on `(0, 1)` and `(1, 2]`.
4. The classical de la Vallée Poussin zero-free region for principal, complex, and real
   Dirichlet characters (with at most one simple real zero for real non-principal `χ`),
   plus Cauchy derivative bounds near `s = 1` and `logDeriv` bounds inside the region.
5. Landau's two-character repulsion theorem.
6. An abstract Estermann Taylor-coefficient positivity engine powering both Page's effective
   theorem (lower bound for `L(1, χ)` and at most one exceptional primitive character below `Q`)
   and Siegel's theorem (`L(1, χ) ≥ C(ε) * q^(-ε)` and `β₁ ≤ 1 - c(ε) * q^(-ε)`).
-/

open Complex Filter MeromorphicOn Metric Real Set MeasureTheory
open scoped Topology Nat ArithmeticFunction ArithmeticFunction.Moebius LSeries

namespace AnalyticNumberTheory.DirichletLFunctions

section BoundaryAndGrowth

/-- Non-vanishing of `DirichletCharacter.LFunction χ s` on the closed half-plane `1 ≤ s.re`
whenever `χ ≠ 1` or `s ≠ 1`. -/
theorem LFunction_ne_zero_on_re_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) (h : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h hs

/-- Non-vanishing at `s = 1` for every non-principal Dirichlet character `χ ≠ 1`. -/
theorem LFunction_one_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-- The abscissa of absolute convergence of the Dirichlet L-series of `χ` is at most `1`. -/
theorem abscissaOfAbsConv_dirichletChar_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (fun n : ℕ ↦ χ n) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun σ hσ ↦ ?_
  have hσ1 : 1 < σ := hσ
  have hsum : Summable (fun n : ℕ ↦ ((n : ℝ) ^ σ)⁻¹) := Real.summable_nat_rpow_inv.2 hσ1
  refine Summable.of_norm_bounded hsum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (by linarith : σ ≠ 0)]
  · have hpos : (0 : ℝ) < (n : ℝ) ^ σ :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
    rw [LSeries.term_of_ne_zero hn, norm_div, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.ofReal_re, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (norm_char_le_one χ (n : ZMod q)) hpos.le

private lemma lseries_summable_of_one_lt_re_bound {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable f s ∧ ‖LSeries f s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hs_ne0 : s.re ≠ 0 := by linarith
  have hsum_nat : Summable (fun n : ℕ ↦ ((n : ℝ) ^ s.re)⁻¹) :=
    Real.summable_nat_rpow_inv.2 hs
  have hls : LSeriesSummable f s := by
    refine Summable.of_norm_bounded hsum_nat fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, Real.zero_rpow hs_ne0]
    · have hpos : (0 : ℝ) < (n : ℝ) ^ s.re :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
      rw [LSeries.term_of_ne_zero hn, norm_div, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        inv_eq_one_div]
      exact div_le_div_of_nonneg_right (hf n) hpos.le
  have hls_one : LSeriesSummable (1 : ℕ → ℂ) (s.re : ℂ) := by
    refine Summable.of_norm_bounded hsum_nat fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, Real.zero_rpow hs_ne0]
    · rw [LSeries.term_of_ne_zero hn, norm_div, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.ofReal_re, inv_eq_one_div]
      simp
  have hnorm : ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n‖ := by
    refine (norm_tsum_le_tsum_norm hls.norm).trans ?_
    refine hls.norm.tsum_le_tsum (fun n ↦ ?_) hls_one.norm
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hpos : (0 : ℝ) < (n : ℝ) ^ s.re :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
      simp only [LSeries.term_of_ne_zero hn, norm_div,
        norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re, Pi.one_apply, norm_one]
      exact div_le_div_of_nonneg_right (hf n) hpos.le
  have hzeta_eq : (∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n‖) =
      ‖riemannZeta (s.re : ℂ)‖ := by
    have hre_term : ∀ n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n‖ =
        (LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n).re := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      · simp only [LSeries.term_of_ne_zero hn, Pi.one_apply, one_div,
          norm_inv, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re]
        have hcpow : ((n : ℂ) ^ (s.re : ℂ)) = (((n : ℝ) ^ s.re : ℝ) : ℂ) := by
          rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n)]
        rw [hcpow, ← Complex.ofReal_inv, Complex.ofReal_re]
    simp_rw [hre_term]
    have htsum_re : (∑' n : ℕ, (LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n).re) =
        (LSeries (1 : ℕ → ℂ) (s.re : ℂ)).re := by
      simpa [LSeries] using (Complex.reCLM.map_tsum hls_one).symm
    have hzeta_s : LSeries (1 : ℕ → ℂ) (s.re : ℂ) = riemannZeta (s.re : ℂ) := by
      have h1 : (1 : ℝ) < ((s.re : ℂ)).re := by simpa using hs
      rw [zeta_eq_tsum_one_div_nat_cpow h1, LSeries]
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term, Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hs_ne0)]
      · simp [LSeries.term_of_ne_zero hn]
    have him0 : (LSeries (1 : ℕ → ℂ) (s.re : ℂ)).im = 0 := by
      have htsum_im : (LSeries (1 : ℕ → ℂ) (s.re : ℂ)).im =
          ∑' n : ℕ, (LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n).im := by
        simpa [LSeries] using Complex.imCLM.map_tsum hls_one
      have hall0 : ∀ n : ℕ, (LSeries.term (1 : ℕ → ℂ) (s.re : ℂ) n).im = 0 := by
        intro n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [LSeries.term]
        · have hcpow : ((n : ℂ) ^ (s.re : ℂ)) = (((n : ℝ) ^ s.re : ℝ) : ℂ) := by
            rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n)]
          simp [LSeries.term_of_ne_zero hn, hcpow, ← Complex.ofReal_inv]
      simp [htsum_im, hall0]
    have hre_nn : 0 ≤ (LSeries (1 : ℕ → ℂ) (s.re : ℂ)).re := by
      rw [← htsum_re]
      exact tsum_nonneg fun n ↦ by rw [← hre_term n]; exact norm_nonneg _
    have hlim_cast : LSeries (1 : ℕ → ℂ) (s.re : ℂ) =
        ((LSeries (1 : ℕ → ℂ) (s.re : ℂ)).re : ℂ) := Complex.ext rfl (by simp [him0])
    rw [htsum_re, ← hzeta_s]
    conv_rhs => rw [hlim_cast, Complex.norm_real, Real.norm_of_nonneg hre_nn]
  refine ⟨hls, hnorm.trans ?_⟩
  rw [hzeta_eq]
  have hz := AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_le_of_one_lt_re hs 0
  have hz_eq : ((s.re : ℂ) + ((0 : ℝ) : ℂ) * I) = (s.re : ℂ) := by simp
  rw [hz_eq] at hz
  have hfrac : s.re / (s.re - 1) = 1 + 1 / (s.re - 1) := by
    have hne : s.re - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
    field_simp [hne]
    ring
  linarith [hz]

/-- Elementary upper bound `‖L(s, χ)‖ ≤ 1 + 1 / (Re s - 1)` for `1 < Re s`. -/
theorem norm_LFunction_le_one_add_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact (lseries_summable_of_one_lt_re_bound (fun n ↦ norm_char_le_one χ (n : ZMod q)) hs).2

/-- Elementary upper bound `‖L(s, χ)⁻¹‖ ≤ 1 + 1 / (Re s - 1)` for `1 < Re s`, proved via the
Möbius Dirichlet inverse series `L(χ * μ, s)`. -/
theorem norm_inv_LFunction_le_one_add_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ 1 + 1 / (s.re - 1) := by
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs] at hmul
  have hinv : (DirichletCharacter.LFunction χ s)⁻¹ =
      LSeries (fun n : ℕ ↦ χ n * ((μ n : ℤ) : ℂ)) s :=
    inv_eq_of_mul_eq_one_right (by simpa [Pi.mul_def] using hmul)
  rw [hinv]
  refine (lseries_summable_of_one_lt_re_bound (fun n ↦ ?_) hs).2
  rw [norm_mul]
  have h1 : ‖χ n‖ ≤ 1 := norm_char_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  simpa using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one

/-- Uniform polynomial growth bound `‖L(s, χ)‖ ≤ (q + 48 q² + 2) (|Im s| + 2)²` on the
half-plane `1 / 2 ≤ Re s` for any non-principal character `χ ≠ 1`. -/
theorem norm_LFunction_re_ge_half_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (|s.im| + 2) ^ 2 := by
  have him2 : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have him_sq : 1 ≤ (|s.im| + 2) ^ 2 := one_le_pow₀ him2
  by_cases hs2 : s.re ≤ 2
  · have hbd := norm_LFunction_strip_poly_le hχ (by linarith : -(1 / 2 : ℝ) ≤ s.re) hs2
    refine hbd.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    linarith
  · push Not at hs2
    have hbd := norm_LFunction_le_one_add_inv χ (by linarith : 1 < s.re)
    have hinv : 1 / (s.re - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have h2 : ‖DirichletCharacter.LFunction χ s‖ ≤ 2 := by linarith
    have hq_nn : (0 : ℝ) ≤ q + 48 * (q : ℝ) ^ 2 := by positivity
    calc
      ‖DirichletCharacter.LFunction χ s‖ ≤ 2 := h2
      _ = 2 * 1 := by ring
      _ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (|s.im| + 2) ^ 2 :=
        mul_le_mul (by linarith) him_sq zero_le_one (by positivity)

end BoundaryAndGrowth

section LogDerivAndThreeFourOne

/-- View a Dirichlet character `χ : DirichletCharacter ℂ q` as a `ℕ →*₀ ℂ` vanishing at `0`. -/
private noncomputable def charHomWithZero {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else χ (n : ℕ)
  map_zero' := rfl
  map_one' := by simp
  map_mul' a b := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    simp [ha, hb, Nat.cast_mul, map_mul]

private lemma charHomWithZero_apply_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hn : n ≠ 0) : charHomWithZero χ n = χ n :=
  ite_eq_right_iff.mpr fun h ↦ absurd h hn

private lemma charHomWithZero_abscissa_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (charHomWithZero χ : ℕ → ℂ) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun σ hσ ↦ ?_
  have hsum := (lseries_summable_of_one_lt_re_bound (f := fun n : ℕ ↦ χ n)
    (fun n ↦ norm_char_le_one χ (n : ZMod q)) (s := (σ : ℂ)) (by simpa using hσ)).1
  refine hsum.congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp [LSeries.term_of_ne_zero hn, charHomWithZero_apply_ne_zero χ hn]

/-- For `1 < Re s`, the negative logarithmic derivative of `L(s, χ)` equals the Dirichlet series
`∑ χ(n) Λ(n) n^(-s)`, which converges absolutely at `s`. -/
theorem neg_logDeriv_LFunction_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ χ n * (Λ n : ℂ)) s ∧
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
        LSeries (fun n ↦ χ n * (Λ n : ℂ)) s := by
  have habs : LSeries.abscissaOfAbsConv (charHomWithZero χ : ℕ → ℂ) < s.re := by
    exact_mod_cast (charHomWithZero_abscissa_le_one χ).trans_lt (by exact_mod_cast hs)
  obtain ⟨hsum, heq⟩ :=
    AnalyticNumberTheory.DirichletSeries.LSeries_mul_vonMangoldt_eq_neg_logDeriv
      (charHomWithZero χ) habs
  have hloc : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries (charHomWithZero χ : ℕ → ℂ) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with w hw
    rw [DirichletCharacter.LFunction_eq_LSeries χ hw, LSeries, LSeries]
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · simp [LSeries.term_of_ne_zero hn, charHomWithZero_apply_ne_zero χ hn]
  have hderiv : deriv (DirichletCharacter.LFunction χ) s =
      deriv (LSeries (charHomWithZero χ : ℕ → ℂ)) s := hloc.deriv_eq
  have hval : DirichletCharacter.LFunction χ s = LSeries (charHomWithZero χ : ℕ → ℂ) s :=
    hloc.eq_of_nhds
  have hterm_eq : ∀ n : ℕ, LSeries.term (fun k ↦ (charHomWithZero χ) k * (Λ k : ℂ)) s n =
      LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · simp [LSeries.term_of_ne_zero hn, charHomWithZero_apply_ne_zero χ hn]
  have hsum' : LSeriesSummable (fun n ↦ χ n * (Λ n : ℂ)) s :=
    hsum.congr hterm_eq
  have hl_eq : LSeries (fun n ↦ (charHomWithZero χ) n * (Λ n : ℂ)) s =
      LSeries (fun n ↦ χ n * (Λ n : ℂ)) s := tsum_congr hterm_eq
  refine ⟨hsum', ?_⟩
  rw [hderiv, hval, ← heq, hl_eq]

/-- For `1 < Re s`, the negative logarithmic derivative of `riemannZeta` equals the Dirichlet
series `∑ Λ(n) n^(-s)`. -/
theorem neg_logDeriv_riemannZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Λ n : ℂ)) s ∧
      -deriv riemannZeta s / riemannZeta s = LSeries (fun n ↦ (Λ n : ℂ)) s := by
  have hmain := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) hs
  have hloc : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 s] riemannZeta := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with w hw
    have hw1 : w ≠ 1 := fun h ↦ by subst h; simp at hw
    rw [LFunction_one_eq_mul_riemannZeta hw1]
    simp
  have hderiv : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) s =
      deriv riemannZeta s := hloc.deriv_eq
  have hval : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s :=
    hloc.eq_of_nhds
  rw [hderiv, hval] at hmain
  simpa using hmain

private lemma term_three_four_one_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (_hσ : 1 < σ) (t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun k ↦ (Λ k : ℂ)) σ n).re +
        4 * (LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) (σ + t * I) n).re +
        (LSeries.term (fun k ↦ (χ ^ 2) k * (Λ k : ℂ)) (σ + (2 * t : ℝ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow_re : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
  have hterm_zeta : (LSeries.term (fun k ↦ (Λ k : ℂ)) σ n).re = Λ n * (n : ℝ) ^ (-σ) := by
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hpow_re,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsplit1 : (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t : ℂ) * I) := by
    rw [show -((σ : ℂ) + (t : ℂ) * I) = (-(σ : ℂ)) + (-(t : ℂ) * I) by ring,
      Complex.cpow_add _ _ hnc, hpow_re]
  have hsplit2 : (n : ℂ) ^ (-((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * I)) ^ 2 := by
    have h2 : -((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
        (-(σ : ℂ)) + ((-(t : ℂ) * I) + (-(t : ℂ) * I)) := by push_cast; ring
    rw [h2, Complex.cpow_add _ _ hnc, Complex.cpow_add _ _ hnc, hpow_re, sq]
  let u : ℂ := χ n * (n : ℂ) ^ (-(t : ℂ) * I)
  have hterm_chi : (LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) (σ + t * I) n).re =
      Λ n * (n : ℝ) ^ (-σ) * u.re := by
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hsplit1]
    have heq : χ n * (Λ n : ℂ) * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t : ℂ) * I)) =
        (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) * u := by
      dsimp only [u]
      push_cast
      ring
    rw [heq, Complex.re_ofReal_mul]
  have hterm_chi2 : (LSeries.term (fun k ↦ (χ ^ 2) k * (Λ k : ℂ)) (σ + (2 * t : ℝ) * I) n).re =
      Λ n * (n : ℝ) ^ (-σ) * (u ^ 2).re := by
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hsplit2]
    have hsq : (χ ^ 2) n = (χ n) ^ 2 := by simp [sq]
    have heq : (χ ^ 2) n * (Λ n : ℂ) *
        ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * I)) ^ 2) =
        (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) * (u ^ 2) := by
      rw [hsq]
      dsimp only [u]
      push_cast
      ring
    rw [heq, Complex.re_ofReal_mul]
  rw [hterm_zeta, hterm_chi, hterm_chi2]
  have hfac_nn : 0 ≤ Λ n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hn_pos.le _)
  have htrig : 0 ≤ 3 + 4 * u.re + (u ^ 2).re := by
    by_cases hcop : Nat.Coprime n q
    · have h1 : ‖χ n‖ = 1 := norm_char_eq_one_of_coprime χ hcop
      have h2 : ‖(n : ℂ) ^ (-(t : ℂ) * I)‖ = 1 := by
        rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
        simp
      have h2' : ‖(n : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by simpa [neg_mul] using h2
      have hu : ‖u‖ = 1 := by
        dsimp only [u]
        rw [norm_mul, h1, h2, mul_one]
      have hsq_sum : u.re ^ 2 + u.im ^ 2 = 1 := by
        have hns : Complex.normSq u = ‖u‖ ^ 2 := Complex.normSq_eq_norm_sq u
        rw [Complex.normSq_apply, hu, one_pow, ← sq, ← sq] at hns
        exact hns
      have hu2_re : (u ^ 2).re = 2 * u.re ^ 2 - 1 := by
        rw [sq, Complex.mul_re]
        linarith
      rw [hu2_re]
      nlinarith
    · have h0 : χ n = 0 := (char_nat_eq_zero_iff_not_coprime χ n).2 hcop
      simp [u, h0]
  have hcombine : 3 * (Λ n * (n : ℝ) ^ (-σ)) + 4 * (Λ n * (n : ℝ) ^ (-σ) * u.re) +
      Λ n * (n : ℝ) ^ (-σ) * (u ^ 2).re =
      (Λ n * (n : ℝ) ^ (-σ)) * (3 + 4 * u.re + (u ^ 2).re) := by ring
  rw [hcombine]
  exact mul_nonneg hfac_nn htrig

/-- The classical 3-4-1 trigonometric inequality for logarithmic derivatives on `1 < σ`:
`0 ≤ 3 Re(-ζ'/ζ(σ)) + 4 Re(-L'/L(σ + i t, χ)) + Re(-L'/L(σ + 2 i t, χ²))`. -/
theorem three_four_one_neg_logDeriv_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta σ / riemannZeta σ).re +
        4 * (-deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
          DirichletCharacter.LFunction χ (σ + t * I)).re +
        (-deriv (DirichletCharacter.LFunction (χ ^ 2)) (σ + (2 * t : ℝ) * I) /
          DirichletCharacter.LFunction (χ ^ 2) (σ + (2 * t : ℝ) * I)).re := by
  have h0 := neg_logDeriv_riemannZeta_eq_LSeries (s := (σ : ℂ)) (by simpa using hσ)
  have h1 := neg_logDeriv_LFunction_eq_LSeries χ (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  have h2 := neg_logDeriv_LFunction_eq_LSeries (χ ^ 2) (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by simpa using hσ)
  rw [h0.2, h1.2, h2.2]
  have hs0 : Summable (fun n ↦ (LSeries.term (fun k ↦ (Λ k : ℂ)) σ n).re) :=
    (Complex.reCLM.summable h0.1)
  have hs1 : Summable (fun n ↦ (LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) (σ + t * I) n).re) :=
    (Complex.reCLM.summable h1.1)
  have hs2 : Summable (fun n ↦ (LSeries.term (fun k ↦ (χ ^ 2) k * (Λ k : ℂ))
      (σ + (2 * t : ℝ) * I) n).re) :=
    (Complex.reCLM.summable h2.1)
  have hre0 : (LSeries (fun k ↦ (Λ k : ℂ)) σ).re =
      ∑' n, (LSeries.term (fun k ↦ (Λ k : ℂ)) σ n).re := by
    simpa [LSeries] using Complex.reCLM.map_tsum h0.1
  have hre1 : (LSeries (fun k ↦ χ k * (Λ k : ℂ)) (σ + t * I)).re =
      ∑' n, (LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) (σ + t * I) n).re := by
    simpa [LSeries] using Complex.reCLM.map_tsum h1.1
  have hre2 : (LSeries (fun k ↦ (χ ^ 2) k * (Λ k : ℂ)) (σ + (2 * t : ℝ) * I)).re =
      ∑' n, (LSeries.term (fun k ↦ (χ ^ 2) k * (Λ k : ℂ)) (σ + (2 * t : ℝ) * I) n).re := by
    simpa [LSeries] using Complex.reCLM.map_tsum h2.1
  rw [hre0, hre1, hre2, ← hs0.tsum_mul_left 3, ← hs1.tsum_mul_left 4,
    ← (hs0.mul_left 3).tsum_add (hs1.mul_left 4),
    ← ((hs0.mul_left 3).add (hs1.mul_left 4)).tsum_add hs2]
  exact tsum_nonneg fun n ↦ term_three_four_one_nonneg χ hσ t n

end LogDerivAndThreeFourOne

section RealCharactersAndZetaEstimates

private lemma differentiable_conj_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z : ℂ ↦ star (f (star z))) := by
  intro z
  have hfz : HasDerivAt f (deriv f (star z)) (star z) := (hf (star z)).hasDerivAt
  have ho_star : (fun w : ℂ ↦ star (f (star w)) - star (f (star z)) -
      (w - z) • star (deriv f (star z))) =o[𝓝 z] (fun w : ℂ ↦ w - z) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hc' := Asymptotics.isLittleO_iff.mp hfz.isLittleO hc
    filter_upwards [(continuous_star.continuousAt.tendsto : Tendsto star (𝓝 z) (𝓝 (star z))).eventually hc'] with w hw
    have h1 : ‖star (f (star w)) - star (f (star z)) - (w - z) • star (deriv f (star z))‖ =
        ‖f (star w) - f (star z) - (star w - star z) • deriv f (star z)‖ := by
      rw [show star (f (star w)) - star (f (star z)) - (w - z) • star (deriv f (star z)) =
          star (f (star w) - f (star z) - (star w - star z) • deriv f (star z)) by
        simp [smul_eq_mul, star_sub, star_mul, mul_comm]]
      exact norm_star _
    have h2 : ‖star w - star z‖ = ‖w - z‖ := by
      rw [← star_sub, norm_star]
    rwa [h1, ← h2]
  exact ((hasDerivAt_iff_isLittleO).2 ho_star).differentiableAt

/-- Conjugation symmetry `L(s̄, χ) = conj (L(s, χ))` for every real non-principal
Dirichlet character `χ`. -/
theorem LFunction_conj_of_isReal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsReal χ) (s : ℂ) :
    DirichletCharacter.LFunction χ (star s) = star (DirichletCharacter.LFunction χ s) := by
  have hstar_eq : star χ = χ := (isReal_iff_star_eq χ).mp hreal
  have hf1 : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hf2 : Differentiable ℂ (fun z : ℂ ↦ star (DirichletCharacter.LFunction χ (star z))) :=
    differentiable_conj_conj hf1
  have hagree : ∀ w ∈ {z : ℂ | 1 < z.re},
      DirichletCharacter.LFunction χ w = star (DirichletCharacter.LFunction χ (star w)) := by
    intro w hw
    have hw' : 1 < (star w).re := by simpa using hw
    rw [DirichletCharacter.LFunction_eq_LSeries χ hw,
      DirichletCharacter.LFunction_eq_LSeries χ hw']
    have hconj : star (∑' n : ℕ, LSeries.term (fun n : ℕ ↦ χ n) (star w) n) =
        ∑' n : ℕ, star (LSeries.term (fun n : ℕ ↦ χ n) (star w) n) := by
      simpa using Complex.conjCLE.map_tsum (f := fun n : ℕ ↦ LSeries.term (fun n : ℕ ↦ χ n) (star w) n)
    rw [LSeries, LSeries, hconj]
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have harg : Complex.arg (n : ℂ) ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn_pos.le]
      exact Real.pi_ne_zero.symm
    have hcpow : star ((n : ℂ) ^ (star w)) = (n : ℂ) ^ w := by
      have hc := Complex.cpow_conj (n : ℂ) (star w) harg
      simpa using hc.symm
    have hchi : star (χ n) = χ n := by
      have := congr_arg (fun ψ : DirichletCharacter ℂ q ↦ ψ n) hstar_eq
      simpa [star_char_apply] using this
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, star_div₀, hchi, hcpow]
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      fun z : ℂ ↦ star (DirichletCharacter.LFunction χ (star z)) := by
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
    exact hagree w hw
  have heq := (hf1.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hf2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ (2 : ℂ)) hev
  simpa using (congr_arg star (heq (Set.mem_univ s))).symm

/-- For a real non-principal character `χ`, `L(x, χ)` is real for every `x : ℝ`. -/
theorem LFunction_real_im_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsReal χ) (x : ℝ) :
    (DirichletCharacter.LFunction χ (x : ℂ)).im = 0 := by
  have h := LFunction_conj_of_isReal hχ hreal (x : ℂ)
  have hstar : star (x : ℂ) = (x : ℂ) := by simp
  rw [hstar] at h
  have him := congr_arg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

private lemma tsum_inv_sq_ge_two_le :
    (∑' k : ℕ, (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ 3 / 4 := by
  have hdom : ∀ k : ℕ, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ 2 ≤
      1 / ((k + 2 : ℝ) * (k + 3 : ℝ)) := by
    intro k
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hk3 : (0 : ℝ) < k + 3 := by positivity
    rw [one_div_le_one_div (by positivity) (by positivity)]
    push_cast
    nlinarith
  have hsum_tele : HasSum (fun k : ℕ ↦ 1 / (k + 2 : ℝ) - 1 / (k + 3 : ℝ)) (1 / 2 : ℝ) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / (k + 2 : ℝ) - 1 / (k + 3 : ℝ)) =
          1 / 2 - 1 / (N + 2 : ℝ) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring
      simp_rw [hpart]
      have h0 : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 2 : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using tendsto_const_nhds.sub h0
    · intro k
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hsum_k3 : Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ 2) := by
    have hs : Summable (fun k : ℕ ↦ ((k : ℝ) ^ (2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.2 (by norm_num)
    have hshift := (summable_nat_add_iff 3).2 hs
    refine hshift.congr fun k ↦ ?_
    simp [one_div]
  have hsum_k2 : Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).1 hsum_k3
  have hle_half : (∑' k : ℕ, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ 2) ≤ 1 / 2 := by
    rw [← hsum_tele.tsum_eq]
    refine hsum_k3.tsum_le_tsum (fun k ↦ ?_) hsum_tele.summable
    calc
      (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ 2 ≤ 1 / ((k + 2 : ℝ) * (k + 3 : ℝ)) := hdom k
      _ = 1 / (k + 2 : ℝ) - 1 / (k + 3 : ℝ) := by
          have hk2 : (k + 2 : ℝ) ≠ 0 := by positivity
          have hk3 : (k + 3 : ℝ) ≠ 0 := by positivity
          field_simp [hk2, hk3]
          ring
  rw [hsum_k2.tsum_eq_zero_add]
  have hshift_eq : (∑' k : ℕ, (1 : ℝ) / ((k + 1 + 2 : ℕ) : ℝ) ^ 2) =
      ∑' k : ℕ, (1 : ℝ) / ((k + 3 : ℕ) : ℝ) ^ 2 := by
    refine tsum_congr fun k ↦ ?_
    rw [show k + 1 + 2 = k + 3 by omega]
  rw [hshift_eq]
  norm_num at hle_half ⊢
  linarith

/-- For every real non-principal character `χ`, `L(1, χ) > 0`. -/
theorem LFunction_one_pos_of_isReal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsReal χ) :
    0 < (DirichletCharacter.LFunction χ 1).re := by
  have h2_ge : (1 / 4 : ℝ) ≤ (DirichletCharacter.LFunction χ 2).re := by
    have h2_eq := DirichletCharacter.LFunction_eq_LSeries χ (s := (2 : ℂ)) (by norm_num)
    have hsum : LSeriesSummable (fun n : ℕ ↦ χ n) (2 : ℂ) :=
      (lseries_summable_of_one_lt_re_bound (fun n ↦ norm_char_le_one χ (n : ZMod q))
        (by norm_num)).1
    have hsplit : LSeries (fun n : ℕ ↦ χ n) (2 : ℂ) =
        1 + ∑' k : ℕ, LSeries.term (fun n : ℕ ↦ χ n) 2 (k + 2) := by
      rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
      have hsum1 : Summable (fun n : ℕ ↦ LSeries.term (fun n : ℕ ↦ χ n) 2 (n + 1)) :=
        (summable_nat_add_iff 1).2 hsum
      rw [hsum1.tsum_eq_zero_add]
      have ht1 : LSeries.term (fun n : ℕ ↦ χ n) 2 1 = 1 := by simp [LSeries.term]
      rw [ht1, show (fun k : ℕ ↦ LSeries.term (fun n : ℕ ↦ χ n) 2 (k + 1 + 1)) =
        fun k : ℕ ↦ LSeries.term (fun n : ℕ ↦ χ n) 2 (k + 2) by rfl]
    have hsum2 : Summable (fun k : ℕ ↦ LSeries.term (fun n : ℕ ↦ χ n) 2 (k + 2)) :=
      (summable_nat_add_iff 2).2 hsum
    have hsum_bd : Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) := by
      have hs : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.2 (by norm_num)
      refine ((summable_nat_add_iff 2).2 hs).congr fun k ↦ ?_
      simp [one_div]
    have htail : ‖∑' k : ℕ, LSeries.term (fun n : ℕ ↦ χ n) 2 (k + 2)‖ ≤ 3 / 4 := by
      refine (norm_tsum_le_tsum_norm hsum2.norm).trans ?_
      refine (hsum2.norm.tsum_le_tsum (fun k ↦ ?_) hsum_bd).trans tsum_inv_sq_ge_two_le
      have hk : k + 2 ≠ 0 := by omega
      rw [LSeries.term_of_ne_zero hk, norm_div,
        show ((k + 2 : ℕ) : ℂ) ^ (2 : ℂ) = (((((k + 2 : ℕ) : ℝ) ^ 2 : ℝ)) : ℂ) by
          norm_cast,
        Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      exact div_le_div_of_nonneg_right (norm_char_le_one χ _) (sq_nonneg _)
    rw [h2_eq, hsplit, Complex.add_re, Complex.one_re]
    have hre_le : |(∑' k : ℕ, LSeries.term (fun n : ℕ ↦ χ n) 2 (k + 2)).re| ≤ 3 / 4 :=
      (Complex.abs_re_le_norm _).trans htail
    linarith [(abs_le.mp hre_le).1]
  by_contra hle
  push Not at hle
  have hne1 : DirichletCharacter.LFunction χ 1 ≠ 0 := LFunction_one_ne_zero hχ
  have him1 : (DirichletCharacter.LFunction χ 1).im = 0 := LFunction_real_im_zero hχ hreal 1
  have h1_lt : (DirichletCharacter.LFunction χ 1).re < 0 := by
    refine lt_of_le_of_ne hle fun hre0 ↦ hne1 ?_
    exact Complex.ext (by simpa using hre0) (by simpa using him1)
  have hcont : ContinuousOn (fun x : ℝ ↦ (DirichletCharacter.LFunction χ (x : ℂ)).re)
      (Set.Icc 1 2) :=
    ((Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal))).continuousOn
  have h0_mem : (0 : ℝ) ∈ Set.Icc ((DirichletCharacter.LFunction χ (1 : ℂ)).re)
      ((DirichletCharacter.LFunction χ (2 : ℂ)).re) :=
    ⟨by simpa using h1_lt.le, by linarith⟩
  obtain ⟨σ, hσ_mem, hσ_zero⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont h0_mem
  have hσ_ne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    LFunction_ne_zero_on_re_one χ (by simpa using hσ_mem.1) (Or.inl hχ)
  exact hσ_ne (Complex.ext (by simpa using hσ_zero) (by simpa using LFunction_real_im_zero hχ hreal σ))

/-- Entire completion `(s - 1) * riemannZeta s` defined via `riemannZeta₀`. -/
noncomputable def zetaOne (s : ℂ) : ℂ :=
  1 + (s - 1) * riemannZeta₀ s

/-- `zetaOne` is differentiable everywhere on `ℂ`. -/
theorem differentiable_zetaOne : Differentiable ℂ zetaOne :=
  (differentiable_const 1).add
    ((differentiable_id.sub_const 1).mul AnalyticNumberTheory.RiemannZeta.differentiable_riemannZeta₀_bridge)

/-- Away from `s = 1`, `zetaOne s = (s - 1) * riemannZeta s`. -/
theorem zetaOne_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) :
    zetaOne s = (s - 1) * riemannZeta s := by
  dsimp only [zetaOne]
  rw [← AnalyticNumberTheory.RiemannZeta.riemannZeta_sub_one_div_eq_riemannZeta₀ hs]
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hs']
  ring

/-- Value `zetaOne 1 = 1`. -/
@[simp]
theorem zetaOne_one : zetaOne 1 = 1 := by
  simp [zetaOne]

private lemma integral_Ioi_rpow_neg_sub_one {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 1) = 1 / σ := by
  have hint : IntegrableOn (fun u : ℝ ↦ u ^ (-σ - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (by linarith) zero_lt_one
  have htend := intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hint tendsto_id
  have heval : ∀ᶠ R in atTop, ∫ u in (1 : ℝ)..R, u ^ (-σ - 1) =
      (R ^ (-σ) - 1) / (-σ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 R := by
      rw [Set.uIcc_of_le hR]
      intro hmem
      linarith [hmem.1]
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have hpow_eq : -σ - 1 + 1 = -σ := by ring
    rw [hpow_eq, Real.one_rpow]
  have hlim : Tendsto (fun R : ℝ ↦ (R ^ (-σ) - 1) / (-σ)) atTop (𝓝 (1 / σ)) := by
    have hpow : Tendsto (fun R : ℝ ↦ R ^ (-σ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hσ
    have hsub := hpow.sub (tendsto_const_nhds (x := (1 : ℝ)))
    have hdiv := hsub.div_const (-σ)
    have hval : (0 - 1 : ℝ) / (-σ) = 1 / σ := by
      have hne : σ ≠ 0 := hσ.ne'
      field_simp [hne]
      ring
    rwa [hval] at hdiv
  exact tendsto_nhds_unique htend (hlim.congr' (heval.mono fun _ h ↦ h.symm))

/-- On the open interval `(0, 1)`, `riemannZeta (σ : ℂ)` is real and negative, satisfying
`(riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) < 0`. -/
theorem riemannZeta_neg_on_Ioo {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) :
    (riemannZeta (σ : ℂ)).im = 0 ∧ (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  have hσ_pos : 0 < σ := hσ.1
  have hσ_lt : σ < 1 := hσ.2
  have hs_pos : (0 : ℝ) < (σ : ℂ).re := by simpa using hσ_pos
  have hs_ne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ_lt.ne
  rw [AnalyticNumberTheory.RiemannZeta.riemannZeta_eq_eulerMaclaurin_of_re_pos hs_pos hs_ne]
  let f : ℝ → ℝ := fun u ↦
    AnalyticNumberTheory.AnalyticTools.Summation.sawtooth u * u ^ (-σ - 1)
  have hf_eq : ∀ u ∈ Set.Ioi (1 : ℝ),
      (AnalyticNumberTheory.AnalyticTools.Summation.sawtooth u : ℂ) *
        (u : ℂ) ^ (-(σ : ℂ) - 1) = (f u : ℂ) := by
    intro u hu
    have hu1 : (1 : ℝ) < u := Set.mem_Ioi.mp hu
    have hu_pos : (0 : ℝ) < u := by linarith
    have hcp : (u : ℂ) ^ (-(σ : ℂ) - 1) = ((u ^ (-σ - 1) : ℝ) : ℂ) := by
      rw [show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_cpow hu_pos.le]
    dsimp only [f]
    rw [hcp, Complex.ofReal_mul]
  have hdom : IntegrableOn (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (-σ - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -σ - 1) (by linarith) zero_lt_one).const_mul (1 / 2)
  have hsaw_le : ∀ u : ℝ,
      |AnalyticNumberTheory.AnalyticTools.Summation.sawtooth u| ≤ 1 / 2 := by
    intro u
    rw [AnalyticNumberTheory.AnalyticTools.Summation.sawtooth, abs_le]
    constructor <;> linarith [Int.fract_nonneg u, Int.fract_lt_one u]
  have hf_le : ∀ u ∈ Set.Ioi (1 : ℝ), ‖f u‖ ≤ (1 / 2 : ℝ) * u ^ (-σ - 1) := by
    intro u hu
    have hu1 : (1 : ℝ) < u := Set.mem_Ioi.mp hu
    have hu_pos : (0 : ℝ) < u := by linarith
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu_pos.le _)]
    exact mul_le_mul_of_nonneg_right (hsaw_le u) (Real.rpow_nonneg hu_pos.le _)
  have hf_meas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hcont : ContinuousOn (fun u : ℝ ↦ u ^ (-σ - 1)) (Set.Ioi 1) := by
      intro u hu
      have hu1 : (1 : ℝ) < u := Set.mem_Ioi.mp hu
      exact (continuousAt_rpow_const _ _ (Or.inl (by linarith : u ≠ 0))).continuousWithinAt
    have hfl : Measurable (fun u : ℝ ↦ AnalyticNumberTheory.AnalyticTools.Summation.sawtooth u) := by
      have heq : (fun u : ℝ ↦ AnalyticNumberTheory.AnalyticTools.Summation.sawtooth u) =
          fun u ↦ u - (⌊u⌋ : ℝ) - 1 / 2 := by
        ext u
        rw [AnalyticNumberTheory.AnalyticTools.Summation.sawtooth, Int.fract]
      rw [heq]
      exact (measurable_id.sub ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
        Int.measurable_floor)).sub measurable_const
    exact (hfl.aestronglyMeasurable).mul (hcont.aestronglyMeasurable measurableSet_Ioi)
  have hint_f : IntegrableOn f (Set.Ioi 1) :=
    hdom.mono' hf_meas (ae_restrict_of_forall_mem measurableSet_Ioi hf_le)
  have hint_eq : (∫ u in Set.Ioi (1 : ℝ),
      (AnalyticNumberTheory.AnalyticTools.Summation.sawtooth u : ℂ) *
        (u : ℂ) ^ (-(σ : ℂ) - 1)) = ((∫ u in Set.Ioi (1 : ℝ), f u : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hf_eq]
    simpa [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integral_comp_comm hint_f
  have hcast : 1 / ((σ : ℂ) - 1) + 1 / 2 -
      (σ : ℂ) * ((∫ u in Set.Ioi (1 : ℝ), f u : ℝ) : ℂ) =
      (((1 / (σ - 1) + 1 / 2 - σ * ∫ u in Set.Ioi (1 : ℝ), f u : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hint_eq, hcast]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  have hint_abs : |∫ u in Set.Ioi (1 : ℝ), f u| ≤ 1 / (2 * σ) := by
    calc
      |∫ u in Set.Ioi (1 : ℝ), f u| = ‖∫ u in Set.Ioi (1 : ℝ), f u‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ u in Set.Ioi (1 : ℝ), ‖f u‖ := MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * u ^ (-σ - 1) :=
        MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hdom
          (ae_restrict_of_forall_mem measurableSet_Ioi hf_le)
      _ = (1 / 2 : ℝ) * ∫ u in Set.Ioi (1 : ℝ), u ^ (-σ - 1) := MeasureTheory.integral_const_mul _ _
      _ = (1 / 2 : ℝ) * (1 / σ) := by rw [integral_Ioi_rpow_neg_sub_one hσ_pos]
      _ = 1 / (2 * σ) := by ring
  have hint_lo : -(1 / (2 * σ)) ≤ ∫ u in Set.Ioi (1 : ℝ), f u := (abs_le.mp hint_abs).1
  have hmul_le : -(σ * ∫ u in Set.Ioi (1 : ℝ), f u) ≤ 1 / 2 := by
    have hσ_ne : σ ≠ 0 := hσ_pos.ne'
    calc
      -(σ * ∫ u in Set.Ioi (1 : ℝ), f u) ≤ σ * (1 / (2 * σ)) := by nlinarith
      _ = 1 / 2 := by field_simp [hσ_ne]
  have hfrac : 1 / (σ - 1) + 1 / 2 + 1 / 2 = σ / (σ - 1) := by
    have hne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ_lt.ne
    field_simp [hne]
    ring
  linarith

/-- Uniform growth bound `‖zetaOne s‖ ≤ C * (|Im s| + 3)²` on the vertical strip `1 / 2 ≤ Re s ≤ 2`. -/
theorem norm_zetaOne_re_ge_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖zetaOne s‖ ≤ C * (|s.im| + 3) ^ 2 := by
  let K : Set ℂ := {w : ℂ | 1 / 2 ≤ w.re ∧ w.re ≤ 2 ∧ |w.im| ≤ 2}
  have hK_eq : K = Complex.re ⁻¹' Set.Icc (1 / 2 : ℝ) 2 ∩ Complex.im ⁻¹' Set.Icc (-2 : ℝ) 2 := by
    ext w
    simp [K, abs_le, and_assoc]
  have hK_closed : IsClosed K := by
    rw [hK_eq]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  have hK_bdd : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨4, fun w hw ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |w.re| ≤ 2 := abs_le.mpr ⟨by linarith [hw.1], hw.2.1⟩
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 2 + 2 := add_le_add hre hw.2.2
      _ = 4 := by norm_num
  have hK_comp : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK_closed, hK_bdd⟩
  have hK_nonempty : K.Nonempty := ⟨(1 : ℂ), by norm_num, by norm_num, by norm_num⟩
  obtain ⟨w₀, _, hw₀_max⟩ := hK_comp.exists_isMaxOn hK_nonempty
    (differentiable_zetaOne.continuous.norm.continuousOn)
  obtain ⟨C₁, hC₁, hbd₁⟩ := AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_re_ge_one_le
  obtain ⟨C₂, hC₂, hbd₂⟩ :=
    AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_critical_strip_le (ε := 1 / 4) (by norm_num)
  let C : ℝ := max (‖zetaOne w₀‖ + 1) (max C₁ C₂)
  refine ⟨C, by positivity, fun s hs_lo hs_hi ↦ ?_⟩
  by_cases him : |s.im| ≤ 2
  · have hsK : s ∈ K := ⟨hs_lo, hs_hi, him⟩
    have h9 : (1 : ℝ) ≤ (|s.im| + 3) ^ 2 := by nlinarith [abs_nonneg s.im]
    calc
      ‖zetaOne s‖ ≤ ‖zetaOne w₀‖ := hw₀_max hsK
      _ ≤ C := le_trans (by linarith) (le_max_left _ _)
      _ = C * 1 := by ring
      _ ≤ C * (|s.im| + 3) ^ 2 := mul_le_mul_of_nonneg_left h9 (by positivity)
  · push Not at him
    have hs1 : s ≠ 1 := fun h ↦ by subst h; norm_num at him
    rw [zetaOne_eq_sub_one_mul hs1, norm_mul]
    have hs_sub : ‖s - 1‖ ≤ |s.im| + 3 := by
      have hre : |s.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc
        ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| := Complex.norm_le_abs_re_add_abs_im (s - 1)
        _ = |s.re - 1| + |s.im| := by simp
        _ ≤ 1 + |s.im| := add_le_add hre le_rfl
        _ ≤ |s.im| + 3 := by linarith
    have hzeta_bd : ‖riemannZeta s‖ ≤ C * (|s.im| + 3) := by
      have hs_eq : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
      by_cases hre1 : 1 ≤ s.re
      · have hz : ‖riemannZeta s‖ ≤ C₁ * Real.log (|s.im| + 2) := by
          conv_lhs => rw [hs_eq]
          exact hbd₁ (σ := s.re) (t := s.im) hre1 him.le
        have hlog : Real.log (|s.im| + 2) ≤ |s.im| + 3 := by
          have := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg s.im] : 0 < |s.im| + 2)
          linarith
        calc
          ‖riemannZeta s‖ ≤ C₁ * Real.log (|s.im| + 2) := hz
          _ ≤ C₁ * (|s.im| + 3) := mul_le_mul_of_nonneg_left hlog hC₁.le
          _ ≤ C * (|s.im| + 3) :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
              (by linarith [abs_nonneg s.im])
      · push Not at hre1
        have hz : ‖riemannZeta s‖ ≤ C₂ * (|s.im| + 2) ^ ((1 - s.re) / 2 + 1 / 4) := by
          conv_lhs => rw [hs_eq]
          exact hbd₂ (σ := s.re) (t := s.im) ⟨by linarith, hre1.le⟩ (by linarith)
        have hpow_le : (|s.im| + 2) ^ ((1 - s.re) / 2 + 1 / 4) ≤ |s.im| + 3 := by
          have hbase : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
          have hexp : (1 - s.re) / 2 + 1 / 4 ≤ 1 := by linarith
          calc
            (|s.im| + 2) ^ ((1 - s.re) / 2 + 1 / 4) ≤ (|s.im| + 2) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hbase hexp
            _ = |s.im| + 2 := Real.rpow_one _
            _ ≤ |s.im| + 3 := by linarith
        calc
          ‖riemannZeta s‖ ≤ C₂ * (|s.im| + 2) ^ ((1 - s.re) / 2 + 1 / 4) := hz
          _ ≤ C₂ * (|s.im| + 3) := mul_le_mul_of_nonneg_left hpow_le hC₂.le
          _ ≤ C * (|s.im| + 3) :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _))
              (by linarith [abs_nonneg s.im])
    calc
      ‖s - 1‖ * ‖riemannZeta s‖ ≤ (|s.im| + 3) * (C * (|s.im| + 3)) :=
        mul_le_mul hs_sub hzeta_bd (norm_nonneg _) (by positivity)
      _ = C * (|s.im| + 3) ^ 2 := by ring

/-- Upper bound `Re (-ζ'/ζ(σ)) ≤ 1 / (σ - 1) + C_zeta` for real `σ ∈ (1, 2]`. -/
theorem neg_logDeriv_riemannZeta_real_le :
    ∃ C_zeta : ℝ, 0 < C_zeta ∧ ∀ σ ∈ Set.Ioc (1 : ℝ) 2,
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C_zeta := by
  have hcomp : IsCompact ((Complex.ofReal : ℝ → ℂ) '' Set.Icc (1 : ℝ) 2) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hne : ((Complex.ofReal : ℝ → ℂ) '' Set.Icc (1 : ℝ) 2).Nonempty :=
    ⟨(1 : ℂ), 1, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hcont_z : Continuous zetaOne := differentiable_zetaOne.continuous
  have hd_z : Differentiable ℂ (deriv zetaOne) := by
    have ha : AnalyticOnNhd ℂ zetaOne Set.univ :=
      differentiable_zetaOne.differentiableOn.analyticOnNhd isOpen_univ
    exact differentiableOn_univ.mp ha.deriv.differentiableOn
  have hne0 : ∀ z ∈ (Complex.ofReal : ℝ → ℂ) '' Set.Icc (1 : ℝ) 2, zetaOne z ≠ 0 := by
    rintro _ ⟨σ, hσ, rfl⟩
    rcases eq_or_lt_of_le hσ.1 with rfl | hσ1
    · simp
    · have hne1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne'
      rw [zetaOne_eq_sub_one_mul hne1]
      refine mul_ne_zero (sub_ne_zero.mpr hne1) ?_
      exact AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ1)
  obtain ⟨z₁, _, hz₁_min⟩ := hcomp.exists_isMinOn hne hcont_z.norm.continuousOn
  obtain ⟨z₂, _, hz₂_max⟩ := hcomp.exists_isMaxOn hne hd_z.continuous.norm.continuousOn
  have hm_pos : 0 < ‖zetaOne z₁‖ :=
    norm_pos_iff.mpr (hne0 z₁ ‹_›)
  let C_zeta : ℝ := (‖deriv zetaOne z₂‖ + 1) / ‖zetaOne z₁‖
  refine ⟨C_zeta, by positivity, fun σ hσ ↦ ?_⟩
  have hσ1 : 1 < σ := hσ.1
  have hσ_mem : (σ : ℂ) ∈ (Complex.ofReal : ℝ → ℂ) '' Set.Icc (1 : ℝ) 2 :=
    ⟨σ, ⟨hσ.1.le, hσ.2⟩, rfl⟩
  have hne_s : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne'
  have hloc : riemannZeta =ᶠ[𝓝 (σ : ℂ)] fun z ↦ zetaOne z / (z - 1) := by
    have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds hne_s] with z hz
    rw [zetaOne_eq_sub_one_mul hz]
    have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    field_simp [hz']
  have hld_eq : logDeriv riemannZeta (σ : ℂ) = logDeriv (fun z ↦ zetaOne z / (z - 1)) (σ : ℂ) := by
    simp only [logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]
  have hdiv_ld : logDeriv (fun z ↦ zetaOne z / (z - 1)) (σ : ℂ) =
      logDeriv zetaOne (σ : ℂ) - ((σ : ℂ) - 1)⁻¹ := by
    let lin : ℂ → ℂ := fun z ↦ z - 1
    have h1 : DifferentiableAt ℂ zetaOne (σ : ℂ) := differentiable_zetaOne _
    have h2 : DifferentiableAt ℂ lin (σ : ℂ) := differentiableAt_id.sub_const 1
    have hld := logDeriv_div (f := zetaOne) (g := lin) (σ : ℂ) (hne0 _ hσ_mem)
      (sub_ne_zero.mpr hne_s) h1 h2
    change logDeriv (zetaOne / lin) (σ : ℂ) = _
    simpa [lin, logDeriv_apply] using hld
  have hneg_ld : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) =
      ((σ : ℂ) - 1)⁻¹ - logDeriv zetaOne (σ : ℂ) := by
    rw [show -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) = -logDeriv riemannZeta (σ : ℂ) by
      simp [logDeriv_apply]; ring, hld_eq, hdiv_ld]
    ring
  have hinv_re : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      Complex.ofReal_re, one_div]
  have hld_norm : ‖logDeriv zetaOne (σ : ℂ)‖ ≤ C_zeta := by
    rw [logDeriv_apply, norm_div]
    have hnum : ‖deriv zetaOne (σ : ℂ)‖ ≤ ‖deriv zetaOne z₂‖ + 1 :=
      le_trans (hz₂_max hσ_mem) (by linarith)
    have hden : ‖zetaOne z₁‖ ≤ ‖zetaOne (σ : ℂ)‖ := hz₁_min hσ_mem
    exact div_le_div₀ (by positivity) hnum hm_pos hden
  have hld_re : -(logDeriv zetaOne (σ : ℂ)).re ≤ C_zeta :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hld_norm)
  rw [hneg_ld, Complex.sub_re, hinv_re]
  linarith

private lemma logDeriv_eulerFinset_le (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p)
    {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun w : ℂ ↦ ∏ p ∈ F, (1 - (p : ℂ) ^ (-w))) s ∧
      (∏ p ∈ F, (1 - (p : ℂ) ^ (-s))) ≠ 0 ∧
      ‖logDeriv (fun w : ℂ ↦ ∏ p ∈ F, (1 - (p : ℂ) ^ (-w))) s‖ ≤ ∑ p ∈ F, Real.log p := by
  classical
  induction F using Finset.induction with
  | empty =>
    refine ⟨differentiableAt_const 1, by simp, ?_⟩
    simp [logDeriv_const]
  | @insert p F hpF ih =>
    have hp : Nat.Prime p := hF p (Finset.mem_insert_self p F)
    have ih' := ih (fun q hq ↦ hF q (Finset.mem_insert_of_mem hq))
    let fp : ℂ → ℂ := fun w ↦ 1 - (p : ℂ) ^ (-w)
    let PF : ℂ → ℂ := fun w ↦ ∏ q ∈ F, (1 - (q : ℂ) ^ (-w))
    have hp_ne0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hfp_eq : fp = fun w ↦ 1 - Complex.exp (Complex.log (p : ℂ) * (-w)) := by
      ext w
      simp [fp, Complex.cpow_def_of_ne_zero hp_ne0]
    have hfp_deriv : HasDerivAt fp (Complex.log (p : ℂ) * (p : ℂ) ^ (-s)) s := by
      rw [hfp_eq]
      have harg : HasDerivAt (fun w : ℂ ↦ Complex.log (p : ℂ) * (-w)) (-Complex.log (p : ℂ)) s := by
        simpa using (hasDerivAt_id s).neg.const_mul (Complex.log (p : ℂ))
      have hexp := harg.cexp
      have hsub := (hasDerivAt_const s (1 : ℂ)).sub hexp
      convert hsub using 1
      rw [Complex.cpow_def_of_ne_zero hp_ne0]
      ring
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hp_two : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpow_norm : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
      rw [norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, Real.rpow_neg hp_pos.le]
      have hp_le : (2 : ℝ) ≤ (p : ℝ) ^ s.re := by
        calc
          (2 : ℝ) ≤ (p : ℝ) := hp_two
          _ = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (p : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hfp_norm : 1 / 2 ≤ ‖fp s‖ := by
      have hrev : ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ :=
        norm_sub_norm_le 1 ((p : ℂ) ^ (-s))
      rw [norm_one] at hrev
      exact le_trans (by linarith) hrev
    have hfp_ne : fp s ≠ 0 := norm_pos_iff.mp (by linarith)
    have hlog_p : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hp_pos.le]
    have hfp_ld : ‖logDeriv fp s‖ ≤ Real.log p := by
      rw [logDeriv_apply, hfp_deriv.deriv, norm_div, norm_mul, hlog_p, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg (by linarith))]
      have hnum : Real.log p * ‖(p : ℂ) ^ (-s)‖ ≤ Real.log p * (1 / 2) :=
        mul_le_mul_of_nonneg_left hpow_norm (Real.log_nonneg (by linarith))
      have hquot : (Real.log p * (1 / 2)) / ‖fp s‖ ≤ (Real.log p * (1 / 2)) / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (Real.log_nonneg (by linarith)) (by norm_num))
          (by norm_num) hfp_norm
      have h1 : (Real.log p * (1 / 2)) / (1 / 2 : ℝ) = Real.log p := by ring
      exact (div_le_div_of_nonneg_right hnum (by positivity)).trans (hquot.trans_eq h1)
    have hprod_eq : (fun w : ℂ ↦ ∏ q ∈ insert p F, (1 - (q : ℂ) ^ (-w))) =
        fun w : ℂ ↦ fp w * PF w := by
      ext w
      exact Finset.prod_insert hpF
    have hprod_s : (∏ q ∈ insert p F, (1 - (q : ℂ) ^ (-s))) = fp s * PF s :=
      Finset.prod_insert hpF
    rw [hprod_eq, hprod_s]
    refine ⟨hfp_deriv.differentiableAt.mul ih'.1, mul_ne_zero hfp_ne ih'.2.1, ?_⟩
    change ‖logDeriv (fp * PF) s‖ ≤ _
    rw [logDeriv_mul s hfp_ne ih'.2.1 hfp_deriv.differentiableAt ih'.1, Finset.sum_insert hpF]
    exact (norm_add_le _ _).trans (add_le_add hfp_ld ih'.2.2)

/-- For `1 < Re s` and `[NeZero q]`, the logarithmic derivative of `L(s, 1_q)` differs from
that of `riemannZeta` by at most `Real.log q`. -/
theorem norm_logDeriv_LFunction_one_sub_riemannZeta_le {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s -
      logDeriv riemannZeta s‖ ≤ Real.log q := by
  let P : ℂ → ℂ := fun w ↦ ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))
  have hP := logDeriv_eulerFinset_le q.primeFactors
    (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) hs
  have hloc : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      P * riemannZeta := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with w hw
    have hw1 : w ≠ 1 := fun h ↦ by subst h; simp at hw
    exact LFunction_one_eq_mul_riemannZeta hw1
  have hz_ne : riemannZeta s ≠ 0 :=
    AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re hs
  have hz_diff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (fun h ↦ by subst h; simp at hs)
  have hld_eq : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s =
      logDeriv (P * riemannZeta) s := by
    simp only [logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]
  rw [hld_eq, logDeriv_mul s hP.2.1 hz_ne hP.1 hz_diff, add_sub_cancel_right]
  have hsum_log : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
    have hprod_ne : ∀ p ∈ q.primeFactors, (p : ℝ) ≠ 0 :=
      fun p hp ↦ Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [← Real.log_prod hprod_ne]
    have hdvd : ∏ p ∈ q.primeFactors, p ∣ q := Nat.prod_primeFactors_dvd q
    have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdvd
    have hle' : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
      simpa [Nat.cast_prod] using hle
    have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, (p : ℝ) := by
      refine Finset.prod_pos fun p hp ↦ ?_
      exact Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
    exact Real.log_le_log hpos hle'
  exact hP.2.2.trans hsum_log

/-- For `1 < σ` (real), the real part of `logDeriv (LFunction χ) σ` (and the norm of its
real part) is bounded above by `Re (-ζ'/ζ(σ))`. -/
theorem norm_re_logDeriv_LFunction_le_neg_logDeriv_zeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    |((logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re)| ≤
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hL := neg_logDeriv_LFunction_eq_LSeries χ (s := (σ : ℂ)) (by simpa using hσ)
  have hZ := neg_logDeriv_riemannZeta_eq_LSeries (s := (σ : ℂ)) (by simpa using hσ)
  have hnorm_le : ‖-deriv (DirichletCharacter.LFunction χ) (σ : ℂ) /
      DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
    rw [hL.2, hZ.2]
    have hre_eq : (LSeries (fun n ↦ (Λ n : ℂ)) σ).re =
        ∑' n : ℕ, (LSeries.term (fun n ↦ (Λ n : ℂ)) σ n).re := by
      simpa [LSeries] using Complex.reCLM.map_tsum hZ.1
    have hsum_re : Summable (fun n ↦ (LSeries.term (fun n ↦ (Λ n : ℂ)) σ n).re) :=
      Complex.reCLM.summable hZ.1
    rw [hre_eq]
    refine (norm_tsum_le_tsum_norm hL.1.norm).trans ?_
    refine hL.1.norm.tsum_le_tsum (fun n ↦ ?_) hsum_re
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hpow : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
    have hterm_chi : ‖LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) σ n‖ =
        ‖χ n‖ * (Λ n * (n : ℝ) ^ (-σ)) := by
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hpow,
        mul_assoc, norm_mul, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg hn_pos.le _))]
    have hterm_zeta : (LSeries.term (fun k ↦ (Λ k : ℂ)) σ n).re = Λ n * (n : ℝ) ^ (-σ) := by
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hpow,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hterm_chi, hterm_zeta]
    exact mul_le_of_le_one_left
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hn_pos.le _))
      (norm_char_le_one χ (n : ZMod q))
  have hneg_eq : (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re =
      -(-deriv (DirichletCharacter.LFunction χ) (σ : ℂ) /
        DirichletCharacter.LFunction χ (σ : ℂ)).re := by
    simp [logDeriv_apply, neg_div]
  rw [hneg_eq, abs_neg]
  exact (Complex.abs_re_le_norm _).trans hnorm_le

end RealCharactersAndZetaEstimates

section ClassicalZeroFreeRegion

private lemma exists_small_delta (a B C ε : ℝ) (ha : 0 < a) (hB : 0 < B) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ a ∧ δ * C ≤ ε ∧ δ * Real.log (B / δ) ≤ ε := by
  let δ₁ : ℝ := ε / (C + 1)
  let δ₂ : ℝ := (ε / (2 * Real.sqrt B + 1)) ^ 2
  let δ : ℝ := min a (min δ₁ δ₂)
  have hδ₁ : 0 < δ₁ := div_pos hε (by linarith)
  have hδ₂ : 0 < δ₂ := sq_pos_of_pos (div_pos hε (by positivity))
  have hδ_pos : 0 < δ := lt_min ha (lt_min hδ₁ hδ₂)
  have hδ_le_a : δ ≤ a := min_le_left _ _
  have hδ_le_1 : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ_pos, hδ_le_a, ?_, ?_⟩
  · calc
      δ * C ≤ δ₁ * C := mul_le_mul_of_nonneg_right hδ_le_1 hC
      _ = ε * (C / (C + 1)) := by dsimp only [δ₁]; ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by linarith)).2 (by linarith)) hε.le
      _ = ε := mul_one ε
  · have hlog_sqrt : Real.log (B / δ) ≤ 2 * Real.sqrt (B / δ) := by
      have hpos : 0 < B / δ := div_pos hB hδ_pos
      have hspos : 0 < Real.sqrt (B / δ) := Real.sqrt_pos.mpr hpos
      have hsq : Real.sqrt (B / δ) * Real.sqrt (B / δ) = B / δ := Real.mul_self_sqrt hpos.le
      have h2 := Real.log_le_sub_one_of_pos hspos
      calc
        Real.log (B / δ) = Real.log (Real.sqrt (B / δ) * Real.sqrt (B / δ)) := by rw [hsq]
        _ = Real.log (Real.sqrt (B / δ)) + Real.log (Real.sqrt (B / δ)) :=
          Real.log_mul hspos.ne' hspos.ne'
        _ ≤ 2 * Real.sqrt (B / δ) := by linarith
    have hsqrt_le : Real.sqrt δ ≤ ε / (2 * Real.sqrt B + 1) := by
      have h := Real.sqrt_le_sqrt hδ_le_2
      rwa [Real.sqrt_sq (div_pos hε (by positivity)).le] at h
    calc
      δ * Real.log (B / δ) ≤ δ * (2 * Real.sqrt (B / δ)) :=
        mul_le_mul_of_nonneg_left hlog_sqrt hδ_pos.le
      _ = 2 * Real.sqrt B * Real.sqrt δ := by
          rw [Real.sqrt_div hB.le]
          have hsqd : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ_pos.le
          have hne : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ_pos).ne'
          calc
            δ * (2 * (Real.sqrt B / Real.sqrt δ))
              = (Real.sqrt δ * Real.sqrt δ) * (2 * (Real.sqrt B / Real.sqrt δ)) := by rw [hsqd]
            _ = 2 * Real.sqrt B * Real.sqrt δ := by field_simp [hne]
      _ ≤ 2 * Real.sqrt B * (ε / (2 * Real.sqrt B + 1)) :=
        mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
      _ = ε * ((2 * Real.sqrt B) / (2 * Real.sqrt B + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) hε.le
      _ = ε := mul_one ε

private lemma landau_LFunction_sphere_bound {q : ℕ} [NeZero q]
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {η : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4)
    (T : ℝ) :
    let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (T : ℂ) * I
    let M : ℝ := 408 * ((q : ℝ) * (|T| + 2)) ^ 2 / η
    ∀ w ∈ Metric.sphere z₀ (1 / 2 : ℝ), ‖DirichletCharacter.LFunction ψ w / DirichletCharacter.LFunction ψ z₀‖ ≤ M := by
  intro z₀ M w hw
  rw [Metric.mem_sphere, dist_eq_norm] at hw
  have hz₀_re : z₀.re = 1 + η := by simp [z₀]
  have hz₀_im : z₀.im = T := by simp [z₀]
  have hw_re : 1 / 2 ≤ w.re := by
    have hre : |w.re - z₀.re| ≤ 1 / 2 := by
      calc
        |w.re - z₀.re| = |(w - z₀).re| := by simp
        _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
        _ = 1 / 2 := hw
    rw [hz₀_re] at hre
    linarith [(abs_le.mp hre).1]
  have hw_im : |w.im| + 2 ≤ 2 * (|T| + 2) := by
    have him : |w.im - z₀.im| ≤ 1 / 2 := by
      calc
        |w.im - z₀.im| = |(w - z₀).im| := by simp
        _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
        _ = 1 / 2 := hw
    have hw_abs : |w.im| ≤ |T| + 1 / 2 := by
      rw [hz₀_im] at him
      have h1 := (abs_le.mp him).1
      have h2 := (abs_le.mp him).2
      rw [abs_le]
      constructor <;> linarith [neg_abs_le T, le_abs_self T]
    linarith [abs_nonneg T]
  have hLw : ‖DirichletCharacter.LFunction ψ w‖ ≤ 204 * ((q : ℝ) * (|T| + 2)) ^ 2 := by
    have hbd := norm_LFunction_re_ge_half_le hψ hw_re
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    have hq_poly : (q : ℝ) + 48 * (q : ℝ) ^ 2 + 2 ≤ 51 * (q : ℝ) ^ 2 := by nlinarith
    have him_sq : (|w.im| + 2) ^ 2 ≤ 4 * (|T| + 2) ^ 2 := by
      calc
        (|w.im| + 2) ^ 2 ≤ (2 * (|T| + 2)) ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg w.im, abs_nonneg T]) hw_im
        _ = 4 * (|T| + 2) ^ 2 := by ring
    calc
      ‖DirichletCharacter.LFunction ψ w‖ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (|w.im| + 2) ^ 2 := hbd
      _ ≤ (51 * (q : ℝ) ^ 2) * (4 * (|T| + 2) ^ 2) :=
        mul_le_mul hq_poly him_sq (sq_nonneg _) (by positivity)
      _ = 204 * ((q : ℝ) * (|T| + 2)) ^ 2 := by ring
  have hinv : ‖(DirichletCharacter.LFunction ψ z₀)⁻¹‖ ≤ 2 / η := by
    have hz₀_gt1 : 1 < z₀.re := by rw [hz₀_re]; linarith
    have h1 := norm_inv_LFunction_le_one_add_inv ψ hz₀_gt1
    rw [hz₀_re, show 1 + η - 1 = η by ring] at h1
    have h1_le : (1 : ℝ) ≤ 1 / η := (one_le_div hη_pos).2 (by linarith)
    have h2 : 1 + 1 / η ≤ 2 / η := by rw [show (2 : ℝ) / η = 1 / η + 1 / η by ring]; linarith
    linarith
  rw [div_eq_mul_inv, norm_mul]
  calc
    ‖DirichletCharacter.LFunction ψ w‖ * ‖(DirichletCharacter.LFunction ψ z₀)⁻¹‖
      ≤ (204 * ((q : ℝ) * (|T| + 2)) ^ 2) * (2 / η) :=
        mul_le_mul hLw hinv (norm_nonneg _) (by positivity)
    _ = M := by ring

private lemma landau_LFunction_center_le {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    (hψ : ψ ≠ 1) {η : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4) (T : ℝ) :
    -(logDeriv (DirichletCharacter.LFunction ψ) (((1 + η : ℝ) : ℂ) + (T : ℂ) * I)).re ≤
      8 * (Real.log (408 / η) + 2 * Real.log ((q : ℝ) * (|T| + 2))) := by
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (T : ℂ) * I
  let M : ℝ := 408 * ((q : ℝ) * (|T| + 2)) ^ 2 / η
  have hz₀_re : z₀.re = 1 + η := by simp [z₀]
  have hz₀_ne : DirichletCharacter.LFunction ψ z₀ ≠ 0 :=
    LFunction_ne_zero_on_re_one ψ (by rw [hz₀_re]; linarith) (Or.inl hψ)
  have hlandau :=
    AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.landau_neg_re_logDeriv_center_le
      (f := DirichletCharacter.LFunction ψ) (z₀ := z₀) (R := 1 / 2) (M := M)
      (by norm_num)
      (((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd
        isOpen_univ).mono (Set.subset_univ _))
      hz₀_ne
      (landau_LFunction_sphere_bound hψ hη_pos hη_le T)
      (fun ρ _ hρ_zero ↦ by
        by_contra hlt
        push Not at hlt
        rw [hz₀_re] at hlt
        exact LFunction_ne_zero_on_re_one ψ (by linarith) (Or.inl hψ) hρ_zero)
  have hlogM : Real.log M = Real.log (408 / η) + 2 * Real.log ((q : ℝ) * (|T| + 2)) := by
    dsimp only [M]
    have hq_pos : (0 : ℝ) < (q : ℝ) * (|T| + 2) := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      positivity
    rw [show 408 * ((q : ℝ) * (|T| + 2)) ^ 2 / η = (408 / η) * ((q : ℝ) * (|T| + 2)) ^ 2 by ring,
      Real.log_mul (by positivity) (pow_ne_zero 2 hq_pos.ne'), Real.log_pow]
    push_cast
    ring
  have h4 : (4 / (1 / 2 : ℝ)) * Real.log M =
      8 * (Real.log (408 / η) + 2 * Real.log ((q : ℝ) * (|T| + 2))) := by
    rw [hlogM]; ring
  rw [h4] at hlandau
  exact hlandau

private lemma landau_LFunction_center_sub_zero_le {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    (hψ : ψ ≠ 1) {η : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4) (T : ℝ)
    {ρ : ℂ} (hρ_mem : ρ ∈ Metric.closedBall (((1 + η : ℝ) : ℂ) + (T : ℂ) * I) (1 / 4 : ℝ))
    (hρ_zero : DirichletCharacter.LFunction ψ ρ = 0) :
    -(logDeriv (DirichletCharacter.LFunction ψ) (((1 + η : ℝ) : ℂ) + (T : ℂ) * I)).re ≤
      8 * (Real.log (408 / η) + 2 * Real.log ((q : ℝ) * (|T| + 2))) -
        (((((1 + η : ℝ) : ℂ) + (T : ℂ) * I - ρ)⁻¹).re) := by
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (T : ℂ) * I
  let M : ℝ := 408 * ((q : ℝ) * (|T| + 2)) ^ 2 / η
  have hz₀_re : z₀.re = 1 + η := by simp [z₀]
  have hz₀_ne : DirichletCharacter.LFunction ψ z₀ ≠ 0 :=
    LFunction_ne_zero_on_re_one ψ (by rw [hz₀_re]; linarith) (Or.inl hψ)
  have hρ_mem' : ρ ∈ Metric.closedBall z₀ ((1 / 2 : ℝ) / 2) := by
    convert hρ_mem using 2
    norm_num
  have hlandau :=
    AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.landau_neg_re_logDeriv_center_le_sub_zero
      (f := DirichletCharacter.LFunction ψ) (z₀ := z₀) (R := 1 / 2) (M := M)
      (by norm_num)
      (((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd
        isOpen_univ).mono (Set.subset_univ _))
      hz₀_ne
      (landau_LFunction_sphere_bound hψ hη_pos hη_le T)
      (fun w _ hw_zero ↦ by
        by_contra hlt
        push Not at hlt
        rw [hz₀_re] at hlt
        exact LFunction_ne_zero_on_re_one ψ (by linarith) (Or.inl hψ) hw_zero)
      hρ_mem' hρ_zero
  have hlogM : Real.log M = Real.log (408 / η) + 2 * Real.log ((q : ℝ) * (|T| + 2)) := by
    dsimp only [M]
    have hq_pos : (0 : ℝ) < (q : ℝ) * (|T| + 2) := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      positivity
    rw [show 408 * ((q : ℝ) * (|T| + 2)) ^ 2 / η = (408 / η) * ((q : ℝ) * (|T| + 2)) ^ 2 by ring,
      Real.log_mul (by positivity) (pow_ne_zero 2 hq_pos.ne'), Real.log_pow]
    push_cast
    ring
  have h4 : (4 / (1 / 2 : ℝ)) * Real.log M =
      8 * (Real.log (408 / η) + 2 * Real.log ((q : ℝ) * (|T| + 2))) := by
    rw [hlogM]; ring
  rw [h4] at hlandau
  exact hlandau

private lemma landau_LFunction_center_sub_two_zeros_le {q : ℕ} [NeZero q]
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {η : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4)
    {ρ₁ ρ₂ : ℂ} (hρ₁_mem : ρ₁ ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ))
    (hρ₂_mem : ρ₂ ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ))
    (hρ₁ : DirichletCharacter.LFunction ψ ρ₁ = 0)
    (hρ₂ : (ρ₂ ≠ ρ₁ ∧ DirichletCharacter.LFunction ψ ρ₂ = 0) ∨
      (ρ₂ = ρ₁ ∧ deriv (DirichletCharacter.LFunction ψ) ρ₁ = 0)) :
    -(logDeriv (DirichletCharacter.LFunction ψ) ((1 + η : ℝ) : ℂ)).re ≤
      8 * (Real.log (408 / η) + 2 * Real.log (2 * (q : ℝ))) -
        (((((1 + η : ℝ) : ℂ) - ρ₁)⁻¹).re) - (((((1 + η : ℝ) : ℂ) - ρ₂)⁻¹).re) := by
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ)
  let M : ℝ := 408 * ((q : ℝ) * (|(0 : ℝ)| + 2)) ^ 2 / η
  let g : ℂ → ℂ := dslope (DirichletCharacter.LFunction ψ) ρ₁
  have hf_diff : Differentiable ℂ (DirichletCharacter.LFunction ψ) :=
    DirichletCharacter.differentiable_LFunction hψ
  have hg_diff : Differentiable ℂ g := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (isOpen_univ.mem_nhds (Set.mem_univ ρ₁))).mpr
      hf_diff.differentiableOn
  have hz₀_re : z₀.re = 1 + η := by simp [z₀]
  have hz₀_ne : DirichletCharacter.LFunction ψ z₀ ≠ 0 :=
    LFunction_ne_zero_on_re_one ψ (by rw [hz₀_re]; linarith) (Or.inl hψ)
  have hρ₁_re_lt : ρ₁.re < 1 := by
    by_contra hle
    push Not at hle
    exact LFunction_ne_zero_on_re_one ψ hle (Or.inl hψ) hρ₁
  have hne_z₀ : z₀ ≠ ρ₁ := fun h ↦ by
    have : z₀.re = ρ₁.re := congr_arg Complex.re h
    rw [hz₀_re] at this
    linarith
  have hg_val : ∀ w : ℂ, w ≠ ρ₁ → g w = (w - ρ₁)⁻¹ * DirichletCharacter.LFunction ψ w := by
    intro w hw
    dsimp only [g]
    rw [dslope_of_ne _ hw, slope_def_module, hρ₁, sub_zero, smul_eq_mul]
  have hgz₀_ne : g z₀ ≠ 0 := by
    rw [hg_val z₀ hne_z₀]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hne_z₀)) hz₀_ne
  have hg_sphere : ∀ w ∈ Metric.sphere z₀ (1 / 2 : ℝ), ‖g w / g z₀‖ ≤ M := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hdist1 : ‖z₀ - ρ₁‖ ≤ 1 / 4 := by
      have h := hρ₁_mem
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at h
      exact h
    have hdist2 : 1 / 4 ≤ ‖w - ρ₁‖ := by
      have htri : ‖w - z₀‖ ≤ ‖w - ρ₁‖ + ‖z₀ - ρ₁‖ := by
        calc
          ‖w - z₀‖ = ‖(w - ρ₁) - (z₀ - ρ₁)‖ := by ring_nf
          _ ≤ ‖w - ρ₁‖ + ‖z₀ - ρ₁‖ := norm_sub_le _ _
      linarith
    have hw_ne : w ≠ ρ₁ := fun h ↦ by
      rw [h, sub_self, norm_zero] at hdist2
      linarith
    have hfac : ‖(z₀ - ρ₁) / (w - ρ₁)‖ ≤ 1 := by
      rw [norm_div, div_le_one (by linarith)]
      exact hdist1.trans hdist2
    have hratio : g w / g z₀ = ((z₀ - ρ₁) / (w - ρ₁)) *
        (DirichletCharacter.LFunction ψ w / DirichletCharacter.LFunction ψ z₀) := by
      rw [hg_val w hw_ne, hg_val z₀ hne_z₀]
      have h1 : w - ρ₁ ≠ 0 := sub_ne_zero.mpr hw_ne
      have h2 : z₀ - ρ₁ ≠ 0 := sub_ne_zero.mpr hne_z₀
      field_simp [h1, h2, hz₀_ne]
    rw [hratio, norm_mul]
    have hw0 : w ∈ Metric.sphere (((1 + η : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) (1 / 2 : ℝ) := by
      simpa [z₀] using hw
    have hLsph := landau_LFunction_sphere_bound hψ hη_pos hη_le 0 w hw0
    have hLsph' : ‖DirichletCharacter.LFunction ψ w / DirichletCharacter.LFunction ψ z₀‖ ≤ M := by
      simpa [z₀, M] using hLsph
    calc
      ‖(z₀ - ρ₁) / (w - ρ₁)‖ * ‖DirichletCharacter.LFunction ψ w / DirichletCharacter.LFunction ψ z₀‖
        ≤ 1 * M := mul_le_mul hfac hLsph' (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have hg_zero₂ : g ρ₂ = 0 := by
    rcases hρ₂ with ⟨hne, hz⟩ | ⟨rfl, hd⟩
    · rw [hg_val ρ₂ hne, hz, mul_zero]
    · dsimp only [g]
      rw [dslope_same, hd]
  have hρ₂_mem' : ρ₂ ∈ Metric.closedBall z₀ ((1 / 2 : ℝ) / 2) := by
    convert hρ₂_mem using 2
    norm_num
  have hlandau_g :=
    AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.landau_neg_re_logDeriv_center_le_sub_zero
      (f := g) (z₀ := z₀) (R := 1 / 2) (M := M)
      (by norm_num)
      ((hg_diff.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _))
      hgz₀_ne hg_sphere
      (fun w _ hw_zero ↦ by
        by_contra hlt
        push Not at hlt
        rw [hz₀_re] at hlt
        have hw_gt : 1 < w.re := by linarith
        have hw_ne : w ≠ ρ₁ := fun h ↦ by
          have : w.re = ρ₁.re := congr_arg Complex.re h
          linarith
        rw [hg_val w hw_ne] at hw_zero
        have hLw := (mul_eq_zero.mp hw_zero).resolve_left (inv_ne_zero (sub_ne_zero.mpr hw_ne))
        exact LFunction_ne_zero_on_re_one ψ (by linarith) (Or.inl hψ) hLw)
      hρ₂_mem' hg_zero₂
  have hloc : DirichletCharacter.LFunction ψ =ᶠ[𝓝 z₀] fun w ↦ (w - ρ₁) * g w := by
    filter_upwards with w
    by_cases hw : w = ρ₁
    · subst hw
      simp [hρ₁]
    · rw [hg_val w hw]
      have hne : w - ρ₁ ≠ 0 := sub_ne_zero.mpr hw
      field_simp [hne]
  have hld_f : logDeriv (DirichletCharacter.LFunction ψ) z₀ = (z₀ - ρ₁)⁻¹ + logDeriv g z₀ := by
    let lin : ℂ → ℂ := fun w ↦ w - ρ₁
    have hloc' : DirichletCharacter.LFunction ψ =ᶠ[𝓝 z₀] (lin * g) := hloc
    have h1 : logDeriv (DirichletCharacter.LFunction ψ) z₀ = logDeriv (lin * g) z₀ := by
      simp only [logDeriv_apply, hloc'.deriv_eq, hloc'.eq_of_nhds]
    have hlin : DifferentiableAt ℂ lin z₀ := differentiableAt_id.sub_const ρ₁
    rw [h1, logDeriv_mul (f := lin) (g := g) z₀ (sub_ne_zero.mpr hne_z₀) hgz₀_ne hlin (hg_diff z₀)]
    simp [lin, logDeriv_apply]
  have hlogM : Real.log M = Real.log (408 / η) + 2 * Real.log (2 * (q : ℝ)) := by
    dsimp only [M]
    have hq_pos : (0 : ℝ) < 2 * (q : ℝ) := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      positivity
    rw [show 408 * ((q : ℝ) * (|(0 : ℝ)| + 2)) ^ 2 / η = (408 / η) * (2 * (q : ℝ)) ^ 2 by
      simp; ring,
      Real.log_mul (by positivity) (pow_ne_zero 2 hq_pos.ne'), Real.log_pow]
    push_cast
    ring
  rw [hld_f, Complex.add_re, neg_add]
  have h4 : (4 / (1 / 2 : ℝ)) * Real.log M =
      8 * (Real.log (408 / η) + 2 * Real.log (2 * (q : ℝ))) := by
    rw [hlogM]
    ring
  rw [h4] at hlandau_g
  dsimp only [z₀] at hlandau_g ⊢
  linarith [hlandau_g]

private lemma landau_zetaOne_center_exists :
    ∃ C_z1 : ℝ, 1 ≤ C_z1 ∧ ∀ {η : ℝ}, 0 < η → η ≤ 1 / 4 → ∀ T : ℝ,
      -(logDeriv zetaOne (((1 + η : ℝ) : ℂ) + (T : ℂ) * I)).re ≤
        8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3)) := by
  obtain ⟨C, hC_pos, hbd⟩ := norm_zetaOne_re_ge_half_le
  let C_z1 : ℝ := max 1 (32 * C)
  refine ⟨C_z1, le_max_left _ _, fun {η} hη_pos hη_le T ↦ ?_⟩
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = 1 + η := by simp [z₀]
  have hz₀_im : z₀.im = T := by simp [z₀]
  have hz₀_1_lt : 1 < z₀.re := by rw [hz₀_re]; linarith
  have hz₀_ne1 : z₀ ≠ 1 := fun h ↦ by simp [h] at hz₀_1_lt
  have hzeta_ne : riemannZeta z₀ ≠ 0 :=
    AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re hz₀_1_lt
  have hz₀_ne0 : zetaOne z₀ ≠ 0 := by
    rw [zetaOne_eq_sub_one_mul hz₀_ne1]
    exact mul_ne_zero (sub_ne_zero.mpr hz₀_ne1) hzeta_ne
  have hinv_z₀ : ‖(zetaOne z₀)⁻¹‖ ≤ 2 / η ^ 2 := by
    rw [zetaOne_eq_sub_one_mul hz₀_ne1, mul_inv, norm_mul]
    have hsub_ge : η ≤ ‖z₀ - 1‖ := by
      calc
        η = |(z₀ - 1).re| := by simp [hz₀_re, abs_of_pos hη_pos]
        _ ≤ ‖z₀ - 1‖ := Complex.abs_re_le_norm (z₀ - 1)
    have h1 : ‖(z₀ - 1)⁻¹‖ ≤ 1 / η := by
      rw [norm_inv, one_div]
      exact inv_anti₀ hη_pos hsub_ge
    have hzeta_inv : ‖(riemannZeta z₀)⁻¹‖ ≤ 1 + 1 / η := by
      have hz_eq := LFunction_one_eq_mul_riemannZeta (q := 1) hz₀_ne1
      simp only [Nat.primeFactors_one, Finset.prod_empty, one_mul] at hz_eq
      rw [← hz_eq]
      simpa [hz₀_re] using norm_inv_LFunction_le_one_add_inv (1 : DirichletCharacter ℂ 1) hz₀_1_lt
    have h2 : 1 + 1 / η ≤ 2 / η := by
      have : (1 : ℝ) ≤ 1 / η := (one_le_div hη_pos).2 (by linarith)
      rw [show (2 : ℝ) / η = 1 / η + 1 / η by ring]
      linarith
    calc
      ‖(z₀ - 1)⁻¹‖ * ‖(riemannZeta z₀)⁻¹‖ ≤ (1 / η) * (2 / η) :=
        mul_le_mul h1 (hzeta_inv.trans h2) (norm_nonneg _) (by positivity)
      _ = 2 / η ^ 2 := by ring
  let M : ℝ := C_z1 / η ^ 2 * (|T| + 3) ^ 2
  have hsphere : ∀ w ∈ Metric.sphere z₀ (1 / 2 : ℝ), ‖zetaOne w / zetaOne z₀‖ ≤ M := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hw_re_lo : 1 / 2 ≤ w.re := by
      have hre : |w.re - z₀.re| ≤ 1 / 2 := by
        calc
          |w.re - z₀.re| = |(w - z₀).re| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 2 := hw
      rw [hz₀_re] at hre
      linarith [(abs_le.mp hre).1]
    have hw_re_hi : w.re ≤ 2 := by
      have hre : |w.re - z₀.re| ≤ 1 / 2 := by
        calc
          |w.re - z₀.re| = |(w - z₀).re| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 2 := hw
      rw [hz₀_re] at hre
      linarith [(abs_le.mp hre).2]
    have hw_im : |w.im| + 3 ≤ 4 * (|T| + 3) := by
      have him : |w.im - z₀.im| ≤ 1 / 2 := by
        calc
          |w.im - z₀.im| = |(w - z₀).im| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
          _ = 1 / 2 := hw
      have hw_abs : |w.im| ≤ |T| + 1 / 2 := by
        rw [hz₀_im] at him
        have h1 := (abs_le.mp him).1
        have h2 := (abs_le.mp him).2
        rw [abs_le]
        constructor <;> linarith [neg_abs_le T, le_abs_self T]
      linarith [abs_nonneg T]
    have hzw : ‖zetaOne w‖ ≤ C * (4 * (|T| + 3)) ^ 2 := by
      refine (hbd w hw_re_lo hw_re_hi).trans ?_
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith [abs_nonneg w.im, abs_nonneg T]) hw_im)
        hC_pos.le
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖zetaOne w‖ * ‖(zetaOne z₀)⁻¹‖
        ≤ (C * (4 * (|T| + 3)) ^ 2) * (2 / η ^ 2) :=
          mul_le_mul hzw hinv_z₀ (norm_nonneg _) (by positivity)
      _ = (32 * C) / η ^ 2 * (|T| + 3) ^ 2 := by ring
      _ ≤ M := by
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _)
            (sq_nonneg η)) (sq_nonneg _)
  have hlandau :=
    AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.landau_neg_re_logDeriv_center_le
      (f := zetaOne) (z₀ := z₀) (R := 1 / 2) (M := M)
      (by norm_num)
      ((differentiable_zetaOne.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _))
      hz₀_ne0 hsphere (fun ρ _ hρ_zero ↦ by
        by_contra hlt
        push Not at hlt
        have hρ_gt : 1 < ρ.re := hz₀_1_lt.trans hlt
        have hρ_ne1 : ρ ≠ 1 := fun h ↦ by simp [h] at hρ_gt
        have hζ_ne := AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re hρ_gt
        rw [zetaOne_eq_sub_one_mul hρ_ne1] at hρ_zero
        exact hζ_ne ((mul_eq_zero.mp hρ_zero).resolve_left (sub_ne_zero.mpr hρ_ne1)))
  have hlogM : Real.log M = Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3) := by
    dsimp only [M]
    have hpos1 : 0 < C_z1 / η ^ 2 := by positivity
    have hpos2 : 0 < |T| + 3 := by linarith [abs_nonneg T]
    rw [Real.log_mul hpos1.ne' (pow_ne_zero 2 hpos2.ne'), Real.log_pow]
    push_cast
    ring
  have h4 : (4 / (1 / 2 : ℝ)) * Real.log M = 8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3)) := by
    rw [hlogM]
    ring
  rw [h4] at hlandau
  exact hlandau

private lemma landau_zetaOne_center_sub_zero_exists :
    ∃ C_z1 : ℝ, 1 ≤ C_z1 ∧ ∀ {η : ℝ}, 0 < η → η ≤ 1 / 4 → ∀ T : ℝ, ∀ {ρ : ℂ},
      ρ ∈ Metric.closedBall (((1 + η : ℝ) : ℂ) + (T : ℂ) * I) (1 / 4 : ℝ) →
      zetaOne ρ = 0 →
      -(logDeriv zetaOne (((1 + η : ℝ) : ℂ) + (T : ℂ) * I)).re ≤
        8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3)) -
          (((((1 + η : ℝ) : ℂ) + (T : ℂ) * I - ρ)⁻¹).re) := by
  obtain ⟨C, hC_pos, hbd⟩ := norm_zetaOne_re_ge_half_le
  let C_z1 : ℝ := max 1 (32 * C)
  refine ⟨C_z1, le_max_left _ _, fun {η} hη_pos hη_le T {ρ} hρ_mem hρ_zero ↦ ?_⟩
  let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = 1 + η := by simp [z₀]
  have hz₀_im : z₀.im = T := by simp [z₀]
  have hz₀_1_lt : 1 < z₀.re := by rw [hz₀_re]; linarith
  have hz₀_ne1 : z₀ ≠ 1 := fun h ↦ by simp [h] at hz₀_1_lt
  have hz₀_ne0 : zetaOne z₀ ≠ 0 := by
    rw [zetaOne_eq_sub_one_mul hz₀_ne1]
    exact mul_ne_zero (sub_ne_zero.mpr hz₀_ne1)
      (AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re hz₀_1_lt)
  have hinv_z₀ : ‖(zetaOne z₀)⁻¹‖ ≤ 2 / η ^ 2 := by
    rw [zetaOne_eq_sub_one_mul hz₀_ne1, mul_inv, norm_mul]
    have hsub_ge : η ≤ ‖z₀ - 1‖ := by
      calc
        η = |(z₀ - 1).re| := by simp [hz₀_re, abs_of_pos hη_pos]
        _ ≤ ‖z₀ - 1‖ := Complex.abs_re_le_norm (z₀ - 1)
    have h1 : ‖(z₀ - 1)⁻¹‖ ≤ 1 / η := by
      rw [norm_inv, one_div]
      exact inv_anti₀ hη_pos hsub_ge
    have hzeta_inv : ‖(riemannZeta z₀)⁻¹‖ ≤ 1 + 1 / η := by
      have hz_eq := LFunction_one_eq_mul_riemannZeta (q := 1) hz₀_ne1
      simp only [Nat.primeFactors_one, Finset.prod_empty, one_mul] at hz_eq
      rw [← hz_eq]
      simpa [hz₀_re] using norm_inv_LFunction_le_one_add_inv (1 : DirichletCharacter ℂ 1) hz₀_1_lt
    have h2 : 1 + 1 / η ≤ 2 / η := by
      have : (1 : ℝ) ≤ 1 / η := (one_le_div hη_pos).2 (by linarith)
      rw [show (2 : ℝ) / η = 1 / η + 1 / η by ring]
      linarith
    calc
      ‖(z₀ - 1)⁻¹‖ * ‖(riemannZeta z₀)⁻¹‖ ≤ (1 / η) * (2 / η) :=
        mul_le_mul h1 (hzeta_inv.trans h2) (norm_nonneg _) (by positivity)
      _ = 2 / η ^ 2 := by ring
  let M : ℝ := C_z1 / η ^ 2 * (|T| + 3) ^ 2
  have hsphere : ∀ w ∈ Metric.sphere z₀ (1 / 2 : ℝ), ‖zetaOne w / zetaOne z₀‖ ≤ M := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hw_re_lo : 1 / 2 ≤ w.re := by
      have hre : |w.re - z₀.re| ≤ 1 / 2 := by
        calc
          |w.re - z₀.re| = |(w - z₀).re| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 2 := hw
      rw [hz₀_re] at hre
      linarith [(abs_le.mp hre).1]
    have hw_re_hi : w.re ≤ 2 := by
      have hre : |w.re - z₀.re| ≤ 1 / 2 := by
        calc
          |w.re - z₀.re| = |(w - z₀).re| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
          _ = 1 / 2 := hw
      rw [hz₀_re] at hre
      linarith [(abs_le.mp hre).2]
    have hw_im : |w.im| + 3 ≤ 4 * (|T| + 3) := by
      have him : |w.im - z₀.im| ≤ 1 / 2 := by
        calc
          |w.im - z₀.im| = |(w - z₀).im| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
          _ = 1 / 2 := hw
      have hw_abs : |w.im| ≤ |T| + 1 / 2 := by
        rw [hz₀_im] at him
        have h1 := (abs_le.mp him).1
        have h2 := (abs_le.mp him).2
        rw [abs_le]
        constructor <;> linarith [neg_abs_le T, le_abs_self T]
      linarith [abs_nonneg T]
    have hzw : ‖zetaOne w‖ ≤ C * (4 * (|T| + 3)) ^ 2 := by
      refine (hbd w hw_re_lo hw_re_hi).trans ?_
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith [abs_nonneg w.im, abs_nonneg T]) hw_im)
        hC_pos.le
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖zetaOne w‖ * ‖(zetaOne z₀)⁻¹‖
        ≤ (C * (4 * (|T| + 3)) ^ 2) * (2 / η ^ 2) :=
          mul_le_mul hzw hinv_z₀ (norm_nonneg _) (by positivity)
      _ = (32 * C) / η ^ 2 * (|T| + 3) ^ 2 := by ring
      _ ≤ M := by
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _)
            (sq_nonneg η)) (sq_nonneg _)
  have hρ_mem' : ρ ∈ Metric.closedBall z₀ ((1 / 2 : ℝ) / 2) := by
    convert hρ_mem using 2
    norm_num
  have hlandau :=
    AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.landau_neg_re_logDeriv_center_le_sub_zero
      (f := zetaOne) (z₀ := z₀) (R := 1 / 2) (M := M)
      (by norm_num)
      ((differentiable_zetaOne.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _))
      hz₀_ne0 hsphere (fun w _ hw_zero ↦ by
        by_contra hlt
        push Not at hlt
        have hw_gt : 1 < w.re := hz₀_1_lt.trans hlt
        have hw_ne1 : w ≠ 1 := fun h ↦ by simp [h] at hw_gt
        have hζ_ne := AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re hw_gt
        rw [zetaOne_eq_sub_one_mul hw_ne1] at hw_zero
        exact hζ_ne ((mul_eq_zero.mp hw_zero).resolve_left (sub_ne_zero.mpr hw_ne1)))
      hρ_mem' hρ_zero
  have hlogM : Real.log M = Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3) := by
    dsimp only [M]
    have hpos1 : 0 < C_z1 / η ^ 2 := by positivity
    have hpos2 : 0 < |T| + 3 := by linarith [abs_nonneg T]
    rw [Real.log_mul hpos1.ne' (pow_ne_zero 2 hpos2.ne'), Real.log_pow]
    push_cast
    ring
  have h4 : (4 / (1 / 2 : ℝ)) * Real.log M = 8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3)) := by
    rw [hlogM]
    ring
  rw [h4] at hlandau
  exact hlandau

private lemma logDeriv_riemannZeta_eq_zetaOne {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv zetaOne s - (s - 1)⁻¹ := by
  have hloc : riemannZeta =ᶠ[𝓝 s] fun z ↦ zetaOne z / (z - 1) := by
    have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds hs] with z hz'
    rw [zetaOne_eq_sub_one_mul hz']
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz'
    field_simp [hz1]
  let lin : ℂ → ℂ := fun z ↦ z - 1
  have hloc' : riemannZeta =ᶠ[𝓝 s] (zetaOne / lin) := hloc
  have hld_eq : logDeriv riemannZeta s = logDeriv (zetaOne / lin) s := by
    simp only [logDeriv_apply, hloc'.deriv_eq, hloc'.eq_of_nhds]
  have hz1_ne : zetaOne s ≠ 0 := by
    rw [zetaOne_eq_sub_one_mul hs]
    exact mul_ne_zero (sub_ne_zero.mpr hs) hz
  have hlin : DifferentiableAt ℂ lin s := differentiableAt_id.sub_const 1
  rw [hld_eq, logDeriv_div (f := zetaOne) (g := lin) s hz1_ne (sub_ne_zero.mpr hs)
    (differentiable_zetaOne s) hlin]
  simp [lin, logDeriv_apply]

private lemma re_inv_add_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I)⁻¹.re = a / (a ^ 2 + b ^ 2) := by
  have h := Complex.inv_re ((a : ℂ) + (b : ℂ) * I)
  have hns : Complex.normSq ((a : ℂ) + (b : ℂ) * I) = a ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply]
    simp [sq]
  rw [hns] at h
  simpa using h

private lemma zeta_zeroFreeRegion_contradiction
    {C_zeta C_max δ K_const c₀ L η σ₀ β : ℝ}
    (hK_def : K_const = (3 * C_zeta + 80 * (Real.log 4 + 1) + 160) / Real.log 2)
    (hc₀_def : c₀ = δ / 16) (hη_def : η = δ / L) (hσ₀_def : σ₀ = 1 + η)
    (hC_zeta : 0 < C_zeta) (_hC_max : 1 ≤ C_max)
    (hL_ge : Real.log 2 ≤ L) (hδ_pos : 0 < δ)
    (hδ_K : δ * K_const ≤ 1 / 640 * Real.log 2)
    (hδ_log : δ * Real.log ((Real.sqrt C_max + 1) / δ) ≤ 1 / 640 * Real.log 2)
    (hβ_lt1 : β < 1) (hβ_ge : 1 - c₀ / L ≤ β)
    (h_rearrange : 4 / (σ₀ - β) ≤ 3 / η + 3 * C_zeta + 4 / (17 * η) + 1 / (65 * η) +
      80 * Real.log ((Real.sqrt C_max + 1) / δ) + 160 * L + 64 * Real.log 2 + 16 * Real.log 4) :
    False := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  have hη_pos : 0 < η := by rw [hη_def]; exact div_pos hδ_pos hL_pos
  have hη_inv : L / δ = 1 / η := by rw [hη_def, one_div_div]
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h_part1 : 3 * C_zeta + 160 * L + 64 * Real.log 2 + 16 * Real.log 4 ≤ K_const * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
    have hlog2_le_4 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have hle0 : 3 * C_zeta + 64 * Real.log 2 + 16 * Real.log 4 ≤
        3 * C_zeta + 80 * (Real.log 4 + 1) := by linarith
    have hpos : 0 ≤ 3 * C_zeta + 80 * (Real.log 4 + 1) := by positivity
    have h2 : 3 * C_zeta + 64 * Real.log 2 + 16 * Real.log 4 ≤
        (3 * C_zeta + 80 * (Real.log 4 + 1)) * (L / Real.log 2) :=
      hle0.trans (le_mul_of_one_le_right hpos h1)
    calc
      3 * C_zeta + 160 * L + 64 * Real.log 2 + 16 * Real.log 4
        = (3 * C_zeta + 64 * Real.log 2 + 16 * Real.log 4) + 160 * L := by ring
      _ ≤ (3 * C_zeta + 80 * (Real.log 4 + 1)) * (L / Real.log 2) + 160 * L :=
            add_le_add h2 le_rfl
      _ = ((3 * C_zeta + 80 * (Real.log 4 + 1) + 160 * Real.log 2) / Real.log 2) * L := by
            field_simp [hlog2.ne']
      _ ≤ ((3 * C_zeta + 80 * (Real.log 4 + 1) + 160) / Real.log 2) * L := by
            refine mul_le_mul_of_nonneg_right ?_ hL_pos.le
            exact div_le_div_of_nonneg_right (by linarith) hlog2.le
      _ = K_const * L := by rw [← hK_def]
  have h_part1_mul : K_const * L ≤ (1 / 8) / η := by
    calc
      K_const * L = (δ * K_const) * (L / δ) := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 640 * Real.log 2) * (1 / η) := by
          rw [hη_inv]
          exact mul_le_mul_of_nonneg_right hδ_K (by positivity)
      _ ≤ (1 / 8) * (1 / η) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1 / 8) / η := by ring
  have h_part2_mul : 80 * Real.log ((Real.sqrt C_max + 1) / δ) ≤ (1 / 8) / η := by
    have hmul : 80 * (δ * Real.log ((Real.sqrt C_max + 1) / δ)) ≤ 1 / 8 * L := by
      calc
        80 * (δ * Real.log ((Real.sqrt C_max + 1) / δ)) ≤ 80 * (1 / 640 * Real.log 2) :=
            mul_le_mul_of_nonneg_left hδ_log (by norm_num)
        _ = 1 / 8 * Real.log 2 := by ring
        _ ≤ 1 / 8 * L := mul_le_mul_of_nonneg_left hL_ge (by norm_num)
    have hdiv := div_le_div_of_nonneg_right hmul hδ_pos.le
    calc
      80 * Real.log ((Real.sqrt C_max + 1) / δ)
        = (80 * (δ * Real.log ((Real.sqrt C_max + 1) / δ))) / δ := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 8 * L) / δ := hdiv
      _ = 1 / 8 * (L / δ) := by ring
      _ = (1 / 8) / η := by rw [hη_inv]; ring
  have h_upper : 4 / (σ₀ - β) ≤ (15 / 4) / η := by
    have hcoeff : 3 / η + 4 / (17 * η) + 1 / (65 * η) + (1 / 8) / η + (1 / 8) / η ≤ (15 / 4) / η := by
      have hnum : (3 : ℝ) + 4 / 17 + 1 / 65 + 1 / 8 + 1 / 8 ≤ 15 / 4 := by norm_num
      have heq1 : 3 / η + 4 / (17 * η) + 1 / (65 * η) + (1 / 8) / η + (1 / 8) / η =
          (3 + 4 / 17 + 1 / 65 + 1 / 8 + 1 / 8) / η := by ring
      rw [heq1]
      exact div_le_div_of_nonneg_right hnum hη_pos.le
    linarith [h_rearrange, h_part1, h_part1_mul, h_part2_mul, hcoeff]
  have hσ_sub : (16 / 15) * η ≤ σ₀ - β := by
    have hpos : 0 < σ₀ - β := by rw [hσ₀_def]; linarith
    rw [div_le_div_iff₀ hpos hη_pos] at h_upper
    calc
      (16 / 15) * η = (4 / 15) * (4 * η) := by ring
      _ ≤ (4 / 15) * ((15 / 4) * (σ₀ - β)) := mul_le_mul_of_nonneg_left h_upper (by norm_num)
      _ = σ₀ - β := by ring
  have hβ_le : β ≤ 1 - η / 15 := by rw [hσ₀_def] at hσ_sub; linarith [hσ_sub]
  have hc₀_lt : c₀ / L < η / 15 := by
    rw [hc₀_def, hη_def, div_right_comm]
    exact div_lt_div_of_pos_left (div_pos hδ_pos hL_pos) (by norm_num) (by norm_num)
  linarith [hβ_le, hc₀_lt, hβ_ge]

/-- Classical de la Vallée Poussin zero-free region for `riemannZeta`:
there exists `c₀ > 0` such that `riemannZeta s ≠ 0` whenever `s ≠ 1` and
`1 - c₀ / Real.log (|Im s| + 2) ≤ Re s`. -/
theorem zeta_zeroFreeRegion :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨C_zeta, hC_zeta, hzeta_bd⟩ := neg_logDeriv_riemannZeta_real_le
  obtain ⟨C_z1, hC_z1, hz1_bd⟩ := landau_zetaOne_center_exists
  obtain ⟨C_z2, hC_z2, hz2_bd⟩ := landau_zetaOne_center_sub_zero_exists
  let C_max : ℝ := max C_z1 C_z2
  have hC_max : 1 ≤ C_max := le_trans hC_z1 (le_max_left _ _)
  have hcont_z1 : Continuous zetaOne := differentiable_zetaOne.continuous
  obtain ⟨r₀, hr₀_pos, hr₀⟩ := Metric.continuousAt_iff.mp (hcont_z1.continuousAt (x := (1 : ℂ)))
    (1 / 2) (by norm_num)
  let r₁ : ℝ := min r₀ (1 / 2)
  have hr₁_pos : 0 < r₁ := lt_min hr₀_pos (by norm_num)
  have hnear1 : ∀ s : ℂ, s ≠ 1 → ‖s - 1‖ < r₁ → riemannZeta s ≠ 0 := by
    intro s hs1 hsdist hzero
    have hnorm_half : 1 / 2 ≤ ‖zetaOne s‖ := by
      have hlt : dist (zetaOne s) (zetaOne 1) < 1 / 2 := hr₀ (by rw [dist_eq_norm]; exact lt_of_lt_of_le hsdist (min_le_left _ _))
      rw [zetaOne_one, dist_eq_norm] at hlt
      have hrev := norm_sub_norm_le 1 (zetaOne s)
      rw [norm_one, norm_sub_rev] at hrev
      linarith
    rw [zetaOne_eq_sub_one_mul hs1, hzero, mul_zero, norm_zero] at hnorm_half
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K_const : ℝ := (3 * C_zeta + 80 * (Real.log 4 + 1) + 160) / Real.log 2
  have hK_nn : 0 ≤ K_const := by positivity
  let a_bound : ℝ := min (r₁ * Real.log 2 / 8) (Real.log 2 / 8)
  have ha_pos : 0 < a_bound := lt_min (by positivity) (by positivity)
  obtain ⟨δ, hδ_pos, hδ_le_a, hδ_K, hδ_log⟩ :=
    exists_small_delta a_bound (Real.sqrt C_max + 1) K_const (1 / 640 * Real.log 2)
      ha_pos (by positivity) hK_nn (by positivity)
  let c₀ : ℝ := δ / 16
  refine ⟨c₀, by positivity, fun ρ hρ1 hρ_re hρ_zero ↦ ?_⟩
  by_cases hre1 : 1 ≤ ρ.re
  · exact AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_le_re_bridge hre1 hρ_zero
  push Not at hre1
  let t : ℝ := ρ.im
  let β : ℝ := ρ.re
  let L : ℝ := Real.log (|t| + 2)
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  let η : ℝ := δ / L
  have hη_pos : 0 < η := div_pos hδ_pos hL_pos
  have hδ_le_eighth : δ ≤ Real.log 2 / 8 := hδ_le_a.trans (min_le_right _ _)
  have hδ_le_r₁ : δ ≤ r₁ * Real.log 2 / 8 := hδ_le_a.trans (min_le_left _ _)
  have hη_le_eighth : η ≤ 1 / 8 := by
    rw [div_le_iff₀ hL_pos]
    nlinarith
  have hη_le_r₁ : η ≤ r₁ / 8 := by
    rw [div_le_iff₀ hL_pos]
    nlinarith [hr₁_pos]
  have h_one_sub_β : 1 - β ≤ c₀ / L := by linarith
  have hc₀_lt_r1 : c₀ / L < r₁ / 2 := by
    dsimp only [c₀]
    rw [div_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hr₁_pos]
  have ht_ge : r₁ / 2 ≤ |t| := by
    by_contra hlt
    push Not at hlt
    have hdist : ‖ρ - 1‖ < r₁ := by
      calc
        ‖ρ - 1‖ ≤ |(ρ - 1).re| + |(ρ - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (1 - β) + |t| := by
            simp [β, t, abs_of_neg (by linarith : β - 1 < 0)]
        _ < r₁ / 2 + r₁ / 2 := add_lt_add (lt_of_le_of_lt h_one_sub_β hc₀_lt_r1) hlt
        _ = r₁ := by ring
    exact hnear1 ρ hρ1 hdist hρ_zero
  have ht_ge_4η : 4 * η ≤ |t| := by linarith
  let σ₀ : ℝ := 1 + η
  have hσ₀_gt1 : 1 < σ₀ := by linarith
  have hσ₀_le2 : σ₀ ≤ 2 := by linarith
  have h341 := three_four_one_neg_logDeriv_nonneg (1 : DirichletCharacter ℂ 1) hσ₀_gt1 t
  have h_L1_eq : ∀ s : ℂ, s ≠ 1 →
      -deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s =
      -deriv riemannZeta s / riemannZeta s := by
    intro s hs
    have hloc : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 s] riemannZeta := by
      have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
      filter_upwards [hopen.mem_nhds hs] with w hw
      rw [LFunction_one_eq_mul_riemannZeta hw]
      simp
    rw [hloc.deriv_eq, hloc.eq_of_nhds]
  have hs1_ne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := fun h ↦ by
    have := congr_arg Complex.re h
    simp [σ₀] at this
    linarith
  have hs2_ne : ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) ≠ 1 := fun h ↦ by
    have := congr_arg Complex.re h
    simp [σ₀] at this
    linarith
  rw [one_pow] at h341
  rw [h_L1_eq _ hs1_ne, h_L1_eq _ hs2_ne] at h341
  have hterm1 : (-deriv riemannZeta (σ₀ : ℂ) / riemannZeta (σ₀ : ℂ)).re ≤ 1 / η + C_zeta := by
    simpa [σ₀] using hzeta_bd σ₀ ⟨hσ₀_gt1, hσ₀_le2⟩
  have hlog_sub : ∀ c : ℝ, 1 ≤ c → c ≤ C_max →
      Real.log (c / η ^ 2) ≤ 2 * Real.log ((Real.sqrt C_max + 1) / δ) + 2 * L := by
    intro c hc1 hcmax
    have h1 : c / η ^ 2 ≤ ((Real.sqrt C_max + 1) / δ) ^ 2 * L ^ 2 := by
      have hnum : c ≤ (Real.sqrt C_max + 1) ^ 2 := by
        have hsq : C_max = Real.sqrt C_max ^ 2 := (Real.sq_sqrt (by linarith)).symm
        nlinarith [Real.sqrt_nonneg C_max]
      rw [div_eq_mul_inv, show η = δ / L from rfl, div_pow, inv_div, ← mul_div_assoc]
      calc
        c * L ^ 2 / δ ^ 2 ≤ ((Real.sqrt C_max + 1) ^ 2) * L ^ 2 / δ ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum (sq_nonneg L)) (sq_nonneg δ)
        _ = ((Real.sqrt C_max + 1) / δ) ^ 2 * L ^ 2 := by ring
    have hpos : 0 < c / η ^ 2 := by positivity
    have hlog_L : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
    calc
      Real.log (c / η ^ 2) ≤ Real.log (((Real.sqrt C_max + 1) / δ) ^ 2 * L ^ 2) :=
        Real.log_le_log hpos h1
      _ = 2 * Real.log ((Real.sqrt C_max + 1) / δ) + 2 * Real.log L := by
          rw [Real.log_mul (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hL_pos.ne'),
            Real.log_pow, Real.log_pow]
          push_cast
          ring
      _ ≤ 2 * Real.log ((Real.sqrt C_max + 1) / δ) + 2 * L := by linarith
  have hlog_T1 : Real.log (|t| + 3) ≤ L + Real.log 2 := by
    have h1 : |t| + 3 ≤ 2 * (|t| + 2) := by linarith [abs_nonneg t]
    calc
      Real.log (|t| + 3) ≤ Real.log (2 * (|t| + 2)) :=
        Real.log_le_log (by linarith [abs_nonneg t]) h1
      _ = Real.log 2 + L := Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
      _ = L + Real.log 2 := by ring
  have hlog_T2 : Real.log (|2 * t| + 3) ≤ L + Real.log 4 := by
    have h1 : |2 * t| + 3 ≤ 4 * (|t| + 2) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg t]
    calc
      Real.log (|2 * t| + 3) ≤ Real.log (4 * (|t| + 2)) :=
        Real.log_le_log (by linarith [abs_nonneg (2 * t)]) h1
      _ = Real.log 4 + L := Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
      _ = L + Real.log 4 := by ring
  have hρ_mem : ρ ∈ Metric.closedBall (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : ρ - (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) = (((β - (1 + η) : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp [β, t]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    have hc₀_le_eighth : c₀ / L ≤ 1 / 16 := by
      rw [div_le_iff₀ hL_pos]
      dsimp only [c₀]
      nlinarith
    linarith
  have hζ1_zero : zetaOne ρ = 0 := by
    rw [zetaOne_eq_sub_one_mul hρ1, hρ_zero, mul_zero]
  have hz2_re := hz2_bd hη_pos (by linarith) t hρ_mem hζ1_zero
  have hld1_eq : -deriv riemannZeta (σ₀ + t * I) / riemannZeta (σ₀ + t * I) =
      -logDeriv zetaOne (σ₀ + t * I) + ((σ₀ + t * I) - 1)⁻¹ := by
    have h := logDeriv_riemannZeta_eq_zetaOne hs1_ne
      (AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simpa [σ₀] using hσ₀_gt1))
    rw [show -deriv riemannZeta (σ₀ + t * I) / riemannZeta (σ₀ + t * I) =
      -logDeriv riemannZeta (σ₀ + t * I) by simp [logDeriv_apply]; ring, h]
    ring
  have hinv1_re : (((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹).re ≤ 1 / (17 * η) := by
    have hsub : (σ₀ : ℂ) + (t : ℂ) * I - 1 = (η : ℂ) + (t : ℂ) * I := by
      apply Complex.ext <;> simp [σ₀]
    rw [hsub, re_inv_add_mul_I]
    have hden : 17 * η ^ 2 ≤ η ^ 2 + t ^ 2 := by
      have htsq : 16 * η ^ 2 ≤ t ^ 2 := by
        have hsq := sq_le_sq' (by linarith : -|t| ≤ 4 * η) ht_ge_4η
        rw [sq_abs] at hsq
        linarith
      linarith
    calc
      η / (η ^ 2 + t ^ 2) ≤ η / (17 * η ^ 2) :=
        div_le_div_of_nonneg_left hη_pos.le (by positivity) hden
      _ = 1 / (17 * η) := by
          have hne : η ≠ 0 := hη_pos.ne'
          field_simp [hne]
  have hsub_rho_re : (((((1 + η : ℝ) : ℂ) + (t : ℂ) * I - ρ)⁻¹).re) = 1 / (σ₀ - β) := by
    have hsub : ((1 + η : ℝ) : ℂ) + (t : ℂ) * I - ρ = ((σ₀ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [σ₀, β, t]
    rw [hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hterm2 : (-deriv riemannZeta (σ₀ + t * I) / riemannZeta (σ₀ + t * I)).re ≤
      8 * (2 * Real.log ((Real.sqrt C_max + 1) / δ) + 4 * L + 2 * Real.log 2) +
        1 / (17 * η) - 1 / (σ₀ - β) := by
    rw [hld1_eq, Complex.add_re, Complex.neg_re]
    have h1 : 8 * (Real.log (C_z2 / η ^ 2) + 2 * Real.log (|t| + 3)) ≤
        8 * (2 * Real.log ((Real.sqrt C_max + 1) / δ) + 4 * L + 2 * Real.log 2) := by
      have ha := hlog_sub C_z2 hC_z2 (le_max_right _ _)
      linarith [hlog_T1]
    rw [hsub_rho_re, show (1 + η : ℝ) = σ₀ from rfl] at hz2_re
    have hinv1' : (((σ₀ : ℂ) + (t : ℂ) * I - 1)⁻¹).re ≤ 1 / (17 * η) := hinv1_re
    linarith [hz2_re, h1, hinv1']
  have hz1_re := hz1_bd hη_pos (by linarith) (2 * t)
  have hld2_eq : -deriv riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I) /
      riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I) =
      -logDeriv zetaOne (σ₀ + ((2 * t : ℝ) : ℂ) * I) +
        ((σ₀ + ((2 * t : ℝ) : ℂ) * I) - 1)⁻¹ := by
    have h := logDeriv_riemannZeta_eq_zetaOne hs2_ne
      (AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simpa [σ₀] using hσ₀_gt1))
    rw [show -deriv riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I) /
        riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I) =
      -logDeriv riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I) by simp [logDeriv_apply]; ring, h]
    ring
  have hinv2_re : (((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1)⁻¹).re ≤ 1 / (65 * η) := by
    have hsub : (σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1 = (η : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [σ₀]
    rw [hsub, re_inv_add_mul_I]
    have hden : 65 * η ^ 2 ≤ η ^ 2 + (2 * t) ^ 2 := by
      have htsq : 16 * η ^ 2 ≤ t ^ 2 := by
        have hsq := sq_le_sq' (by linarith : -|t| ≤ 4 * η) ht_ge_4η
        rw [sq_abs] at hsq
        linarith
      linarith
    calc
      η / (η ^ 2 + (2 * t) ^ 2) ≤ η / (65 * η ^ 2) :=
        div_le_div_of_nonneg_left hη_pos.le (by positivity) hden
      _ = 1 / (65 * η) := by
          have hne : η ≠ 0 := hη_pos.ne'
          field_simp [hne]
  have hterm3 : (-deriv riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I) /
      riemannZeta (σ₀ + ((2 * t : ℝ) : ℂ) * I)).re ≤
      8 * (2 * Real.log ((Real.sqrt C_max + 1) / δ) + 4 * L + 2 * Real.log 4) +
        1 / (65 * η) := by
    rw [hld2_eq, Complex.add_re, Complex.neg_re]
    have h1 : 8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|2 * t| + 3)) ≤
        8 * (2 * Real.log ((Real.sqrt C_max + 1) / δ) + 4 * L + 2 * Real.log 4) := by
      have ha := hlog_sub C_z1 hC_z1 (le_max_left _ _)
      linarith [hlog_T2]
    rw [show (1 + η : ℝ) = σ₀ from rfl] at hz1_re
    have hinv2' : (((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1)⁻¹).re ≤ 1 / (65 * η) := hinv2_re
    linarith [hz1_re, h1, hinv2']
  have hmul3 : 3 * (1 / η) = 3 / η := by ring
  have hmul4 : 4 * (1 / (σ₀ - β)) = 4 / (σ₀ - β) := by ring
  have hmul4_17 : 4 * (1 / (17 * η)) = 4 / (17 * η) := by ring
  have h_rearrange : 4 / (σ₀ - β) ≤ 3 / η + 3 * C_zeta + 4 / (17 * η) + 1 / (65 * η) +
      80 * Real.log ((Real.sqrt C_max + 1) / δ) + 160 * L + 64 * Real.log 2 + 16 * Real.log 4 := by
    linarith [h341, hterm1, hterm2, hterm3, hmul3, hmul4, hmul4_17]
  exact zeta_zeroFreeRegion_contradiction rfl rfl rfl rfl hC_zeta hC_max hL_ge hδ_pos hδ_K hδ_log
    hre1 hρ_re h_rearrange

private lemma log_408_div_eta_le {q : ℕ} [NeZero q] (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    let L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
    let η : ℝ := δ / L
    Real.log (408 / η) ≤ Real.log (408 / δ) + L ∧
      Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ L + Real.log 2 := by
  intro L η
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqt : 2 ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hL_pos : 0 < L := Real.log_pos (by linarith)
  have hL_le : L ≤ (q : ℝ) * (|t| + 2) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have h1 : 408 / η ≤ (408 / δ) * ((q : ℝ) * (|t| + 2)) := by
    have heq : 408 / η = (408 / δ) * L := by
      dsimp only [η]
      have hδ_ne : δ ≠ 0 := hδ.ne'
      have hL_ne : L ≠ 0 := hL_pos.ne'
      field_simp [hδ_ne, hL_ne]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hL_le (by positivity)
  have hpart1 : Real.log (408 / η) ≤ Real.log (408 / δ) + L := by
    calc
      Real.log (408 / η) ≤ Real.log ((408 / δ) * ((q : ℝ) * (|t| + 2))) :=
        Real.log_le_log (by dsimp only [η]; positivity) h1
      _ = Real.log (408 / δ) + L :=
        Real.log_mul (by positivity) (by positivity)
  have h2 : (q : ℝ) * (|2 * t| + 2) ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg t]
  have hpart2 : Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ L + Real.log 2 := by
    calc
      Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ Real.log (2 * ((q : ℝ) * (|t| + 2))) :=
        Real.log_le_log (by positivity) h2
      _ = Real.log 2 + L := Real.log_mul (by norm_num) (by positivity)
      _ = L + Real.log 2 := by ring
  exact ⟨hpart1, hpart2⟩

/-- Classical de la Vallée Poussin zero-free region for complex Dirichlet characters (`χ² ≠ 1`):
there exists a universal constant `c > 0` such that `L(s, χ) ≠ 0` whenever
`1 - c / Real.log (q * (|Im s| + 2)) ≤ Re s`. -/
theorem zeroFreeRegion_complex :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      IsComplexChar χ → ∀ s : ℂ, 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨C_zeta, hC_zeta, hzeta_bd⟩ := neg_logDeriv_riemannZeta_real_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K_const : ℝ := (3 * C_zeta + 16 * Real.log 2) / Real.log 2 + 120
  obtain ⟨δ, hδ_pos, hδ_le_a, hδ_K, hδ_log⟩ :=
    exists_small_delta (Real.log 2 / 8) 408 K_const (1 / 160 * Real.log 2)
      (by positivity) (by norm_num) (by positivity) (by positivity)
  let c : ℝ := δ / 8
  refine ⟨c, by positivity, fun {q} _ χ hχ ρ hρ_re hρ_zero ↦ ?_⟩
  have hχ2 : χ ^ 2 ≠ 1 := (isComplexChar_iff_not_isReal χ).mp hχ |> fun h ↦ by
    rwa [isReal_iff_sq_eq_one] at h
  have hχ1 : χ ≠ 1 := fun h ↦ hχ2 (by simp [h])
  by_cases hre1 : 1 ≤ ρ.re
  · exact LFunction_ne_zero_on_re_one χ hre1 (Or.inl hχ1) hρ_zero
  push Not at hre1
  let t : ℝ := ρ.im
  let β : ℝ := ρ.re
  have hβ_lt1 : β < 1 := hre1
  let L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hβ_ge : 1 - c / L ≤ β := hρ_re
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  let η : ℝ := δ / L
  have hη_pos : 0 < η := div_pos hδ_pos hL_pos
  have hη_le : η ≤ 1 / 8 := by
    rw [div_le_iff₀ hL_pos]
    nlinarith
  let σ₀ : ℝ := 1 + η
  have hσ₀_gt1 : 1 < σ₀ := by linarith
  have hσ₀_le2 : σ₀ ≤ 2 := by linarith
  have h341 := three_four_one_neg_logDeriv_nonneg χ hσ₀_gt1 t
  have hterm1 : (-deriv riemannZeta (σ₀ : ℂ) / riemannZeta (σ₀ : ℂ)).re ≤ 1 / η + C_zeta := by
    simpa [σ₀] using hzeta_bd σ₀ ⟨hσ₀_gt1, hσ₀_le2⟩
  have hρ_mem : ρ ∈ Metric.closedBall (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : ρ - (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) = (((β - (1 + η) : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp [β, t]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    have hc_le_eighth : c / L ≤ 1 / 8 := by
      rw [div_le_iff₀ hL_pos]
      dsimp only [c]
      nlinarith
    linarith
  have hL1 := landau_LFunction_center_sub_zero_le hχ1 hη_pos (by linarith) t hρ_mem hρ_zero
  have hL2 := landau_LFunction_center_le hχ2 hη_pos (by linarith) (2 * t)
  obtain ⟨hlog_eta, hlog_2t⟩ := log_408_div_eta_le (q := q) t hδ_pos
  have hsub_rho_re : (((((1 + η : ℝ) : ℂ) + (t : ℂ) * I - ρ)⁻¹).re) = 1 / (σ₀ - β) := by
    have hsub : ((1 + η : ℝ) : ℂ) + (t : ℂ) * I - ρ = ((σ₀ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [σ₀, β, t]
    rw [hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hsub_rho_re] at hL1
  have hld_eq : ∀ {ψ : DirichletCharacter ℂ q} {z : ℂ},
      -deriv (DirichletCharacter.LFunction ψ) z / DirichletCharacter.LFunction ψ z =
      -logDeriv (DirichletCharacter.LFunction ψ) z := by
    intro ψ z
    simp [logDeriv_apply, neg_div]
  rw [hld_eq, hld_eq] at h341
  have hlog_eta' : Real.log (408 / η) ≤ Real.log (408 / δ) + L := hlog_eta
  have hlog_2t' : Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ L + Real.log 2 := hlog_2t
  have hterm2 : -(logDeriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I)).re ≤
      8 * Real.log (408 / δ) + 24 * L - 1 / (σ₀ - β) := by
    change -(logDeriv (DirichletCharacter.LFunction χ) (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)).re ≤ _
    linarith [hL1, hlog_eta']
  have hterm3 : -(logDeriv (DirichletCharacter.LFunction (χ ^ 2))
      ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤
      8 * Real.log (408 / δ) + 24 * L + 16 * Real.log 2 := by
    change -(logDeriv (DirichletCharacter.LFunction (χ ^ 2))
      (((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤ _
    linarith [hL2, hlog_eta', hlog_2t']
  have h_comb : 4 / (σ₀ - β) ≤ 3 / η + (3 * C_zeta + 16 * Real.log 2 + 120 * L) +
      40 * Real.log (408 / δ) := by
    have hre_neg : ∀ z : ℂ, (-logDeriv (DirichletCharacter.LFunction χ) z).re =
        -(logDeriv (DirichletCharacter.LFunction χ) z).re := fun _ ↦ rfl
    have hre_neg2 : ∀ z : ℂ, (-logDeriv (DirichletCharacter.LFunction (χ ^ 2)) z).re =
        -(logDeriv (DirichletCharacter.LFunction (χ ^ 2)) z).re := fun _ ↦ rfl
    rw [hre_neg, hre_neg2] at h341
    have hmul4 : 4 * (1 / (σ₀ - β)) = 4 / (σ₀ - β) := by ring
    have hmul3 : 3 * (1 / η) = 3 / η := by ring
    linarith [hterm1, hterm2, hterm3, h341, hmul4, hmul3]
  have h_part1 : (3 * C_zeta + 16 * Real.log 2 + 120 * L) ≤ K_const * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
    have hpos : 0 ≤ 3 * C_zeta + 16 * Real.log 2 := by positivity
    dsimp only [K_const]
    have hmul1 : 3 * C_zeta + 16 * Real.log 2 ≤ (3 * C_zeta + 16 * Real.log 2) * (L / Real.log 2) :=
      le_mul_of_one_le_right hpos h1
    have hmul2 : (3 * C_zeta + 16 * Real.log 2) * (L / Real.log 2) =
        ((3 * C_zeta + 16 * Real.log 2) / Real.log 2) * L := by ring
    linarith
  have hη_inv : L / δ = 1 / η := by
    dsimp only [η]
    have hδ_ne : δ ≠ 0 := hδ_pos.ne'
    have hL_ne : L ≠ 0 := hL_pos.ne'
    field_simp [hδ_ne, hL_ne]
  have h_part1_mul : K_const * L ≤ (1 / 4) / η := by
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    calc
      K_const * L = (δ * K_const) * (L / δ) := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 160 * Real.log 2) * (1 / η) := by
          rw [hη_inv]
          exact mul_le_mul_of_nonneg_right hδ_K (by positivity)
      _ ≤ (1 / 4) * (1 / η) := by nlinarith [div_pos one_pos hη_pos]
      _ = (1 / 4) / η := by ring
  have h_part2_mul : 40 * Real.log (408 / δ) ≤ (1 / 4) / η := by
    have hmul : 40 * (δ * Real.log (408 / δ)) ≤ 1 / 4 * L := by
      calc
        40 * (δ * Real.log (408 / δ)) ≤ 40 * (1 / 160 * Real.log 2) := by linarith
        _ = 1 / 4 * Real.log 2 := by ring
        _ ≤ 1 / 4 * L := by linarith
    have hdiv := div_le_div_of_nonneg_right hmul hδ_pos.le
    calc
      40 * Real.log (408 / δ) = (40 * (δ * Real.log (408 / δ))) / δ := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 4 * L) / δ := hdiv
      _ = 1 / 4 * (L / δ) := by ring
      _ = (1 / 4) / η := by rw [hη_inv]; ring
  have h_upper : 4 / (σ₀ - β) ≤ (7 / 2) / η := by
    have : 3 / η + (1 / 4) / η + (1 / 4) / η = (7 / 2) / η := by ring
    linarith
  have hσ_sub : (8 / 7) * η ≤ σ₀ - β := by
    have hpos : 0 < σ₀ - β := by linarith
    rw [div_le_div_iff₀ hpos hη_pos] at h_upper
    linarith
  have hβ_le : β ≤ 1 - η / 7 := by dsimp only [σ₀] at hσ_sub; linarith
  have hc_lt : c / L < η / 7 := by
    dsimp only [c, η]
    rw [div_right_comm]
    nlinarith [div_pos hδ_pos hL_pos]
  linarith [hβ_ge]

/-- Classical zero-free region for the principal Dirichlet character `1 : DirichletCharacter ℂ q`:
there exists `c > 0` such that `L(s, 1_q) ≠ 0` whenever `s ≠ 1` and
`1 - c / Real.log (q * (|Im s| + 2)) ≤ Re s`. -/
theorem zeroFreeRegion_principal :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (s : ℂ), s ≠ 1 →
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re →
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
  obtain ⟨c₀, hc₀_pos, hzeta⟩ := zeta_zeroFreeRegion
  let c : ℝ := min c₀ (Real.log 2 / 2)
  refine ⟨c, lt_min hc₀_pos (by positivity), fun {q} _ s hs1 hs_re ↦ ?_⟩
  rw [LFunction_one_eq_mul_riemannZeta hs1]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL_ge : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hs_pos : 0 < s.re := by
    have hc_le : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (lt_of_lt_of_le (Real.log_pos (by norm_num)) hL_ge)]
      have h1 : c ≤ Real.log 2 / 2 := min_le_right _ _
      linarith
    linarith
  have hprod_ne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hprime.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    exact sub_ne_zero.mpr fun heq ↦ by
      rw [← heq, norm_one] at hnorm
      exact lt_irrefl _ hnorm
  have hL_im_le : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith [abs_nonneg s.im]) (by nlinarith [abs_nonneg s.im])
  have hc₀_le : 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re := by
    have h1 : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₀ / Real.log (|s.im| + 2) :=
      div_le_div₀ (by positivity) (min_le_left _ _) (Real.log_pos (by linarith [abs_nonneg s.im]))
        hL_im_le
    linarith
  exact mul_ne_zero hprod_ne (hzeta s hs1 hc₀_le)

private lemma real_nonreal_large_im_term3
    {C_z1 δ t L η σ₀ : ℝ} {q : ℕ} [NeZero q]
    (hC_z1 : 1 ≤ C_z1)
    (hz1_bd : ∀ {η : ℝ}, 0 < η → η ≤ 1 / 4 → ∀ T : ℝ,
      -(logDeriv zetaOne (((1 + η : ℝ) : ℂ) + (T : ℂ) * I)).re ≤
        8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3)))
    (hδ_pos : 0 < δ) (hq1 : (1 : ℝ) ≤ q) (hL_def : L = Real.log ((q : ℝ) * (|t| + 2)))
    (hη_def : η = δ / L) (hη_le : η ≤ 1 / 8) (hσ₀_def : σ₀ = 1 + η)
    (ht_ge : η / 2 ≤ |t|) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤
      16 * Real.log ((Real.sqrt C_z1 + 1) / δ) + 33 * L + 16 * Real.log 2 + 1 / (2 * η) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq_pos : (0 : ℝ) < q := by linarith
  have hL_ge : Real.log 2 ≤ L := by
    rw [hL_def]; exact Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  have hη_pos : 0 < η := by rw [hη_def]; exact div_pos hδ_pos hL_pos
  have hσ₀_gt1 : 1 < σ₀ := by rw [hσ₀_def]; linarith
  have hs2_ne : ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) ≠ 1 := fun h ↦ by
    have := congr_arg Complex.re h
    simp at this
    linarith
  have hdiff_1q := norm_logDeriv_LFunction_one_sub_riemannZeta_le (q := q)
    (s := (σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ₀_gt1)
  have hre_1q : -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤
      -(logDeriv riemannZeta ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re + Real.log q := by
    have hsub := (Complex.abs_re_le_norm _).trans hdiff_1q
    rw [Complex.sub_re] at hsub
    linarith [(abs_le.mp hsub).1]
  have hlog_q_le : Real.log q ≤ L := by
    rw [hL_def]; exact Real.log_le_log hq_pos (by nlinarith [abs_nonneg t])
  have hld2_eq : -logDeriv riemannZeta ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
      -logDeriv zetaOne ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) +
        (((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) - 1)⁻¹ := by
    rw [logDeriv_riemannZeta_eq_zetaOne hs2_ne
      (AnalyticNumberTheory.RiemannZeta.riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ₀_gt1))]
    ring
  have hinv2_re : (((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1)⁻¹).re ≤ 1 / (2 * η) := by
    have hsub : (σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1 = (η : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hσ₀_def]
    rw [hsub, re_inv_add_mul_I]
    have h2t : η ≤ |2 * t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have htsq : η ^ 2 ≤ 4 * t ^ 2 := by
      have hsq := sq_le_sq' (by linarith [abs_nonneg (2 * t)]) h2t
      rw [sq_abs] at hsq
      linarith
    have hden : 2 * η ^ 2 ≤ η ^ 2 + (2 * t) ^ 2 := by linarith
    calc
      η / (η ^ 2 + (2 * t) ^ 2) ≤ η / (2 * η ^ 2) :=
        div_le_div_of_nonneg_left hη_pos.le (by positivity) hden
      _ = 1 / (2 * η) := by field_simp [hη_pos.ne']
  have hz1 := hz1_bd hη_pos (by linarith) (2 * t)
  have hlog_Cz : Real.log (C_z1 / η ^ 2) ≤
      2 * Real.log ((Real.sqrt C_z1 + 1) / δ) + 2 * L := by
    have h1 : C_z1 / η ^ 2 ≤ ((Real.sqrt C_z1 + 1) / δ) ^ 2 * L ^ 2 := by
      have hnum : C_z1 ≤ (Real.sqrt C_z1 + 1) ^ 2 := by
        have hsq : C_z1 = Real.sqrt C_z1 ^ 2 := (Real.sq_sqrt (by linarith)).symm
        nlinarith [Real.sqrt_nonneg C_z1]
      have heq_eta : C_z1 / η ^ 2 = C_z1 * L ^ 2 / δ ^ 2 := by
        rw [hη_def]; field_simp [hδ_pos.ne', hL_pos.ne']
      rw [heq_eta]
      calc
        C_z1 * L ^ 2 / δ ^ 2 ≤ ((Real.sqrt C_z1 + 1) ^ 2) * L ^ 2 / δ ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum (sq_nonneg L)) (sq_nonneg δ)
        _ = ((Real.sqrt C_z1 + 1) / δ) ^ 2 * L ^ 2 := by ring
    have hlog_L : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
    calc
      Real.log (C_z1 / η ^ 2) ≤ Real.log (((Real.sqrt C_z1 + 1) / δ) ^ 2 * L ^ 2) :=
        Real.log_le_log (by positivity) h1
      _ = 2 * Real.log ((Real.sqrt C_z1 + 1) / δ) + 2 * Real.log L := by
          rw [Real.log_mul (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hL_pos.ne'),
            Real.log_pow, Real.log_pow]
          push_cast
          ring
      _ ≤ 2 * Real.log ((Real.sqrt C_z1 + 1) / δ) + 2 * L := by linarith
  have hlog_2t_3 : Real.log (|2 * t| + 3) ≤ L + Real.log 2 := by
    have h1 : |2 * t| + 3 ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        2 * |t| + 3 ≤ 2 * (|t| + 2) := by linarith
        _ = 2 * (1 * (|t| + 2)) := by ring
        _ ≤ 2 * ((q : ℝ) * (|t| + 2)) := by gcongr
    calc
      Real.log (|2 * t| + 3) ≤ Real.log (2 * ((q : ℝ) * (|t| + 2))) :=
        Real.log_le_log (by positivity) h1
      _ = Real.log 2 + L := by rw [hL_def, Real.log_mul (by norm_num) (by positivity)]
      _ = L + Real.log 2 := by ring
  rw [show -deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
    -logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) by rw [logDeriv_apply, neg_div]]
  have h1 : -(logDeriv riemannZeta ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤
      16 * Real.log ((Real.sqrt C_z1 + 1) / δ) + 32 * L + 16 * Real.log 2 + 1 / (2 * η) := by
    have hre_add : -(logDeriv riemannZeta ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re =
        (-logDeriv zetaOne ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re +
          (((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1)⁻¹).re := by
      rw [← Complex.neg_re, hld2_eq, Complex.add_re]
    rw [hre_add, hσ₀_def]
    have hz1' : (-logDeriv zetaOne (((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤
        8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|2 * t| + 3)) := hz1
    have hinv2' : (((((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I - 1)⁻¹)).re ≤ 1 / (2 * η) := by
      simpa [hσ₀_def] using hinv2_re
    linarith [hz1', hinv2', hlog_Cz, hlog_2t_3]
  have hre1q : (-logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re =
      -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := rfl
  rw [hre1q]
  linarith [hre_1q, h1, hlog_q_le]

private lemma zeroFreeRegion_real_nonreal_large_im
    {C_zeta C_z1 δ K_const : ℝ} (hC_zeta : 0 < C_zeta) (hC_z1 : 1 ≤ C_z1)
    (hzeta_bd : ∀ σ ∈ Set.Ioc (1 : ℝ) 2,
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C_zeta)
    (hz1_bd : ∀ {η : ℝ}, 0 < η → η ≤ 1 / 4 → ∀ T : ℝ,
      -(logDeriv zetaOne (((1 + η : ℝ) : ℂ) + (T : ℂ) * I)).re ≤
        8 * (Real.log (C_z1 / η ^ 2) + 2 * Real.log (|T| + 3)))
    (hK_def : K_const = (3 * C_zeta + 16 * Real.log 3 + 121) / Real.log 2 + 129)
    (hδ_pos : 0 < δ) (hδ_K : δ * K_const ≤ 1 / 640 * Real.log 2)
    (hδ_log : δ * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) ≤ 1 / 640 * Real.log 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hreal : IsReal χ) (hχ1 : χ ≠ 1)
    {ρ : ℂ} (hρ_re : 1 - (δ / 16) / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ ρ.re)
    (hβ_lt1 : ρ.re < 1) (hρ_zero : DirichletCharacter.LFunction χ ρ = 0)
    (hη_le : δ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 / 8)
    (ht_ge : (δ / Real.log ((q : ℝ) * (|ρ.im| + 2))) / 2 ≤ |ρ.im|) : False := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  let t : ℝ := ρ.im
  let β : ℝ := ρ.re
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq_pos : (0 : ℝ) < q := by linarith
  let L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  let η : ℝ := δ / L
  have hη_pos : 0 < η := div_pos hδ_pos hL_pos
  have hη_le' : η ≤ 1 / 8 := hη_le
  let σ₀ : ℝ := 1 + η
  have hσ₀_gt1 : 1 < σ₀ := by linarith
  have hσ₀_le2 : σ₀ ≤ 2 := by linarith
  have h_one_sub_β_η : 1 - β ≤ η / 16 := by
    have h1 : 1 - β ≤ (δ / 16) / L := by linarith [hρ_re]
    rwa [div_right_comm] at h1
  have hη_inv : L / δ = 1 / η := by
    dsimp only [η]
    field_simp [hδ_pos.ne', hL_pos.ne']
  have hlog_408_le : Real.log (408 / δ) ≤ Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (le_max_left _ _) hδ_pos.le)
  have hlog_Cz_le : Real.log ((Real.sqrt C_z1 + 1) / δ) ≤
      Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (le_max_right _ _) hδ_pos.le)
  have hχ2 : χ ^ 2 = 1 := (isReal_iff_sq_eq_one χ).mp hreal
  have h341 := three_four_one_neg_logDeriv_nonneg χ hσ₀_gt1 t
  rw [hχ2] at h341
  have hterm1 : (-deriv riemannZeta (σ₀ : ℂ) / riemannZeta (σ₀ : ℂ)).re ≤ 1 / η + C_zeta := by
    simpa [σ₀] using hzeta_bd σ₀ ⟨hσ₀_gt1, hσ₀_le2⟩
  have hρ_mem : ρ ∈ Metric.closedBall (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : ρ - (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) = (((β - (1 + η) : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp [β, t]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hL1 := landau_LFunction_center_sub_zero_le hχ1 hη_pos (by linarith) t hρ_mem hρ_zero
  have hsub_rho_re : (((((1 + η : ℝ) : ℂ) + (t : ℂ) * I - ρ)⁻¹).re) = 1 / (σ₀ - β) := by
    have hsub : ((1 + η : ℝ) : ℂ) + (t : ℂ) * I - ρ = ((σ₀ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [σ₀, β, t]
    rw [hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hsub_rho_re] at hL1
  obtain ⟨hlog_eta, _⟩ := log_408_div_eta_le (q := q) t hδ_pos
  have hlog_eta' : Real.log (408 / η) ≤ Real.log (408 / δ) + L := hlog_eta
  have hterm2 : (-deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I) /
      DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I)).re ≤
      8 * Real.log (408 / δ) + 24 * L - 1 / (σ₀ - β) := by
    rw [show -deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I) =
      -logDeriv (DirichletCharacter.LFunction χ) (((1 + η : ℝ) : ℂ) + (t : ℂ) * I) by
        simp [σ₀, logDeriv_apply, neg_div]]
    have hre : (-logDeriv (DirichletCharacter.LFunction χ) (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)).re =
        -(logDeriv (DirichletCharacter.LFunction χ) (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)).re := rfl
    rw [hre]
    linarith [hL1, hlog_eta']
  have hterm3 := real_nonreal_large_im_term3 hC_z1 hz1_bd hδ_pos hq1 rfl rfl (by linarith) rfl ht_ge
  have hmul3 : 3 * (1 / η) = 3 / η := by ring
  have hmul4 : 4 * (1 / (σ₀ - β)) = 4 / (σ₀ - β) := by ring
  have hterm2' : (-deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (t : ℂ) * I) /
      DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I)).re ≤
      8 * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) + 24 * L - 1 / (σ₀ - β) := by
    linarith [hterm2, hlog_408_le]
  have hterm3' : (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I) /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        ((σ₀ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re ≤
      16 * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) + 33 * L + 16 * Real.log 2 + 1 / (2 * η) := by
    linarith [hterm3, hlog_Cz_le]
  have h_comb : 4 / (σ₀ - β) ≤ 3 / η + 1 / (2 * η) + (3 * C_zeta + 16 * Real.log 2 + 129 * L) +
      48 * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) := by
    linarith [hterm1, hterm2', hterm3', h341, hmul3, hmul4]
  have h_part1 : 3 * C_zeta + 16 * Real.log 2 + 129 * L ≤ K_const * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
    have hlog2_le_3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have hpos : 0 ≤ 3 * C_zeta + 16 * Real.log 3 + 121 := by positivity
    have hmul1 : 3 * C_zeta + 16 * Real.log 2 ≤
        (3 * C_zeta + 16 * Real.log 3 + 121) * (L / Real.log 2) := by
      have hle : 3 * C_zeta + 16 * Real.log 2 ≤ 3 * C_zeta + 16 * Real.log 3 + 121 := by linarith
      exact hle.trans (le_mul_of_one_le_right hpos h1)
    have hmul2 : (3 * C_zeta + 16 * Real.log 3 + 121) * (L / Real.log 2) =
        ((3 * C_zeta + 16 * Real.log 3 + 121) / Real.log 2) * L := by ring
    calc
      3 * C_zeta + 16 * Real.log 2 + 129 * L
        ≤ (3 * C_zeta + 16 * Real.log 3 + 121) * (L / Real.log 2) + 129 * L :=
            add_le_add hmul1 le_rfl
      _ = (((3 * C_zeta + 16 * Real.log 3 + 121) / Real.log 2) + 129) * L := by
            rw [hmul2]; ring
      _ = K_const * L := by rw [hK_def]
  have h_part1_mul : K_const * L ≤ (1 / 8) / η := by
    calc
      K_const * L = (δ * K_const) * (L / δ) := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 640 * Real.log 2) * (1 / η) := by
          rw [hη_inv]
          exact mul_le_mul_of_nonneg_right hδ_K (by positivity)
      _ ≤ (1 / 8) * (1 / η) := mul_le_mul_of_nonneg_right (by linarith [hlog2_le1]) (by positivity)
      _ = (1 / 8) / η := by ring
  have h_part2_mul : 48 * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) ≤ (1 / 8) / η := by
    have hmul : 48 * (δ * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ)) ≤ 1 / 8 * L := by
      calc
        48 * (δ * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ)) ≤
            48 * (1 / 640 * Real.log 2) := mul_le_mul_of_nonneg_left hδ_log (by norm_num)
        _ = 3 / 40 * Real.log 2 := by ring
        _ ≤ 1 / 8 * Real.log 2 := by linarith
        _ ≤ 1 / 8 * L := mul_le_mul_of_nonneg_left hL_ge (by norm_num)
    have hdiv := div_le_div_of_nonneg_right hmul hδ_pos.le
    calc
      48 * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ)
        = (48 * (δ * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ))) / δ := by
            field_simp [hδ_pos.ne']
      _ ≤ (1 / 8 * L) / δ := hdiv
      _ = 1 / 8 * (L / δ) := by ring
      _ = (1 / 8) / η := by rw [hη_inv]; ring
  have h_upper : 4 / (σ₀ - β) ≤ (15 / 4) / η := by
    have : 3 / η + 1 / (2 * η) + (1 / 8) / η + (1 / 8) / η = (15 / 4) / η := by ring
    linarith
  have hσ_sub : (16 / 15) * η ≤ σ₀ - β := by
    have hpos : 0 < σ₀ - β := by linarith
    rw [div_le_div_iff₀ hpos hη_pos] at h_upper
    linarith
  have hβ_le : β ≤ 1 - η / 15 := by dsimp only [σ₀] at hσ_sub; linarith
  linarith [h_one_sub_β_η, hη_pos]

private lemma zeroFreeRegion_real_nonreal_small_im
    {C_zeta C_z1 δ K_const : ℝ} (hC_zeta : 0 < C_zeta)
    (hzeta_bd : ∀ σ ∈ Set.Ioc (1 : ℝ) 2,
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C_zeta)
    (hK_def : K_const = (3 * C_zeta + 16 * Real.log 3 + 121) / Real.log 2 + 129)
    (hδ_pos : 0 < δ) (hδ_K : δ * K_const ≤ 1 / 640 * Real.log 2)
    (hδ_log : δ * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) ≤ 1 / 640 * Real.log 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hreal : IsReal χ) (hχ1 : χ ≠ 1)
    {ρ : ℂ} (hρ_im : ρ.im ≠ 0)
    (hρ_re : 1 - (δ / 16) / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ ρ.re)
    (hβ_lt1 : ρ.re < 1) (hρ_zero : DirichletCharacter.LFunction χ ρ = 0)
    (hη_le : δ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 / 8)
    (ht_lt : |ρ.im| < (δ / Real.log ((q : ℝ) * (|ρ.im| + 2))) / 2) : False := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  let t : ℝ := ρ.im
  let β : ℝ := ρ.re
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  let L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  let η : ℝ := δ / L
  have hη_pos : 0 < η := div_pos hδ_pos hL_pos
  have hη_le' : η ≤ 1 / 8 := hη_le
  have ht_lt' : |t| < η / 2 := ht_lt
  let σ₀ : ℝ := 1 + η
  have hσ₀_gt1 : 1 < σ₀ := by linarith
  have hσ₀_le2 : σ₀ ≤ 2 := by linarith
  have h_one_sub_β_η : 1 - β ≤ η / 16 := by
    have h1 : 1 - β ≤ (δ / 16) / L := by linarith [hρ_re]
    rwa [div_right_comm] at h1
  have hη_inv : L / δ = 1 / η := by
    dsimp only [η]
    field_simp [hδ_pos.ne', hL_pos.ne']
  have hlog_408_le : Real.log (408 / δ) ≤ Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (le_max_left _ _) hδ_pos.le)
  have hstar_zero : DirichletCharacter.LFunction χ (star ρ) = 0 := by
    rw [LFunction_conj_of_isReal hχ1 hreal ρ, hρ_zero, star_zero]
  have hstar_ne : star ρ ≠ ρ := by
    intro heq
    have him := congr_arg Complex.im heq
    simp only [Complex.star_def, Complex.conj_im] at him
    exact hρ_im (by linarith)
  have hρ_mem : ρ ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖ρ - ((1 + η : ℝ) : ℂ)‖ ≤ |β - (1 + η)| + |t| := by
      simpa [β, t] using Complex.norm_le_abs_re_add_abs_im (ρ - ((1 + η : ℝ) : ℂ))
    rw [abs_of_neg (by linarith)] at hnorm
    linarith
  have hstar_mem : star ρ ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm, show star ρ - ((1 + η : ℝ) : ℂ) =
      star (ρ - ((1 + η : ℝ) : ℂ)) by simp, norm_star]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem
  have htwo := landau_LFunction_center_sub_two_zeros_le hχ1 hη_pos (by linarith)
    hρ_mem hstar_mem hρ_zero (Or.inl ⟨hstar_ne, hstar_zero⟩)
  have hupper_ld : -(1 / η + C_zeta) ≤
      -(logDeriv (DirichletCharacter.LFunction χ) ((1 + η : ℝ) : ℂ)).re := by
    have h1 := norm_re_logDeriv_LFunction_le_neg_logDeriv_zeta χ hσ₀_gt1
    have h2 := hzeta_bd σ₀ ⟨hσ₀_gt1, hσ₀_le2⟩
    have h3 : ((logDeriv (DirichletCharacter.LFunction χ) (σ₀ : ℂ)).re) ≤
        |((logDeriv (DirichletCharacter.LFunction χ) (σ₀ : ℂ)).re)| := le_abs_self _
    dsimp only [σ₀] at h1 h2 h3 ⊢
    rw [show 1 + η - 1 = η by ring] at h2
    linarith
  have hinv_re_ρ : ((((1 + η : ℝ) : ℂ) - ρ)⁻¹).re = (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) := by
    have hsub : ((1 + η : ℝ) : ℂ) - ρ = ((1 + η - β : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [β, t]
    rw [hsub, re_inv_add_mul_I]
    ring
  have hinv_re_star : ((((1 + η : ℝ) : ℂ) - star ρ)⁻¹).re =
      (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) := by
    have hsub : ((1 + η : ℝ) : ℂ) - star ρ = ((1 + η - β : ℝ) : ℂ) + (t : ℂ) * I := by
      apply Complex.ext <;> simp [β, t]
    rw [hsub, re_inv_add_mul_I]
  have hL2q_le : Real.log (2 * (q : ℝ)) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg t]
  have h_log408_le' : Real.log (408 / η) ≤ Real.log (408 / δ) + L := by
    have hL_le : L ≤ (q : ℝ) * (|t| + 2) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have h1 : 408 / η ≤ (408 / δ) * ((q : ℝ) * (|t| + 2)) := by
      calc
        408 / η = (408 / δ) * L := by dsimp only [η]; rw [div_div_eq_mul_div, div_mul_eq_mul_div]
        _ ≤ (408 / δ) * ((q : ℝ) * (|t| + 2)) := mul_le_mul_of_nonneg_left hL_le (by positivity)
    calc
      Real.log (408 / η) ≤ Real.log ((408 / δ) * ((q : ℝ) * (|t| + 2))) :=
        Real.log_le_log (by positivity) h1
      _ = Real.log (408 / δ) + L := Real.log_mul (by positivity) (by positivity)
  have h_comb_2 : 2 * (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) ≤
      1 / η + C_zeta + 8 * Real.log (408 / δ) + 24 * L := by
    rw [hinv_re_ρ, hinv_re_star] at htwo
    have heq2 : 2 * (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) =
        (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) + (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) := by
      ring
    linarith [htwo, hupper_ld, hL2q_le, h_log408_le', heq2]
  have h_part1 : C_zeta + 24 * L ≤ K_const * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
    have hpos : 0 ≤ C_zeta := hC_zeta.le
    have hmul : C_zeta ≤ (C_zeta / Real.log 2) * L := by
      calc
        C_zeta = C_zeta * 1 := (mul_one _).symm
        _ ≤ C_zeta * (L / Real.log 2) := mul_le_mul_of_nonneg_left h1 hpos
        _ = (C_zeta / Real.log 2) * L := by ring
    have h3pos : 0 < 3 * C_zeta + 16 * Real.log 3 + 121 := by
      have : 0 < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hcoeff : C_zeta / Real.log 2 + 24 ≤ K_const := by
      rw [hK_def]
      have : C_zeta ≤ 3 * C_zeta + 16 * Real.log 3 + 121 := by
        have : 0 < Real.log 3 := Real.log_pos (by norm_num)
        linarith
      have : C_zeta / Real.log 2 ≤ (3 * C_zeta + 16 * Real.log 3 + 121) / Real.log 2 :=
        div_le_div_of_nonneg_right this hlog2.le
      linarith
    have := mul_le_mul_of_nonneg_right hcoeff hL_pos.le
    linarith
  have h_part1_mul : K_const * L ≤ (1 / 8) / η := by
    calc
      K_const * L = (δ * K_const) * (L / δ) := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 640 * Real.log 2) * (1 / η) := by
          rw [hη_inv]
          exact mul_le_mul_of_nonneg_right hδ_K (by positivity)
      _ ≤ (1 / 8) * (1 / η) := by nlinarith [div_pos one_pos hη_pos]
      _ = (1 / 8) / η := by ring
  have h_part2_mul : 8 * Real.log (408 / δ) ≤ (1 / 8) / η := by
    have hmul : 8 * (δ * Real.log (408 / δ)) ≤ 1 / 8 * L := by
      calc
        8 * (δ * Real.log (408 / δ)) ≤ 8 * (δ * Real.log ((max 408 (Real.sqrt C_z1 + 1)) / δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_408_le hδ_pos.le) (by norm_num)
        _ ≤ 8 * (1 / 640 * Real.log 2) := mul_le_mul_of_nonneg_left hδ_log (by norm_num)
        _ = 1 / 80 * Real.log 2 := by ring
        _ ≤ 1 / 8 * L := by linarith
    have hdiv := div_le_div_of_nonneg_right hmul hδ_pos.le
    calc
      8 * Real.log (408 / δ) = (8 * (δ * Real.log (408 / δ))) / δ := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 8 * L) / δ := hdiv
      _ = (1 / 8) * (L / δ) := by ring
      _ = (1 / 8) / η := by rw [hη_inv]; ring
  have h_upper : 2 * (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) ≤ (5 / 4) / η := by
    have : 1 / η + (1 / 8) / η + (1 / 8) / η = (5 / 4) / η := by ring
    linarith
  have h_lo_num : η ≤ 1 + η - β := by linarith
  have h_hi_num : 1 + η - β ≤ (17 / 16) * η := by linarith
  have h_den_le : (1 + η - β) ^ 2 + t ^ 2 ≤ (353 / 256) * η ^ 2 := by
    have h1 : (1 + η - β) ^ 2 ≤ ((17 / 16) * η) ^ 2 :=
      sq_le_sq' (by linarith) h_hi_num
    have h2 : t ^ 2 ≤ (η / 2) ^ 2 := by
      have hsq := sq_le_sq' (by linarith [neg_abs_le t] : -(η / 2) ≤ t)
        (by linarith [le_abs_self t] : t ≤ η / 2)
      exact hsq
    nlinarith
  have h_lower : (512 / 353) / η ≤ 2 * (1 + η - β) / ((1 + η - β) ^ 2 + t ^ 2) := by
    have hnum : 2 * η ≤ 2 * (1 + η - β) := by linarith
    have hden_pos : 0 < (1 + η - β) ^ 2 + t ^ 2 := by positivity
    calc
      (512 / 353) / η = (2 * η) / ((353 / 256) * η ^ 2) := by
          field_simp [hη_pos.ne']
          ring
      _ ≤ (2 * (1 + η - β)) / ((353 / 256) * η ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * (1 + η - β)) / ((1 + η - β) ^ 2 + t ^ 2) :=
          div_le_div_of_nonneg_left (by linarith) hden_pos h_den_le
  have hcmp : (512 / 353 : ℝ) / η ≤ (5 / 4) / η := h_lower.trans h_upper
  have hmul : (512 / 353 : ℝ) ≤ 5 / 4 := by
    have := mul_le_mul_of_nonneg_right hcmp hη_pos.le
    field_simp [hη_pos.ne'] at this
    linarith
  norm_num at hmul

/-- Classical zero-free region off the real axis for real non-principal characters:
there exists `c > 0` such that for any real `χ ≠ 1`, `L(s, χ) ≠ 0` whenever `Im s ≠ 0` and
`1 - c / Real.log (q * (|Im s| + 2)) ≤ Re s`. -/
theorem zeroFreeRegion_real_nonreal :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      IsReal χ → χ ≠ 1 → ∀ s : ℂ, s.im ≠ 0 →
        1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨C_zeta, hC_zeta, hzeta_bd⟩ := neg_logDeriv_riemannZeta_real_le
  obtain ⟨C_z1, hC_z1, hz1_bd⟩ := landau_zetaOne_center_exists
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K_const : ℝ := (3 * C_zeta + 16 * Real.log 3 + 121) / Real.log 2 + 129
  obtain ⟨δ, hδ_pos, hδ_le_a, hδ_K, hδ_log⟩ :=
    exists_small_delta (Real.log 2 / 8) (max 408 (Real.sqrt C_z1 + 1)) K_const (1 / 640 * Real.log 2)
      (by positivity) (by positivity) (by positivity) (by positivity)
  let c : ℝ := δ / 16
  refine ⟨c, by positivity, fun {q} _ χ hreal hχ1 ρ hρ_im hρ_re hρ_zero ↦ ?_⟩
  by_cases hre1 : 1 ≤ ρ.re
  · exact LFunction_ne_zero_on_re_one χ hre1 (Or.inl hχ1) hρ_zero
  push Not at hre1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL_ge : Real.log 2 ≤ Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
  have hL_pos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := lt_of_lt_of_le hlog2 hL_ge
  have hη_le : δ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 1 / 8 := by
    rw [div_le_iff₀ hL_pos]
    nlinarith
  by_cases ht_ge : (δ / Real.log ((q : ℝ) * (|ρ.im| + 2))) / 2 ≤ |ρ.im|
  · exact zeroFreeRegion_real_nonreal_large_im hC_zeta hC_z1 hzeta_bd hz1_bd rfl
      hδ_pos hδ_K hδ_log χ hreal hχ1 hρ_re hre1 hρ_zero hη_le ht_ge
  · push Not at ht_ge
    exact zeroFreeRegion_real_nonreal_small_im hC_zeta hzeta_bd rfl
      hδ_pos hδ_K hδ_log χ hreal hχ1 hρ_im hρ_re hre1 hρ_zero hη_le ht_ge

/-- For a real non-principal character `χ`, there is at most one real zero `β` in the
classical zero-free interval `[1 - c / Real.log (2 * q), 1]`, and any such zero satisfies
`β < 1` and is simple (`analyticOrderNatAt (LFunction χ) β = 1`). -/
theorem zeroFreeRegion_real_at_most_one :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      IsReal χ → χ ≠ 1 →
      Set.Subsingleton {β : ℝ | 1 - c / Real.log (2 * (q : ℝ)) ≤ β ∧
        DirichletCharacter.LFunction χ (β : ℂ) = 0} ∧
      ∀ β : ℝ, 1 - c / Real.log (2 * (q : ℝ)) ≤ β →
        DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        β < 1 ∧ analyticOrderNatAt (DirichletCharacter.LFunction χ) (β : ℂ) = 1 := by
  obtain ⟨C_zeta, hC_zeta, hzeta_bd⟩ := neg_logDeriv_riemannZeta_real_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K_const : ℝ := C_zeta / Real.log 2 + 24
  obtain ⟨δ, hδ_pos, hδ_le_a, hδ_K, hδ_log⟩ :=
    exists_small_delta (Real.log 2 / 8) 408 K_const (1 / 64 * Real.log 2)
      (by positivity) (by norm_num) (by positivity) (by positivity)
  let c : ℝ := δ / 16
  refine ⟨c, by positivity, fun {q} _ χ hreal hχ1 ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  let L : ℝ := Real.log (2 * (q : ℝ))
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  let η : ℝ := δ / L
  have hη_pos : 0 < η := div_pos hδ_pos hL_pos
  have hη_le : η ≤ 1 / 8 := by
    rw [div_le_iff₀ hL_pos]
    nlinarith
  let σ₀ : ℝ := 1 + η
  have hσ₀_gt1 : 1 < σ₀ := by linarith
  have hσ₀_le2 : σ₀ ≤ 2 := by linarith
  have hupper_ld : -(1 / η + C_zeta) ≤
      -(logDeriv (DirichletCharacter.LFunction χ) ((1 + η : ℝ) : ℂ)).re := by
    have h1 := norm_re_logDeriv_LFunction_le_neg_logDeriv_zeta χ hσ₀_gt1
    have h2 := hzeta_bd σ₀ ⟨hσ₀_gt1, hσ₀_le2⟩
    have h3 : ((logDeriv (DirichletCharacter.LFunction χ) (σ₀ : ℂ)).re) ≤
        |((logDeriv (DirichletCharacter.LFunction χ) (σ₀ : ℂ)).re)| := le_abs_self _
    dsimp only [σ₀] at h1 h2 h3 ⊢
    rw [show 1 + η - 1 = η by ring] at h2
    linarith
  have hη_inv : L / δ = 1 / η := by dsimp only [η]; rw [one_div_div]
  have h_log408_le : Real.log (408 / η) ≤ Real.log (408 / δ) + L := by
    have hL_le : L ≤ 2 * (q : ℝ) := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have h1 : 408 / η ≤ (408 / δ) * (2 * (q : ℝ)) := by
      calc
        408 / η = (408 / δ) * L := by dsimp only [η]; rw [div_div_eq_mul_div, div_mul_eq_mul_div]
        _ ≤ (408 / δ) * (2 * (q : ℝ)) := mul_le_mul_of_nonneg_left hL_le (by positivity)
    calc
      Real.log (408 / η) ≤ Real.log ((408 / δ) * (2 * (q : ℝ))) :=
        Real.log_le_log (by positivity) h1
      _ = Real.log (408 / δ) + L := Real.log_mul (by positivity) (by positivity)
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have h_err : C_zeta + 8 * Real.log (408 / δ) + 24 * L ≤ (1 / 4) / η := by
    have h_p1 : C_zeta + 24 * L ≤ K_const * L := by
      have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
      have hmul : C_zeta ≤ (C_zeta / Real.log 2) * L := by
        calc
          C_zeta = C_zeta * 1 := (mul_one _).symm
          _ ≤ C_zeta * (L / Real.log 2) := mul_le_mul_of_nonneg_left h1 hC_zeta.le
          _ = (C_zeta / Real.log 2) * L := by ring
      dsimp only [K_const]
      linarith
    have h_p1_mul : K_const * L ≤ (1 / 8) / η := by
      calc
        K_const * L = (δ * K_const) * (L / δ) := by field_simp [hδ_pos.ne']
        _ ≤ (1 / 64 * Real.log 2) * (1 / η) := by
            rw [hη_inv]
            exact mul_le_mul_of_nonneg_right hδ_K (by positivity)
        _ ≤ (1 / 8) * (1 / η) := by nlinarith [div_pos one_pos hη_pos]
        _ = (1 / 8) / η := by ring
    have h_p2_mul : 8 * Real.log (408 / δ) ≤ (1 / 8) / η := by
      have hmul : 8 * (δ * Real.log (408 / δ)) ≤ 1 / 8 * L := by
        calc
          8 * (δ * Real.log (408 / δ)) ≤ 8 * (1 / 64 * Real.log 2) := by linarith
          _ = 1 / 8 * Real.log 2 := by ring
          _ ≤ 1 / 8 * L := by linarith
      have hdiv := div_le_div_of_nonneg_right hmul hδ_pos.le
      calc
        8 * Real.log (408 / δ) = (8 * (δ * Real.log (408 / δ))) / δ := by field_simp [hδ_pos.ne']
        _ ≤ (1 / 8 * L) / δ := hdiv
        _ = 1 / 8 * (L / δ) := by ring
        _ = (1 / 8) / η := by rw [hη_inv]; ring
    have : (1 / 8) / η + (1 / 8) / η = (1 / 4) / η := by ring
    linarith
  have hmem_of_ge : ∀ β : ℝ, 1 - c / L ≤ β → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      β < 1 ∧ (β : ℂ) ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ) ∧
        (16 / 17) / η ≤ ((((1 + η : ℝ) : ℂ) - (β : ℂ))⁻¹).re := by
    intro β hβ_ge hβ_zero
    have hβ_lt : β < 1 := by
      by_contra hge
      push Not at hge
      exact LFunction_ne_zero_on_re_one χ (by simpa using hge) (Or.inl hχ1) hβ_zero
    have hsub_hi : 1 + η - β ≤ (17 / 16) * η := by
      dsimp only [c, η] at hβ_ge ⊢
      rw [div_right_comm] at hβ_ge
      linarith
    have hmem : (β : ℂ) ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, show (β : ℂ) - ((1 + η : ℝ) : ℂ) =
        ((β - (1 + η) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith)]
      linarith
    have hinv_ge : (16 / 17) / η ≤ ((((1 + η : ℝ) : ℂ) - (β : ℂ))⁻¹).re := by
      rw [show ((1 + η : ℝ) : ℂ) - (β : ℂ) = ((1 + η - β : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_inv, Complex.ofReal_re]
      calc
        (16 / 17) / η = ((17 / 16) * η)⁻¹ := by
            have hne : η ≠ 0 := hη_pos.ne'
            field_simp [hne]
        _ ≤ (1 + η - β)⁻¹ := inv_anti₀ (by linarith) hsub_hi
    exact ⟨hβ_lt, hmem, hinv_ge⟩
  constructor
  · intro β₁ h₁ β₂ h₂
    by_contra hne
    obtain ⟨_, hmem₁, hge₁⟩ := hmem_of_ge β₁ h₁.1 h₁.2
    obtain ⟨_, hmem₂, hge₂⟩ := hmem_of_ge β₂ h₂.1 h₂.2
    have hne_c : (β₂ : ℂ) ≠ (β₁ : ℂ) := by exact_mod_cast Ne.symm hne
    have htwo := landau_LFunction_center_sub_two_zeros_le hχ1 hη_pos (by linarith)
      hmem₁ hmem₂ h₁.2 (Or.inl ⟨hne_c, h₂.2⟩)
    rw [show Real.log (2 * (q : ℝ)) = L from rfl] at htwo
    have hcontr : (32 / 17) / η ≤ (5 / 4) / η := by
      have h1 : (16 / 17) / η + (16 / 17) / η = (32 / 17) / η := by ring
      have h2 : 1 / η + (1 / 4) / η = (5 / 4) / η := by ring
      linarith [htwo, hupper_ld, h_err, h_log408_le, hge₁, hge₂, h1, h2]
    have : (32 / 17 : ℝ) ≤ 5 / 4 := by
      have := mul_le_mul_of_nonneg_right hcontr hη_pos.le
      field_simp [hη_pos.ne'] at this
      linarith
    norm_num at this
  · intro β hβ_ge hβ_zero
    obtain ⟨hβ_lt, hmem, hge⟩ := hmem_of_ge β hβ_ge hβ_zero
    refine ⟨hβ_lt, ?_⟩
    have hd_ne : deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
      intro hd0
      have htwo := landau_LFunction_center_sub_two_zeros_le hχ1 hη_pos (by linarith)
        hmem hmem hβ_zero (Or.inr ⟨rfl, hd0⟩)
      rw [show Real.log (2 * (q : ℝ)) = L from rfl] at htwo
      have hcontr : (32 / 17) / η ≤ (5 / 4) / η := by
        have h1 : (16 / 17) / η + (16 / 17) / η = (32 / 17) / η := by ring
        have h2 : 1 / η + (1 / 4) / η = (5 / 4) / η := by ring
        linarith [htwo, hupper_ld, h_err, h_log408_le, hge, h1, h2]
      have : (32 / 17 : ℝ) ≤ 5 / 4 := by
        have := mul_le_mul_of_nonneg_right hcontr hη_pos.le
        field_simp [hη_pos.ne'] at this
        linarith
      norm_num at this
    have hf_diff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      DirichletCharacter.differentiable_LFunction hχ1
    let g : ℂ → ℂ := dslope (DirichletCharacter.LFunction χ) (β : ℂ)
    have hg_diff : Differentiable ℂ g := by
      rw [← differentiableOn_univ]
      exact (differentiableOn_dslope (isOpen_univ.mem_nhds (Set.mem_univ (β : ℂ)))).mpr
        hf_diff.differentiableOn
    have hf_an : AnalyticAt ℂ (DirichletCharacter.LFunction χ) (β : ℂ) :=
      (hf_diff.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
    have hg_an : AnalyticAt ℂ g (β : ℂ) :=
      (hg_diff.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
    have hg_ne : g (β : ℂ) ≠ 0 := by simpa [g, dslope_same] using hd_ne
    have hfac : ∀ᶠ z in 𝓝 (β : ℂ), DirichletCharacter.LFunction χ z = (z - (β : ℂ)) ^ 1 • g z := by
      filter_upwards with z
      by_cases hz : z = (β : ℂ)
      · subst hz; simp [hβ_zero]
      · simp only [pow_one, smul_eq_mul, g, dslope_of_ne _ hz, slope_def_module, hβ_zero, sub_zero]
        have hne : z - (β : ℂ) ≠ 0 := sub_ne_zero.mpr hz
        field_simp [hne]
    have hord : analyticOrderAt (DirichletCharacter.LFunction χ) (β : ℂ) = (1 : ℕ) :=
      (hf_an.analyticOrderAt_eq_natCast).2 ⟨g, hg_an, hg_ne, hfac⟩
    simp [analyticOrderNatAt, hord]

/-- Unified classical zero-free region for all Dirichlet L-functions: there exists `c > 0`
such that inside `1 - c / Real.log (q * (|Im s| + 2)) ≤ Re s` (`s ≠ 1` if `χ = 1`),
`L(s, χ) ≠ 0` unless `χ` is real non-principal and `s` is its unique simple real zero in that strip. -/
theorem zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (χ ≠ 1 ∨ s ≠ 1) →
      1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re →
      DirichletCharacter.LFunction χ s = 0 →
      IsReal χ ∧ χ ≠ 1 ∧ s.im = 0 ∧ s.re < 1 ∧
        analyticOrderNatAt (DirichletCharacter.LFunction χ) s = 1 ∧
        ∀ t : ℝ, 1 - c / Real.log (2 * (q : ℝ)) ≤ t →
          DirichletCharacter.LFunction χ (t : ℂ) = 0 → t = s.re := by
  obtain ⟨c₁, hc₁, hcomp⟩ := zeroFreeRegion_complex
  obtain ⟨c₂, hc₂, hprin⟩ := zeroFreeRegion_principal
  obtain ⟨c₃, hc₃, hrnr⟩ := zeroFreeRegion_real_nonreal
  obtain ⟨c₄, hc₄, hrreal⟩ := zeroFreeRegion_real_at_most_one
  let c : ℝ := min (min c₁ c₂) (min c₃ c₄)
  have hc_pos : 0 < c := lt_min (lt_min hc₁ hc₂) (lt_min hc₃ hc₄)
  refine ⟨c, hc_pos, fun {q} _ χ s hχs hs_re hs_zero ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  rcases eq_or_ne χ 1 with rfl | hχ1
  · have hs1 : s ≠ 1 := hχs.resolve_left (fun h ↦ h rfl)
    have hc2_le : 1 - c₂ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
      have : c ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
      have : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₂ / Real.log ((q : ℝ) * (|s.im| + 2)) :=
        div_le_div_of_nonneg_right this hL_pos.le
      linarith
    exact False.elim (hprin s hs1 hc2_le hs_zero)
  rcases trichotomy χ with h_prin | hquad | hcx
  · exact False.elim (hχ1 ((isPrincipal_iff).mp h_prin))
  · have hreal : IsReal χ := (isReal_iff_sq_eq_one χ).mpr hquad.2
    have him0 : s.im = 0 := by
      by_contra him_ne
      have hc3_le : 1 - c₃ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
        have : c ≤ c₃ := (min_le_right _ _).trans (min_le_left _ _)
        have : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₃ / Real.log ((q : ℝ) * (|s.im| + 2)) :=
          div_le_div_of_nonneg_right this hL_pos.le
        linarith
      exact hrnr χ hreal hχ1 s him_ne hc3_le hs_zero
    have hs_real : s = (s.re : ℂ) := Complex.ext rfl (by simp [him0])
    have hs_zero_r : DirichletCharacter.LFunction χ (s.re : ℂ) = 0 := by rwa [← hs_real]
    have hc4_le : 1 - c₄ / Real.log (2 * (q : ℝ)) ≤ s.re := by
      have hL0 : Real.log ((q : ℝ) * (|s.im| + 2)) = Real.log (2 * (q : ℝ)) := by
        simp [him0, mul_comm]
      rw [hL0] at hs_re
      have : c ≤ c₄ := (min_le_right _ _).trans (min_le_right _ _)
      have hL2q : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by linarith)
      have : c / Real.log (2 * (q : ℝ)) ≤ c₄ / Real.log (2 * (q : ℝ)) :=
        div_le_div_of_nonneg_right this hL2q.le
      linarith
    obtain ⟨hsub, hprop⟩ := hrreal χ hreal hχ1
    obtain ⟨hre_lt, hord⟩ := hprop s.re hc4_le hs_zero_r
    refine ⟨hreal, hχ1, him0, hre_lt, ?_, fun t ht_ge ht_zero ↦ ?_⟩
    · rwa [hs_real]
    · have ht_c4 : 1 - c₄ / Real.log (2 * (q : ℝ)) ≤ t := by
        have : c ≤ c₄ := (min_le_right _ _).trans (min_le_right _ _)
        have hL2q : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by linarith)
        have : c / Real.log (2 * (q : ℝ)) ≤ c₄ / Real.log (2 * (q : ℝ)) :=
          div_le_div_of_nonneg_right this hL2q.le
        linarith
      exact hsub ⟨ht_c4, ht_zero⟩ ⟨hc4_le, hs_zero_r⟩
  · have hc1_le : 1 - c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
      have : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
      have : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) :=
        div_le_div_of_nonneg_right this hL_pos.le
      linarith
    exact False.elim (hcomp χ hcx s hc1_le hs_zero)

private lemma norm_partial_char_sum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ q := by
  let k0 : ℕ := n / q
  let r : ℕ := n % q
  have hsplit : Finset.Icc 1 n = (Finset.range k0).biUnion (fun j ↦ Finset.Ioc (j * q) (j * q + q)) ∪
      Finset.Ioc (k0 * q) n := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hm1, hmn⟩
      by_cases hm_le : m ≤ k0 * q
      · left
        have hm_pos : 0 < m := hm1
        have hq_pos : 0 < q := NeZero.pos q
        refine ⟨(m - 1) / q, ?_, ?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul hq_pos]
          omega
        · have hdm := Nat.div_add_mod (m - 1) q
          rw [mul_comm q _] at hdm
          have hmod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          omega
        · have hdm := Nat.div_add_mod (m - 1) q
          rw [mul_comm q _] at hdm
          have hmod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          omega
      · right
        omega
    · rintro (⟨j, hj, hm1, hm2⟩ | ⟨hm1, hm2⟩)
      · have : j + 1 ≤ k0 := hj
        have hle : j * q + q ≤ k0 * q := by nlinarith
        have hkq : k0 * q ≤ n := Nat.div_mul_le_self n q
        omega
      · omega
  have hdisj_all : ∀ j₁ ∈ Finset.range k0, ∀ j₂ ∈ Finset.range k0, j₁ ≠ j₂ →
      Disjoint (Finset.Ioc (j₁ * q) (j₁ * q + q)) (Finset.Ioc (j₂ * q) (j₂ * q + q)) := by
    intro j₁ _ j₂ _ hne
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_Ioc] at hm1 hm2
    rcases lt_or_gt_of_ne hne with h | h
    · have : j₁ + 1 ≤ j₂ := h
      nlinarith
    · have : j₂ + 1 ≤ j₁ := h
      nlinarith
  have hdisj_tail : Disjoint ((Finset.range k0).biUnion (fun j ↦ Finset.Ioc (j * q) (j * q + q)))
      (Finset.Ioc (k0 * q) n) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ioc] at hm1 hm2
    rcases hm1 with ⟨j, hj, _, hm_hi⟩
    have : j + 1 ≤ k0 := hj
    nlinarith
  have hsum_blocks : ∑ k ∈ (Finset.range k0).biUnion (fun j ↦ Finset.Ioc (j * q) (j * q + q)), χ k = 0 := by
    rw [Finset.sum_biUnion hdisj_all]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    classical
    exact (sum_Ioc_period_eq χ (j * q)).trans (ite_eq_right_iff.mpr fun h ↦ absurd h hχ)
  rw [hsplit, Finset.sum_union hdisj_tail, hsum_blocks, zero_add]
  have hcard : (Finset.Ioc (k0 * q) n).card ≤ q := by
    rw [Nat.card_Ioc]
    have hdiv := Nat.div_add_mod n q
    rw [mul_comm q k0] at hdiv
    have hmod := Nat.mod_lt n (NeZero.pos q)
    omega
  calc
    ‖∑ k ∈ Finset.Ioc (k0 * q) n, χ k‖ ≤ ∑ _k ∈ Finset.Ioc (k0 * q) n, ‖χ _k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Ioc (k0 * q) n, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ norm_char_le_one χ _
    _ = ((Finset.Ioc (k0 * q) n).card : ℝ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast hcard

/-- Near `s = 1` (`1 - 1 / (2 * log (q + 2)) ≤ Re s ≤ 2`, `|Im s| ≤ 1`), `L(s, χ)` is bounded
by `C * log (q + 2)` for every non-principal character `χ` modulo `q ≥ 2`. -/
theorem norm_LFunction_near_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (_hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ s : ℂ, 1 - 1 / (2 * Real.log (q + 2)) ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 →
        ‖DirichletCharacter.LFunction χ s‖ ≤ C * Real.log (q + 2) := by
  refine ⟨18, by norm_num, fun {q} _ hq {χ} hχ s hs_lo hs_hi him ↦ ?_⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < q := by linarith
  have hlog_q2 : 1 ≤ Real.log (q + 2) := by
    have : Real.exp 1 ≤ (q : ℝ) + 2 := by
      have := Real.exp_one_lt_d9
      linarith
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) this
  have hs_pos : 0 < s.re := by
    have : 1 / (2 * Real.log (q + 2)) ≤ 1 / 2 := by
      rw [one_div_le_one_div (by positivity) (by norm_num)]
      linarith
    linarith
  have hs_ge_half : 1 / 2 ≤ s.re := by
    have : 1 / (2 * Real.log (q + 2)) ≤ 1 / 2 := by
      rw [one_div_le_one_div (by positivity) (by norm_num)]
      linarith
    linarith
  rw [LFunction_eq_mul_integral_of_zero_lt_re hχ hs_pos]
  let S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k
  have hS_eq : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k = S t := fun _ ↦ rfl
  have hS_meas : Measurable S :=
    (measurable_from_top (f := fun k : ℕ ↦ ∑ x ∈ Finset.Icc 1 k, χ x)).comp Nat.measurable_floor
  have hS_q : ∀ t : ℝ, ‖S t‖ ≤ q := fun t ↦ norm_partial_char_sum_le hχ ⌊t⌋₊
  have hS_t : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ t := fun t ht ↦ by
    calc
      ‖S t‖ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_char_le_one χ _)
      _ = (⌊t⌋₊ : ℝ) := by simp
      _ ≤ t := Nat.floor_le ht
  have hint_full : IntegrableOn (fun t : ℝ ↦ S t * (t : ℂ) ^ (-s - 1)) (Set.Ioi 1) := by
    have hdom : IntegrableOn (fun t : ℝ ↦ (q : ℝ) * t ^ (-s.re - 1)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul (q : ℝ)
    refine hdom.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
    · exact (hS_meas.mul ((Complex.continuous_ofReal.measurable).pow_const (-s - 1))).aestronglyMeasurable
    · have ht_pos : (0 : ℝ) < t := lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simpa using mul_le_mul_of_nonneg_right (hS_q t) (Real.rpow_nonneg ht_pos.le _)
  have hint_Ioc : IntegrableOn (fun t : ℝ ↦ S t * (t : ℂ) ^ (-s - 1)) (Set.Ioc 1 q) :=
    hint_full.mono_set Set.Ioc_subset_Ioi_self
  have hint_Ioi_q : IntegrableOn (fun t : ℝ ↦ S t * (t : ℂ) ^ (-s - 1)) (Set.Ioi q) :=
    hint_full.mono_set (Set.Ioi_subset_Ioi (by linarith))
  have hsplit : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) q ∪ Set.Ioi (q : ℝ) := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      by_cases htq : t ≤ q
      · exact Or.inl ⟨ht, htq⟩
      · exact Or.inr (lt_of_not_ge htq)
    · rintro (⟨ht, _⟩ | htq)
      · exact ht
      · linarith
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) q) (Set.Ioi (q : ℝ)) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    linarith [ht1.2, Set.mem_Ioi.mp ht2]
  have hint_split : ∫ t in Set.Ioi (1 : ℝ), S t * (t : ℂ) ^ (-s - 1) =
      (∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)) +
        ∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1) := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_Ioi_q
  have hq_rpow : (q : ℝ) ^ (1 - s.re) ≤ 2 := by
    have h_exp_le : 1 - s.re ≤ 1 / (2 * Real.log (q + 2)) := by linarith
    have h1 : (q : ℝ) ^ (1 - s.re) ≤ (q : ℝ) ^ (1 / (2 * Real.log (q + 2))) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) h_exp_le
    have h2 : (q : ℝ) ^ (1 / (2 * Real.log (q + 2))) ≤ ((q : ℝ) + 2) ^ (1 / (2 * Real.log (q + 2))) :=
      Real.rpow_le_rpow hq_pos.le (by linarith) (by positivity)
    have h3 : ((q : ℝ) + 2) ^ (1 / (2 * Real.log (q + 2))) = Real.exp (1 / 2) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      have hne : Real.log (q + 2) ≠ 0 := by linarith
      field_simp [hne]
    have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith
  have hIoc_bd : ‖∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)‖ ≤ 2 * Real.log (q + 2) := by
    have hdom_Ioc : IntegrableOn (fun t : ℝ ↦ (2 : ℝ) * t⁻¹) (Set.Ioc 1 q) := by
      refine ContinuousOn.integrableOn_Icc (f := fun t : ℝ ↦ 2 * t⁻¹) ?_ |>.mono_set Set.Ioc_subset_Icc_self
      intro t ht
      exact (continuousAt_const.mul (continuousAt_inv₀ (by linarith [ht.1]))).continuousWithinAt
    have hmono : ∫ t in Set.Ioc (1 : ℝ) q, ‖S t * (t : ℂ) ^ (-s - 1)‖ ≤
        ∫ t in Set.Ioc (1 : ℝ) q, (2 : ℝ) * t⁻¹ := by
      refine MeasureTheory.setIntegral_mono_on (hint_Ioc.norm) hdom_Ioc measurableSet_Ioc fun t ht ↦ ?_
      have ht1 : 1 ≤ t := ht.1.le
      have ht_pos : 0 < t := by linarith
      have htq : t ≤ q := ht.2
      have hnorm : ‖S t * (t : ℂ) ^ (-s - 1)‖ ≤ t ^ (-s.re) := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
        have heq : (t : ℝ) * t ^ (-s.re - 1) = t ^ (-s.re) := by
          conv_rhs => rw [show (-s.re : ℝ) = 1 + (-s.re - 1) by ring, Real.rpow_add ht_pos,
            Real.rpow_one]
        calc
          ‖S t‖ * t ^ ((-s - 1).re) ≤ t * t ^ (-s.re - 1) := by
              simpa using mul_le_mul_of_nonneg_right (hS_t t ht_pos.le) (Real.rpow_nonneg ht_pos.le _)
          _ = t ^ (-s.re) := heq
      have ht_pow : t ^ (-s.re) ≤ 2 * t⁻¹ := by
        have heq : t ^ (-s.re) = t ^ (1 - s.re) * t⁻¹ := by
          rw [show (-s.re : ℝ) = (1 - s.re) + (-1 : ℝ) by ring, Real.rpow_add ht_pos,
            Real.rpow_neg_one]
        have ht1s : t ^ (1 - s.re) ≤ 2 := by
          by_cases hre1 : s.re ≤ 1
          · exact (Real.rpow_le_rpow ht_pos.le htq (by linarith)).trans hq_rpow
          · push Not at hre1
            have : t ^ (1 - s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
            linarith
        rw [heq]
        exact mul_le_mul_of_nonneg_right ht1s (by positivity)
      exact hnorm.trans ht_pow
    have heval : ∫ t in Set.Ioc (1 : ℝ) q, (2 : ℝ) * t⁻¹ = 2 * Real.log q := by
      rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ q),
        integral_inv (by intro hx; rw [Set.uIcc_of_le (by linarith)] at hx; linarith [hx.1]),
        div_one]
    have hlog_le : Real.log q ≤ Real.log (q + 2) := Real.log_le_log hq_pos (by linarith)
    calc
      ‖∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)‖
        ≤ ∫ t in Set.Ioc (1 : ℝ) q, ‖S t * (t : ℂ) ^ (-s - 1)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) q, (2 : ℝ) * t⁻¹ := hmono
      _ = 2 * Real.log q := heval
      _ ≤ 2 * Real.log (q + 2) := by linarith
  have hIoi_bd : ‖∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1)‖ ≤ 4 := by
    have hdom_q : IntegrableOn (fun t : ℝ ↦ (q : ℝ) * t ^ (-s.re - 1)) (Set.Ioi q) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hq_pos).const_mul (q : ℝ)
    have hmono : ∫ t in Set.Ioi (q : ℝ), ‖S t * (t : ℂ) ^ (-s - 1)‖ ≤
        ∫ t in Set.Ioi (q : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
      refine MeasureTheory.setIntegral_mono_on hint_Ioi_q.norm hdom_q measurableSet_Ioi fun t ht ↦ ?_
      have ht_pos : (0 : ℝ) < t := lt_trans hq_pos (Set.mem_Ioi.mp ht)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simpa using mul_le_mul_of_nonneg_right (hS_q t) (Real.rpow_nonneg ht_pos.le _)
    have heval_rpow : ∫ t in Set.Ioi (q : ℝ), t ^ (-s.re - 1) = (q : ℝ) ^ (-s.re) / s.re := by
      have hint_r : IntegrableOn (fun t : ℝ ↦ t ^ (-s.re - 1)) (Set.Ioi q) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hq_pos
      have htend := intervalIntegral_tendsto_integral_Ioi (q : ℝ) hint_r tendsto_id
      have hev : ∀ᶠ R in atTop, ∫ t in (q : ℝ)..R, t ^ (-s.re - 1) =
          (R ^ (-s.re) - (q : ℝ) ^ (-s.re)) / (-s.re) := by
        filter_upwards [eventually_ge_atTop (q : ℝ)] with R hR
        have h0 : (0 : ℝ) ∉ Set.uIcc (q : ℝ) R := by
          rw [Set.uIcc_of_le hR]; intro hmem; linarith [hmem.1]
        rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show -s.re - 1 + 1 = -s.re by ring]
      have hlim : Tendsto (fun R : ℝ ↦ (R ^ (-s.re) - (q : ℝ) ^ (-s.re)) / (-s.re)) atTop
          (𝓝 ((q : ℝ) ^ (-s.re) / s.re)) := by
        have h0 : Tendsto (fun R : ℝ ↦ R ^ (-s.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hs_pos
        have hdiv := (h0.sub (tendsto_const_nhds (x := (q : ℝ) ^ (-s.re)))).div_const (-s.re)
        have hval : (0 - (q : ℝ) ^ (-s.re)) / (-s.re) = (q : ℝ) ^ (-s.re) / s.re := by
          have hs_ne : s.re ≠ 0 := hs_pos.ne'
          field_simp [hs_ne]
          ring
        rwa [hval] at hdiv
      exact tendsto_nhds_unique htend (hlim.congr' (hev.mono fun _ h ↦ h.symm))
    have hmul_val : (q : ℝ) * ((q : ℝ) ^ (-s.re) / s.re) = (q : ℝ) ^ (1 - s.re) / s.re := by
      rw [show (1 - s.re : ℝ) = 1 + (-s.re) by ring, Real.rpow_add hq_pos, Real.rpow_one]
      ring
    calc
      ‖∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1)‖
        ≤ ∫ t in Set.Ioi (q : ℝ), ‖S t * (t : ℂ) ^ (-s - 1)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (q : ℝ), (q : ℝ) * t ^ (-s.re - 1) := hmono
      _ = (q : ℝ) * ∫ t in Set.Ioi (q : ℝ), t ^ (-s.re - 1) := MeasureTheory.integral_const_mul _ _
      _ = (q : ℝ) ^ (1 - s.re) / s.re := by rw [heval_rpow, hmul_val]
      _ ≤ 2 / (1 / 2) := div_le_div₀ (by positivity) hq_rpow (by norm_num) hs_ge_half
      _ = 4 := by norm_num
  have hs_norm : ‖s‖ ≤ 3 := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_pos hs_pos]
      _ ≤ 2 + 1 := add_le_add hs_hi him
      _ = 3 := by norm_num
  rw [norm_mul]
  change ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), S t * (t : ℂ) ^ (-s - 1)‖ ≤ 18 * Real.log (q + 2)
  rw [hint_split]
  have hint_bd : ‖(∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)) +
      ∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1)‖ ≤ 6 * Real.log (q + 2) := by
    calc
      ‖(∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)) +
          ∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1)‖
        ≤ ‖∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)‖ +
            ‖∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1)‖ := norm_add_le _ _
      _ ≤ 2 * Real.log (q + 2) + 4 := add_le_add hIoc_bd hIoi_bd
      _ ≤ 6 * Real.log (q + 2) := by linarith
  calc
    ‖s‖ * ‖(∫ t in Set.Ioc (1 : ℝ) q, S t * (t : ℂ) ^ (-s - 1)) +
        ∫ t in Set.Ioi (q : ℝ), S t * (t : ℂ) ^ (-s - 1)‖
      ≤ 3 * (6 * Real.log (q + 2)) := mul_le_mul hs_norm hint_bd (norm_nonneg _) (by norm_num)
    _ = 18 * Real.log (q + 2) := by ring

/-- Cauchy derivative bound on the real axis near `s = 1`:
`‖L'(σ, χ)‖ ≤ C * (log (q + 2))²` for `σ ∈ [1 - 1 / (4 log (q + 2)), 1]`. -/
theorem norm_deriv_LFunction_near_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (_hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      ∀ σ : ℝ, 1 - 1 / (4 * Real.log (q + 2)) ≤ σ → σ ≤ 1 →
        ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ C * (Real.log (q + 2)) ^ 2 := by
  obtain ⟨C₀, hC₀, hnear⟩ := norm_LFunction_near_one_le
  refine ⟨4 * C₀, by positivity, fun {q} _ hq {χ} hχ σ hσ_lo hσ_hi ↦ ?_⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog_q2 : 1 ≤ Real.log (q + 2) := by
    have : Real.exp 1 ≤ (q : ℝ) + 2 := by
      have := Real.exp_one_lt_d9; linarith
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) this
  let r : ℝ := 1 / (4 * Real.log (q + 2))
  have hr_pos : 0 < r := by positivity
  have hr_le_quarter : r ≤ 1 / 4 := by
    dsimp only [r]
    rw [one_div_le_one_div (by positivity) (by norm_num)]
    linarith
  have hcauchy : ∮ w in C((σ : ℂ), r), (1 / (w - (σ : ℂ)) ^ 2) •
      DirichletCharacter.LFunction χ w =
      (2 * Real.pi * Complex.I) • deriv (DirichletCharacter.LFunction χ) (σ : ℂ) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.deriv_eq_smul_circleIntegral
      hr_pos
  have hsphere : ∀ w ∈ Metric.sphere (σ : ℂ) r,
      ‖(1 / (w - (σ : ℂ)) ^ 2) • DirichletCharacter.LFunction χ w‖ ≤
        (1 / r ^ 2) * (C₀ * Real.log (q + 2)) := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hw_re_lo : 1 - 1 / (2 * Real.log (q + 2)) ≤ w.re := by
      have hre : |w.re - σ| ≤ r := by
        calc
          |w.re - σ| = |(w - (σ : ℂ)).re| := by simp
          _ ≤ ‖w - (σ : ℂ)‖ := Complex.abs_re_le_norm _
          _ = r := hw
      have h1 : σ - r ≤ w.re := by linarith [(abs_le.mp hre).1]
      have h2 : 1 / (4 * Real.log (q + 2)) + 1 / (4 * Real.log (q + 2)) = 1 / (2 * Real.log (q + 2)) := by
        ring
      dsimp only [r] at h1
      linarith
    have hw_re_hi : w.re ≤ 2 := by
      have hre : |w.re - σ| ≤ r := by
        calc
          |w.re - σ| = |(w - (σ : ℂ)).re| := by simp
          _ ≤ ‖w - (σ : ℂ)‖ := Complex.abs_re_le_norm _
          _ = r := hw
      linarith [(abs_le.mp hre).2]
    have hw_im : |w.im| ≤ 1 := by
      have him : |w.im| ≤ r := by
        calc
          |w.im| = |(w - (σ : ℂ)).im| := by simp
          _ ≤ ‖w - (σ : ℂ)‖ := Complex.abs_im_le_norm _
          _ = r := hw
      linarith
    have hLw := hnear hq hχ w hw_re_lo hw_re_hi hw_im
    rw [norm_smul, norm_div, norm_one, norm_pow, hw]
    exact mul_le_mul_of_nonneg_left hLw (by positivity)
  have hint_norm := circleIntegral.norm_integral_le_of_norm_le_const hr_pos.le hsphere
  rw [hcauchy, norm_smul, Complex.norm_mul, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one] at hint_norm
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcancel : (2 * Real.pi) * ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤
      (2 * Real.pi) * ((C₀ * Real.log (q + 2)) / r) := by
    calc
      (2 * Real.pi) * ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖
        ≤ 2 * Real.pi * r * ((1 / r ^ 2) * (C₀ * Real.log (q + 2))) := hint_norm
      _ = (2 * Real.pi) * ((C₀ * Real.log (q + 2)) / r) := by
          have hr_ne : r ≠ 0 := hr_pos.ne'
          field_simp [hr_ne]
  have hdiv : ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ (C₀ * Real.log (q + 2)) / r :=
    le_of_mul_le_mul_left hcancel hpi
  calc
    ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ (C₀ * Real.log (q + 2)) / r := hdiv
    _ = 4 * C₀ * (Real.log (q + 2)) ^ 2 := by
        dsimp only [r]
        have hne : Real.log (q + 2) ≠ 0 := by linarith
        field_simp [hne]

/-- On `1 < Re s ≤ 2`, the logarithmic derivative satisfies the universal bound
`‖logDeriv (LFunction χ) s‖ ≤ 1 / (Re s - 1) + C_zeta`. -/
theorem norm_logDeriv_LFunction_re_gt_one_le :
    ∃ C_zeta : ℝ, 0 < C_zeta ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      1 < s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 1 / (s.re - 1) + C_zeta := by
  obtain ⟨C_zeta, hC_zeta, hzeta_bd⟩ := neg_logDeriv_riemannZeta_real_le
  refine ⟨C_zeta, hC_zeta, fun {q} _ χ s hs1 hs2 ↦ ?_⟩
  have hL := neg_logDeriv_LFunction_eq_LSeries χ hs1
  have hZ := neg_logDeriv_riemannZeta_eq_LSeries (s := (s.re : ℂ)) (by simpa using hs1)
  have hnorm_eq : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ =
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ := by
    rw [logDeriv_apply, show -deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) by ring,
      norm_neg]
  have hnorm_le : ‖-deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
    rw [hL.2, hZ.2]
    have hre_eq : (LSeries (fun n ↦ (Λ n : ℂ)) (s.re : ℂ)).re =
        ∑' n : ℕ, (LSeries.term (fun n ↦ (Λ n : ℂ)) (s.re : ℂ) n).re := by
      simpa [LSeries] using Complex.reCLM.map_tsum hZ.1
    have hsum_re : Summable (fun n ↦ (LSeries.term (fun n ↦ (Λ n : ℂ)) (s.re : ℂ) n).re) :=
      Complex.reCLM.summable hZ.1
    rw [hre_eq]
    refine (norm_tsum_le_tsum_norm hL.1.norm).trans ?_
    refine hL.1.norm.tsum_le_tsum (fun n ↦ ?_) hsum_re
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hpow_norm : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn) s
    have hpow_re : (n : ℂ) ^ (-(s.re : ℂ)) = (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
    have hterm_chi : ‖LSeries.term (fun k ↦ χ k * (Λ k : ℂ)) s n‖ =
        ‖χ n‖ * (Λ n / (n : ℝ) ^ s.re) := by
      rw [LSeries.term_of_ne_zero hn, norm_div, hpow_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_div_assoc]
    have hterm_zeta : (LSeries.term (fun k ↦ (Λ k : ℂ)) (s.re : ℂ) n).re =
        Λ n / (n : ℝ) ^ s.re := by
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hpow_re,
        ← Complex.ofReal_mul, Complex.ofReal_re, Real.rpow_neg hn_pos.le, div_eq_mul_inv]
    rw [hterm_chi, hterm_zeta]
    exact mul_le_of_le_one_left (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (norm_char_le_one χ (n : ZMod q))
  rw [hnorm_eq]
  exact hnorm_le.trans (hzeta_bd s.re ⟨hs1, hs2⟩)

/-- Logarithmic-derivative upper bound inside the narrower zero-free region (away from any real
zero when `χ` is real): `‖logDeriv (LFunction χ) s‖ ≤ C * (log (q * (|Im s| + 2)))²`. -/
theorem norm_logDeriv_LFunction_zeroFreeRegion_le :
    ∃ c' > 0, ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ s : ℂ, (IsComplexChar χ ∨ 1 ≤ |s.im|) →
      1 - c' / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ C * (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 2 := by
  obtain ⟨c, hc_pos, hzfr⟩ := zeroFreeRegion
  obtain ⟨C_zeta, hC_zeta, hgt1_bd⟩ := norm_logDeriv_LFunction_re_gt_one_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c₁ : ℝ := min c (Real.log 2 / 4)
  have hc₁_pos : 0 < c₁ := lt_min hc_pos (by positivity)
  let c' : ℝ := c₁ / 16
  have hc'_pos : 0 < c' := by positivity
  let C_bc : ℝ := (60 / c₁) * (Real.log (5100 * (4 / c₁ + 1)) / Real.log 2 + 3)
  let C_right : ℝ := (4 / c₁) / Real.log 2 + C_zeta / (Real.log 2) ^ 2
  let C : ℝ := max 1 (max C_bc C_right)
  refine ⟨c', hc'_pos, C, by positivity, fun {q} _ χ hχ s hcond hs_lo hs_hi ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  let L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  by_cases hs_right : 1 + c₁ / (4 * L) ≤ s.re
  · have hbd := hgt1_bd χ s (by linarith [div_pos hc₁_pos (by positivity : 0 < 4 * L)]) hs_hi
    have hinv : 1 / (s.re - 1) ≤ (4 / c₁) * L := by
      have h4c : 0 < c₁ / (4 * L) := by positivity
      have hsub : c₁ / (4 * L) ≤ s.re - 1 := by linarith
      have hsre1 : 0 < s.re - 1 := by linarith
      rw [one_div_le hsre1 (by positivity)]
      calc
        1 / ((4 / c₁) * L) = c₁ / (4 * L) := by field_simp [hc₁_pos.ne', hL_pos.ne']
        _ ≤ s.re - 1 := hsub
    have hL_div : L ≤ (1 / Real.log 2) * L ^ 2 := by
      have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
      calc
        L = L * 1 := (mul_one L).symm
        _ ≤ L * (L / Real.log 2) := mul_le_mul_of_nonneg_left h1 hL_pos.le
        _ = (1 / Real.log 2) * L ^ 2 := by ring
    have hCz_bd : C_zeta ≤ (C_zeta / (Real.log 2) ^ 2) * L ^ 2 := by
      have h1 : (Real.log 2) ^ 2 ≤ L ^ 2 := sq_le_sq' (by linarith) hL_ge
      calc
        C_zeta = (C_zeta / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := by field_simp [hlog2.ne']
        _ ≤ (C_zeta / (Real.log 2) ^ 2) * L ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hC_ge : C_right ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    calc
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 1 / (s.re - 1) + C_zeta := hbd
      _ ≤ (4 / c₁) * L + C_zeta := by linarith
      _ ≤ (4 / c₁) * ((1 / Real.log 2) * L ^ 2) + (C_zeta / (Real.log 2) ^ 2) * L ^ 2 := by
          gcongr
      _ = C_right * L ^ 2 := by dsimp only [C_right]; ring
      _ ≤ C * L ^ 2 := mul_le_mul_of_nonneg_right hC_ge (sq_nonneg L)
  · push Not at hs_right
    let η : ℝ := c₁ / (4 * L)
    let z₀ : ℂ := ((1 + η : ℝ) : ℂ) + (s.im : ℂ) * I
    let R : ℝ := c₁ / (2 * L)
    let r : ℝ := c₁ / (3 * L)
    have hR_pos : 0 < R := by positivity
    have hr_pos : 0 < r := by positivity
    have hrR : r < R := by
      dsimp only [r, R]
      exact div_lt_div_of_pos_left hc₁_pos (by positivity) (by linarith)
    have hR_le_eighth : R ≤ 1 / 8 := by
      dsimp only [R]
      rw [div_le_iff₀ (by positivity)]
      have hc1_le : c₁ ≤ Real.log 2 / 4 := min_le_right _ _
      nlinarith
    have hs_mem : s ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub : s - z₀ = ((s.re - (1 + η) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [z₀]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      have h1 : 1 + η - s.re ≤ η + c' / L := by linarith
      dsimp only [η, c', r] at h1 ⊢
      have h2 : c₁ / (4 * L) + c₁ / 16 / L ≤ c₁ / (3 * L) := by
        have hpos : (0 : ℝ) < c₁ / L := by positivity
        calc
          c₁ / (4 * L) + c₁ / 16 / L = (5 / 16) * (c₁ / L) := by ring
          _ ≤ (1 / 3) * (c₁ / L) := mul_le_mul_of_nonneg_right (by norm_num) hpos.le
          _ = c₁ / (3 * L) := by ring
      linarith
    have hball_ne : ∀ w ∈ Metric.ball z₀ R, DirichletCharacter.LFunction χ w ≠ 0 := by
      intro w hw hzero
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hw_re_lo : 1 - c₁ / (4 * L) < w.re := by
        have hre : |w.re - z₀.re| < R := by
          calc
            |w.re - z₀.re| = |(w - z₀).re| := by simp
            _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
            _ < R := hw
        have hz₀_re : z₀.re = 1 + η := by simp [z₀]
        rw [hz₀_re] at hre
        dsimp only [η, R] at hre ⊢
        have h1 : 1 + c₁ / (4 * L) - c₁ / (2 * L) = 1 - c₁ / (4 * L) := by ring
        linarith [(abs_lt.mp hre).1]
      have hw_im_diff : |w.im - s.im| < R := by
        calc
          |w.im - s.im| = |(w - z₀).im| := by simp [z₀]
          _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
          _ < R := hw
      have hw_im_hi : |w.im| + 2 ≤ 2 * (|s.im| + 2) := by
        have h1 : |w.im| ≤ |s.im| + R := by
          have := (abs_lt.mp hw_im_diff).1
          have := (abs_lt.mp hw_im_diff).2
          rw [abs_le]
          constructor <;> linarith [neg_abs_le s.im, le_abs_self s.im]
        linarith [abs_nonneg s.im]
      have hw_L_le : Real.log ((q : ℝ) * (|w.im| + 2)) ≤ 2 * L := by
        have hpos_w : (0 : ℝ) < (q : ℝ) * (|w.im| + 2) := by positivity
        have hne_qt : (q : ℝ) * (|s.im| + 2) ≠ 0 := by positivity
        calc
          Real.log ((q : ℝ) * (|w.im| + 2)) ≤ Real.log (2 * ((q : ℝ) * (|s.im| + 2))) :=
            Real.log_le_log hpos_w (by nlinarith [abs_nonneg s.im])
          _ = Real.log 2 + L := Real.log_mul (by norm_num) hne_qt
          _ ≤ 2 * L := by linarith
      have hw_re_zfr : 1 - c / Real.log ((q : ℝ) * (|w.im| + 2)) ≤ w.re := by
        have hc1_le_c : c₁ ≤ c := min_le_left _ _
        have hw_L_pos : 0 < Real.log ((q : ℝ) * (|w.im| + 2)) :=
          Real.log_pos (by nlinarith [abs_nonneg w.im])
        have hfrac : c₁ / (4 * L) ≤ c / Real.log ((q : ℝ) * (|w.im| + 2)) := by
          rw [div_le_div_iff₀ (by positivity) hw_L_pos]
          calc
            c₁ * Real.log ((q : ℝ) * (|w.im| + 2)) ≤ c * (2 * L) :=
              mul_le_mul hc1_le_c hw_L_le hw_L_pos.le hc_pos.le
            _ ≤ c * (4 * L) := by nlinarith
        linarith
      have hres := hzfr χ w (Or.inl hχ) hw_re_zfr hzero
      rcases hcond with hcx | him1
      · exact (isComplexChar_iff_not_isReal χ).mp hcx hres.1
      · have hw_im_ne : w.im ≠ 0 := by
          intro hw0
          rw [hw0, zero_sub, abs_neg] at hw_im_diff
          linarith
        exact hw_im_ne hres.2.2.1
    let M : ℝ := 5100 * (4 / c₁ + 1) * ((q : ℝ) * (|s.im| + 2)) ^ 3
    have hball_bd : ∀ w ∈ Metric.ball z₀ R,
        ‖DirichletCharacter.LFunction χ w / DirichletCharacter.LFunction χ z₀‖ ≤ M := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hw_re_lo : 1 / 2 ≤ w.re := by
        have hre : |w.re - z₀.re| < R := by
          calc
            |w.re - z₀.re| = |(w - z₀).re| := by simp
            _ ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
            _ < R := hw
        have hz₀_re : z₀.re = 1 + η := by simp [z₀]
        linarith [(abs_lt.mp hre).1, show (0 : ℝ) < η by positivity]
      have hw_im_diff : |w.im - s.im| < R := by
        calc
          |w.im - s.im| = |(w - z₀).im| := by simp [z₀]
          _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
          _ < R := hw
      have hw_im_hi : |w.im| + 2 ≤ 2 * (|s.im| + 2) := by
        have h1 : |w.im| ≤ |s.im| + R := by
          have := (abs_lt.mp hw_im_diff).1
          have := (abs_lt.mp hw_im_diff).2
          rw [abs_le]
          constructor <;> linarith [neg_abs_le s.im, le_abs_self s.im]
        linarith [abs_nonneg s.im]
      have hLw : ‖DirichletCharacter.LFunction χ w‖ ≤ 204 * ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
        have hbd := norm_LFunction_re_ge_half_le hχ hw_re_lo
        have hq_poly : (q : ℝ) + 48 * (q : ℝ) ^ 2 + 2 ≤ 51 * (q : ℝ) ^ 2 := by nlinarith
        have him_sq : (|w.im| + 2) ^ 2 ≤ 4 * (|s.im| + 2) ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg w.im, abs_nonneg s.im]) hw_im_hi |>.trans_eq (by ring)
        calc
          ‖DirichletCharacter.LFunction χ w‖ ≤ (q + 48 * (q : ℝ) ^ 2 + 2) * (|w.im| + 2) ^ 2 := hbd
          _ ≤ (51 * (q : ℝ) ^ 2) * (4 * (|s.im| + 2) ^ 2) :=
            mul_le_mul hq_poly him_sq (sq_nonneg _) (by positivity)
          _ = 204 * ((q : ℝ) * (|s.im| + 2)) ^ 2 := by ring
      have hinv : ‖(DirichletCharacter.LFunction χ z₀)⁻¹‖ ≤ (4 / c₁ + 1) * ((q : ℝ) * (|s.im| + 2)) := by
        have hz₀_gt1 : 1 < z₀.re := by simp [z₀]; positivity
        have h1 := norm_inv_LFunction_le_one_add_inv χ hz₀_gt1
        have hz₀_sub : z₀.re - 1 = η := by simp [z₀]
        rw [hz₀_sub] at h1
        have hL_le_q : L ≤ (q : ℝ) * (|s.im| + 2) :=
          (Real.log_le_sub_one_of_pos (by nlinarith [abs_nonneg s.im])).trans (by
            nlinarith [abs_nonneg s.im])
        have h1_le_q : (1 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
        calc
          ‖(DirichletCharacter.LFunction χ z₀)⁻¹‖ ≤ 1 + 1 / η := h1
          _ = 1 + (4 / c₁) * L := by dsimp only [η]; rw [one_div_div]; ring
          _ ≤ (q : ℝ) * (|s.im| + 2) + (4 / c₁) * ((q : ℝ) * (|s.im| + 2)) := by gcongr
          _ = (4 / c₁ + 1) * ((q : ℝ) * (|s.im| + 2)) := by ring
      rw [div_eq_mul_inv, norm_mul]
      calc
        ‖DirichletCharacter.LFunction χ w‖ * ‖(DirichletCharacter.LFunction χ z₀)⁻¹‖
          ≤ (204 * ((q : ℝ) * (|s.im| + 2)) ^ 2) * ((4 / c₁ + 1) * ((q : ℝ) * (|s.im| + 2))) :=
            mul_le_mul hLw hinv (norm_nonneg _) (by positivity)
        _ = 204 * (4 / c₁ + 1) * ((q : ℝ) * (|s.im| + 2)) ^ 3 := by ring
        _ ≤ M := by
            dsimp only [M]
            have : (0 : ℝ) ≤ (4 / c₁ + 1) * ((q : ℝ) * (|s.im| + 2)) ^ 3 := by positivity
            nlinarith
    have hbc :=
      AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.landau_logDeriv_le_of_ne_zero
        hr_pos.le hrR (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
        hball_ne hball_bd hs_mem
    have hcoeff : 2 * (R + r) / (R - r) ^ 2 = (60 / c₁) * L := by
      dsimp only [R, r]
      have hc1_ne : c₁ ≠ 0 := hc₁_pos.ne'
      have hL_ne : L ≠ 0 := hL_pos.ne'
      field_simp [hc1_ne, hL_ne]
      ring
    have hlogM : Real.log M ≤ (Real.log (5100 * (4 / c₁ + 1)) / Real.log 2 + 3) * L := by
      dsimp only [M]
      have hqt_pos : (0 : ℝ) < (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
      rw [Real.log_mul (by positivity) (pow_ne_zero 3 hqt_pos.ne'), Real.log_pow]
      push_cast
      have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
      have hc_pos : 0 < Real.log (5100 * (4 / c₁ + 1)) := by
        apply Real.log_pos
        have : 0 < 4 / c₁ := by positivity
        linarith
      calc
        Real.log (5100 * (4 / c₁ + 1)) + 3 * L
          ≤ Real.log (5100 * (4 / c₁ + 1)) * (L / Real.log 2) + 3 * L := by nlinarith
        _ = (Real.log (5100 * (4 / c₁ + 1)) / Real.log 2 + 3) * L := by ring
    have hC_ge : C_bc ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    calc
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ 2 * (R + r) / (R - r) ^ 2 * Real.log M := hbc
      _ = (60 / c₁) * L * Real.log M := by rw [hcoeff]
      _ ≤ (60 / c₁) * L * ((Real.log (5100 * (4 / c₁ + 1)) / Real.log 2 + 3) * L) :=
          mul_le_mul_of_nonneg_left hlogM (by positivity)
      _ = C_bc * L ^ 2 := by dsimp only [C_bc]; ring
      _ ≤ C * L ^ 2 := mul_le_mul_of_nonneg_right hC_ge (sq_nonneg L)

end ClassicalZeroFreeRegion

section LandauTheorem

private lemma changeLevel_isReal {d q : ℕ} (hd : d ∣ q) {χ : DirichletCharacter ℂ d}
    (hreal : IsReal χ) : IsReal (DirichletCharacter.changeLevel hd χ) := by
  rw [isReal_iff_sq_eq_one] at hreal ⊢
  rw [← map_pow, hreal, map_one]

private lemma changeLevel_ne_one_of_distinct_primitive {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive)
    (hr₁ : IsReal χ₁) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1)
    (hneq : (⟨q₁, χ₁⟩ : Σ q : ℕ, DirichletCharacter ℂ q) ≠ ⟨q₂, χ₂⟩) :
    let ψ₁ : DirichletCharacter ℂ (q₁ * q₂) := DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁
    let ψ₂ : DirichletCharacter ℂ (q₁ * q₂) := DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂
    ψ₁ ≠ 1 ∧ ψ₂ ≠ 1 ∧ ψ₁ * ψ₂ ≠ 1 := by
  have : NeZero (q₁ * q₂) := inferInstance
  intro ψ₁ ψ₂
  have hψ₁ : ψ₁ ≠ 1 := by
    intro h
    have hc := conductor_changeLevel_of_isPrimitive (dvd_mul_right q₁ q₂) hp₁
    change ψ₁.conductor = q₁ at hc
    rw [h, DirichletCharacter.conductor_one] at hc
    have hq₁ : q₁ = 1 := hc.symm
    subst hq₁
    exact h₁ (DirichletCharacter.level_one χ₁)
  have hψ₂ : ψ₂ ≠ 1 := by
    intro h
    have hc := conductor_changeLevel_of_isPrimitive (dvd_mul_left q₂ q₁) hp₂
    change ψ₂.conductor = q₂ at hc
    rw [h, DirichletCharacter.conductor_one] at hc
    have hq₂ : q₂ = 1 := hc.symm
    subst hq₂
    exact h₂ (DirichletCharacter.level_one χ₂)
  refine ⟨hψ₁, hψ₂, fun hprod ↦ ?_⟩
  have hψ₁_sq : ψ₁ * ψ₁ = 1 := by
    have hsq := (isReal_iff_sq_eq_one ψ₁).mp (changeLevel_isReal (dvd_mul_right q₁ q₂) hr₁)
    rwa [← sq]
  have hψ_eq : ψ₁ = ψ₂ := by
    calc
      ψ₁ = ψ₁ * 1 := (mul_one ψ₁).symm
      _ = ψ₁ * (ψ₁ * ψ₂) := by rw [hprod]
      _ = (ψ₁ * ψ₁) * ψ₂ := by rw [mul_assoc]
      _ = 1 * ψ₂ := by rw [hψ₁_sq]
      _ = ψ₂ := one_mul ψ₂
  have hq_eq : q₁ = q₂ := by
    have hc₁ := conductor_changeLevel_of_isPrimitive (dvd_mul_right q₁ q₂) hp₁
    have hc₂ := conductor_changeLevel_of_isPrimitive (dvd_mul_left q₂ q₁) hp₂
    change ψ₁.conductor = q₁ at hc₁
    change ψ₂.conductor = q₂ at hc₂
    rw [← hc₁, hψ_eq, hc₂]
  subst hq_eq
  have hχ_eq : χ₁ = χ₂ :=
    DirichletCharacter.changeLevel_injective (dvd_mul_right q₁ q₁) hψ_eq
  exact hneq (congrArg (Sigma.mk q₁) hχ_eq)

private lemma four_char_term_nonneg {q : ℕ} [NeZero q] {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) {σ : ℝ} (_hσ : 1 < σ) (n : ℕ) :
    0 ≤ (LSeries.term (fun k ↦ (Λ k : ℂ)) (σ : ℂ) n).re +
        (LSeries.term (fun k ↦ ψ₁ k * (Λ k : ℂ)) (σ : ℂ) n).re +
        (LSeries.term (fun k ↦ ψ₂ k * (Λ k : ℂ)) (σ : ℂ) n).re +
        (LSeries.term (fun k ↦ (ψ₁ * ψ₂) k * (Λ k : ℂ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpow_re : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
  have hterm : ∀ ψ : DirichletCharacter ℂ q,
      (LSeries.term (fun k ↦ ψ k * (Λ k : ℂ)) (σ : ℂ) n).re =
        Λ n * (n : ℝ) ^ (-σ) * (ψ n).re := by
    intro ψ
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hpow_re]
    have heq : ψ n * (Λ n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) =
        (((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)) * ψ n := by push_cast; ring
    rw [heq, Complex.re_ofReal_mul]
  have hterm_z : (LSeries.term (fun k ↦ (Λ k : ℂ)) (σ : ℂ) n).re = Λ n * (n : ℝ) ^ (-σ) := by
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, hpow_re,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hterm_z, hterm ψ₁, hterm ψ₂, hterm (ψ₁ * ψ₂)]
  have him₁ : (ψ₁ n).im = 0 := hr₁ (n : ZMod q)
  have him₂ : (ψ₂ n).im = 0 := hr₂ (n : ZMod q)
  have hprod_re : ((ψ₁ * ψ₂) n).re = (ψ₁ n).re * (ψ₂ n).re := by
    change (ψ₁ (n : ZMod q) * ψ₂ (n : ZMod q)).re = _
    rw [Complex.mul_re, him₁, him₂, mul_zero, sub_zero]
  have hfactor : Λ n * (n : ℝ) ^ (-σ) + Λ n * (n : ℝ) ^ (-σ) * (ψ₁ n).re +
      Λ n * (n : ℝ) ^ (-σ) * (ψ₂ n).re + Λ n * (n : ℝ) ^ (-σ) * ((ψ₁ * ψ₂) n).re =
      (Λ n * (n : ℝ) ^ (-σ)) * ((1 + (ψ₁ n).re) * (1 + (ψ₂ n).re)) := by
    rw [hprod_re]; ring
  rw [hfactor]
  have h1 : 0 ≤ 1 + (ψ₁ n).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm (ψ₁ n)).trans (norm_char_le_one ψ₁ (n : ZMod q)))).1
    linarith
  have h2 : 0 ≤ 1 + (ψ₂ n).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm (ψ₂ n)).trans (norm_char_le_one ψ₂ (n : ZMod q)))).1
    linarith
  exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hn_pos.le _))
    (mul_nonneg h1 h2)

private lemma four_char_neg_logDeriv_nonneg {q : ℕ} [NeZero q]
    {ψ₁ ψ₂ : DirichletCharacter ℂ q} (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂)
    {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
        (-deriv (DirichletCharacter.LFunction ψ₁) (σ : ℂ) /
          DirichletCharacter.LFunction ψ₁ (σ : ℂ)).re +
        (-deriv (DirichletCharacter.LFunction ψ₂) (σ : ℂ) /
          DirichletCharacter.LFunction ψ₂ (σ : ℂ)).re +
        (-deriv (DirichletCharacter.LFunction (ψ₁ * ψ₂)) (σ : ℂ) /
          DirichletCharacter.LFunction (ψ₁ * ψ₂) (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  obtain ⟨hz_s, hz_eq⟩ := neg_logDeriv_riemannZeta_eq_LSeries hs
  obtain ⟨h1_s, h1_eq⟩ := neg_logDeriv_LFunction_eq_LSeries ψ₁ hs
  obtain ⟨h2_s, h2_eq⟩ := neg_logDeriv_LFunction_eq_LSeries ψ₂ hs
  obtain ⟨h12_s, h12_eq⟩ := neg_logDeriv_LFunction_eq_LSeries (ψ₁ * ψ₂) hs
  rw [hz_eq, h1_eq, h2_eq, h12_eq, LSeries, LSeries, LSeries, LSeries]
  have hz_re := (Complex.reCLM.hasSum hz_s.hasSum).tsum_eq.symm
  have h1_re := (Complex.reCLM.hasSum h1_s.hasSum).tsum_eq.symm
  have h2_re := (Complex.reCLM.hasSum h2_s.hasSum).tsum_eq.symm
  have h12_re := (Complex.reCLM.hasSum h12_s.hasSum).tsum_eq.symm
  simp only [Complex.reCLM_apply] at hz_re h1_re h2_re h12_re
  rw [hz_re, h1_re, h2_re, h12_re]
  have hz_sr : Summable fun n ↦ (LSeries.term (fun k ↦ (Λ k : ℂ)) (σ : ℂ) n).re :=
    (Complex.reCLM.hasSum hz_s.hasSum).summable
  have h1_sr : Summable fun n ↦ (LSeries.term (fun k ↦ ψ₁ k * (Λ k : ℂ)) (σ : ℂ) n).re :=
    (Complex.reCLM.hasSum h1_s.hasSum).summable
  have h2_sr : Summable fun n ↦ (LSeries.term (fun k ↦ ψ₂ k * (Λ k : ℂ)) (σ : ℂ) n).re :=
    (Complex.reCLM.hasSum h2_s.hasSum).summable
  have h12_sr : Summable fun n ↦ (LSeries.term (fun k ↦ (ψ₁ * ψ₂) k * (Λ k : ℂ)) (σ : ℂ) n).re :=
    (Complex.reCLM.hasSum h12_s.hasSum).summable
  rw [← hz_sr.tsum_add h1_sr, ← (hz_sr.add h1_sr).tsum_add h2_sr,
    ← ((hz_sr.add h1_sr).add h2_sr).tsum_add h12_sr]
  exact tsum_nonneg fun n ↦ four_char_term_nonneg hr₁ hr₂ hσ n

/-- **Landau's two-character repulsion theorem**: there exists a universal constant `c_L > 0`
such that for any two distinct primitive real non-principal Dirichlet characters `χ₁` mod `q₁`
and `χ₂` mod `q₂`, if `L(β₁, χ₁) = 0` and `L(β₂, χ₂) = 0` with `0 < β₁, β₂`, then
`min β₁ β₂ < 1 - c_L / Real.log (q₁ * q₂ + 2)`. Equivalently, at most one primitive real
character has a real zero exceeding `1 - c_L / Real.log (q₁ * q₂ + 2)`. -/
theorem landau_two_characters :
    ∃ c_L : ℝ, 0 < c_L ∧ ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
      {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂},
      χ₁.IsPrimitive → χ₂.IsPrimitive →
      IsReal χ₁ → IsReal χ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      (⟨q₁, χ₁⟩ : Σ q : ℕ, DirichletCharacter ℂ q) ≠ ⟨q₂, χ₂⟩ →
      ∀ {β₁ β₂ : ℝ}, 0 < β₁ → 0 < β₂ →
        DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
        DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
        min β₁ β₂ < 1 - c_L / Real.log ((q₁ : ℝ) * q₂ + 2) := by
  obtain ⟨C_zeta, hC_zeta, hzeta_bd⟩ := neg_logDeriv_riemannZeta_real_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K_const : ℝ := C_zeta / Real.log 2 + 120
  obtain ⟨δ, hδ_pos, hδ_le_a, hδ_K, hδ_log⟩ :=
    exists_small_delta (Real.log 2 / 8) 408 K_const (1 / 192 * Real.log 2)
      (by positivity) (by norm_num) (by positivity) (by positivity)
  let c_L : ℝ := δ / 32
  refine ⟨c_L, by positivity, fun {q₁ q₂} _ _ {χ₁ χ₂} hp₁ hp₂ hr₁ hr₂ h₁ h₂ hneq
      {β₁ β₂} _ _ hz₁ hz₂ ↦ ?_⟩
  by_contra hcontr
  push Not at hcontr
  have hβ₁_ge : 1 - c_L / Real.log ((q₁ : ℝ) * q₂ + 2) ≤ β₁ :=
    le_trans hcontr (min_le_left _ _)
  have hβ₂_ge : 1 - c_L / Real.log ((q₁ : ℝ) * q₂ + 2) ≤ β₂ :=
    le_trans hcontr (min_le_right _ _)
  have hβ₁_lt : β₁ < 1 := by
    by_contra hle
    push Not at hle
    exact LFunction_ne_zero_on_re_one χ₁ (by simpa using hle) (Or.inl h₁) hz₁
  have hβ₂_lt : β₂ < 1 := by
    by_contra hle
    push Not at hle
    exact LFunction_ne_zero_on_re_one χ₂ (by simpa using hle) (Or.inl h₂) hz₂
  let q : ℕ := q₁ * q₂
  have : NeZero q := inferInstance
  let ψ₁ : DirichletCharacter ℂ q := DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁
  let ψ₂ : DirichletCharacter ℂ q := DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂
  obtain ⟨hψ₁, hψ₂, hψ₁₂⟩ := changeLevel_ne_one_of_distinct_primitive hp₁ hp₂ hr₁ h₁ h₂ hneq
  have hrψ₁ : IsReal ψ₁ := changeLevel_isReal (dvd_mul_right q₁ q₂) hr₁
  have hrψ₂ : IsReal ψ₂ := changeLevel_isReal (dvd_mul_left q₂ q₁) hr₂
  have hψ₁_zero : DirichletCharacter.LFunction ψ₁ (β₁ : ℂ) = 0 := by
    dsimp only [ψ₁]
    rw [LFunction_changeLevel_eq (dvd_mul_right q₁ q₂) χ₁ (Or.inl h₁), hz₁, zero_mul]
  have hψ₂_zero : DirichletCharacter.LFunction ψ₂ (β₂ : ℂ) = 0 := by
    dsimp only [ψ₂]
    rw [LFunction_changeLevel_eq (dvd_mul_left q₂ q₁) χ₂ (Or.inl h₂), hz₂, zero_mul]
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast NeZero.pos q₁
  have hq₂ : (1 : ℝ) ≤ q₂ := by exact_mod_cast NeZero.pos q₂
  have hq : (1 : ℝ) ≤ q := by
    dsimp only [q]
    push_cast
    nlinarith
  let L : ℝ := Real.log ((q₁ : ℝ) * q₂ + 2)
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2 hL_ge
  let η : ℝ := δ / L
  have hη_pos : 0 < η := div_pos hδ_pos hL_pos
  have hη_le : η ≤ 1 / 8 := by
    rw [div_le_iff₀ hL_pos]
    nlinarith
  let σ₀ : ℝ := 1 + η
  have hσ₀_gt1 : 1 < σ₀ := by linarith
  have hσ₀_le2 : σ₀ ≤ 2 := by linarith
  have hfour := four_char_neg_logDeriv_nonneg hrψ₁ hrψ₂ hσ₀_gt1
  have hterm_z : (-deriv riemannZeta (σ₀ : ℂ) / riemannZeta (σ₀ : ℂ)).re ≤ 1 / η + C_zeta := by
    simpa [σ₀] using hzeta_bd σ₀ ⟨hσ₀_gt1, hσ₀_le2⟩
  have hq2_le : Real.log (2 * (q : ℝ)) ≤ 2 * L := by
    have hmul_le : 2 * (q : ℝ) ≤ ((q₁ : ℝ) * q₂ + 2) ^ 2 := by
      have : (q : ℝ) = (q₁ : ℝ) * q₂ := by dsimp only [q]; push_cast; ring
      rw [this]
      nlinarith
    calc
      Real.log (2 * (q : ℝ)) ≤ Real.log (((q₁ : ℝ) * q₂ + 2) ^ 2) :=
        Real.log_le_log (by positivity) hmul_le
      _ = 2 * L := by
          rw [Real.log_pow]
          push_cast
          ring
  have hlog408_le : Real.log (408 / η) ≤ Real.log (408 / δ) + L := by
    have hL_le : L ≤ (q₁ : ℝ) * q₂ + 2 :=
      (Real.log_le_sub_one_of_pos (by nlinarith)).trans (by linarith)
    have h1 : 408 / η ≤ (408 / δ) * ((q₁ : ℝ) * q₂ + 2) := by
      calc
        408 / η = (408 / δ) * L := by dsimp only [η]; rw [div_div_eq_mul_div, div_mul_eq_mul_div]
        _ ≤ (408 / δ) * ((q₁ : ℝ) * q₂ + 2) := mul_le_mul_of_nonneg_left hL_le (by positivity)
    calc
      Real.log (408 / η) ≤ Real.log ((408 / δ) * ((q₁ : ℝ) * q₂ + 2)) :=
        Real.log_le_log (by positivity) h1
      _ = Real.log (408 / δ) + L := Real.log_mul (by positivity) (by nlinarith)
  have hmk_mem : ∀ β : ℝ, 1 - c_L / L ≤ β → β < 1 →
      (β : ℂ) ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ) ∧
        (32 / 33) / η ≤ ((((1 + η : ℝ) : ℂ) - (β : ℂ))⁻¹).re := by
    intro β hβ_ge hβ_lt
    have hsub_hi : 1 + η - β ≤ (33 / 32) * η := by
      dsimp only [c_L, η] at hβ_ge ⊢
      rw [div_right_comm] at hβ_ge
      linarith
    have hmem : (β : ℂ) ∈ Metric.closedBall ((1 + η : ℝ) : ℂ) (1 / 4 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, show (β : ℂ) - ((1 + η : ℝ) : ℂ) =
        ((β - (1 + η) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith)]
      linarith
    have hinv_ge : (32 / 33) / η ≤ ((((1 + η : ℝ) : ℂ) - (β : ℂ))⁻¹).re := by
      rw [show ((1 + η : ℝ) : ℂ) - (β : ℂ) = ((1 + η - β : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_inv, Complex.ofReal_re]
      calc
        (32 / 33) / η = ((33 / 32) * η)⁻¹ := by field_simp [hη_pos.ne']
        _ ≤ (1 + η - β)⁻¹ := inv_anti₀ (by linarith) hsub_hi
    exact ⟨hmem, hinv_ge⟩
  obtain ⟨hmem₁, hge₁⟩ := hmk_mem β₁ hβ₁_ge hβ₁_lt
  obtain ⟨hmem₂, hge₂⟩ := hmk_mem β₂ hβ₂_ge hβ₂_lt
  have hL1 := landau_LFunction_center_sub_zero_le hψ₁ hη_pos (by linarith) 0 (by simpa using hmem₁) hψ₁_zero
  have hL2 := landau_LFunction_center_sub_zero_le hψ₂ hη_pos (by linarith) 0 (by simpa using hmem₂) hψ₂_zero
  have hL12 := landau_LFunction_center_le hψ₁₂ hη_pos (by linarith) 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hL1 hL2 hL12
  have hld_eq : ∀ ψ : DirichletCharacter ℂ q,
      (-deriv (DirichletCharacter.LFunction ψ) (σ₀ : ℂ) /
        DirichletCharacter.LFunction ψ (σ₀ : ℂ)).re =
        -(logDeriv (DirichletCharacter.LFunction ψ) ((1 + η : ℝ) : ℂ)).re := by
    intro ψ
    rw [show -deriv (DirichletCharacter.LFunction ψ) (σ₀ : ℂ) /
        DirichletCharacter.LFunction ψ (σ₀ : ℂ) =
      -logDeriv (DirichletCharacter.LFunction ψ) ((1 + η : ℝ) : ℂ) by
        rw [logDeriv_apply, neg_div]]
    rfl
  rw [hld_eq ψ₁, hld_eq ψ₂, hld_eq (ψ₁ * ψ₂)] at hfour
  have hq2_le' : Real.log ((q : ℝ) * 2) ≤ 2 * L := by rw [mul_comm]; exact hq2_le
  have hcomb : (32 / 33) / η + (32 / 33) / η ≤
      1 / η + C_zeta + 24 * Real.log (408 / δ) + 120 * L := by
    linarith [hfour, hterm_z, hL1, hL2, hL12, hge₁, hge₂, hq2_le', hlog408_le]
  have hη_inv : L / δ = 1 / η := by dsimp only [η]; rw [one_div_div]
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have h_p1 : C_zeta + 120 * L ≤ K_const * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hlog2).2 hL_ge
    have hmul : C_zeta ≤ (C_zeta / Real.log 2) * L := by
      calc
        C_zeta = C_zeta * 1 := (mul_one _).symm
        _ ≤ C_zeta * (L / Real.log 2) := mul_le_mul_of_nonneg_left h1 hC_zeta.le
        _ = (C_zeta / Real.log 2) * L := by ring
    dsimp only [K_const]
    linarith
  have h_p1_mul : K_const * L ≤ (1 / 8) / η := by
    calc
      K_const * L = (δ * K_const) * (L / δ) := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 192 * Real.log 2) * (1 / η) := by
          rw [hη_inv]
          exact mul_le_mul_of_nonneg_right hδ_K (by positivity)
      _ ≤ (1 / 8) * (1 / η) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1 / 8) / η := by ring
  have h_p2_mul : 24 * Real.log (408 / δ) ≤ (1 / 8) / η := by
    have hmul : 24 * (δ * Real.log (408 / δ)) ≤ 1 / 8 * L := by
      calc
        24 * (δ * Real.log (408 / δ)) ≤ 24 * (1 / 192 * Real.log 2) :=
            mul_le_mul_of_nonneg_left hδ_log (by norm_num)
        _ = 1 / 8 * Real.log 2 := by ring
        _ ≤ 1 / 8 * L := mul_le_mul_of_nonneg_left hL_ge (by norm_num)
    have hdiv := div_le_div_of_nonneg_right hmul hδ_pos.le
    calc
      24 * Real.log (408 / δ) = (24 * (δ * Real.log (408 / δ))) / δ := by field_simp [hδ_pos.ne']
      _ ≤ (1 / 8 * L) / δ := hdiv
      _ = 1 / 8 * (L / δ) := by ring
      _ = (1 / 8) / η := by rw [hη_inv]; ring
  have hcontra : (64 / 33 : ℝ) / η ≤ (5 / 4) / η := by
    have h1 : (32 / 33) / η + (32 / 33) / η = (64 / 33) / η := by ring
    have h2 : 1 / η + (1 / 8) / η + (1 / 8) / η = (5 / 4) / η := by ring
    linarith
  have hfinal : (64 / 33 : ℝ) ≤ 5 / 4 := by
    have := mul_le_mul_of_nonneg_right hcontra hη_pos.le
    field_simp [hη_pos.ne'] at this
    linarith
  norm_num at hfinal

end LandauTheorem

section EstermannEngine

private lemma riemannZeta_bound_sphere_two :
    ∃ C_ζ : ℝ, 0 < C_ζ ∧ ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ), ‖riemannZeta z‖ ≤ C_ζ := by
  have hcomp : IsCompact (Metric.closedBall (2 : ℂ) (3 / 2 : ℝ)) :=
    isCompact_closedBall (2 : ℂ) (3 / 2 : ℝ)
  have hne : (Metric.closedBall (2 : ℂ) (3 / 2 : ℝ)).Nonempty :=
    ⟨2, Metric.mem_closedBall_self (by norm_num)⟩
  obtain ⟨z₀, _, hz₀_max⟩ :=
    hcomp.exists_isMaxOn hne differentiable_zetaOne.continuous.norm.continuousOn
  let C_ζ : ℝ := 2 * (‖zetaOne z₀‖ + 1)
  refine ⟨C_ζ, by positivity, fun z hz ↦ ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have hz_sub_ge : 1 / 2 ≤ ‖z - 1‖ := by
    have hrev := norm_sub_norm_le (z - 2) (-1 : ℂ)
    rw [show (z - 2) - (-1 : ℂ) = z - 1 by ring, norm_neg, norm_one, hz] at hrev
    linarith
  have hz_ne1 : z ≠ 1 := fun h ↦ by
    subst h
    norm_num at hz_sub_ge
  have hz_mem : z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hz]
  have hzeta_one_le : ‖zetaOne z‖ ≤ ‖zetaOne z₀‖ := hz₀_max hz_mem
  have heq : ‖riemannZeta z‖ = ‖zetaOne z‖ / ‖z - 1‖ := by
    rw [zetaOne_eq_sub_one_mul hz_ne1, norm_mul]
    have hnz : ‖z - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz_ne1)
    field_simp [hnz]
  rw [heq]
  calc
    ‖zetaOne z‖ / ‖z - 1‖ ≤ ‖zetaOne z₀‖ / (1 / 2) :=
      div_le_div₀ (norm_nonneg _) hzeta_one_le (by norm_num) hz_sub_ge
    _ = 2 * ‖zetaOne z₀‖ := by ring
    _ ≤ C_ζ := by dsimp only [C_ζ]; linarith

private lemma iteratedDeriv_inv_sub_one (k : ℕ) :
    Set.EqOn (iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹))
      (fun w : ℂ ↦ (-1 : ℂ) ^ k * (k ! : ℂ) * (w - 1)⁻¹ ^ (k + 1)) {w : ℂ | w ≠ 1} := by
  induction k with
  | zero =>
      intro w _
      simp
  | succ k ih =>
      intro w hw
      have hopen : IsOpen ({z : ℂ | z ≠ 1}) := isOpen_compl_singleton
      have hev : iteratedDeriv k (fun w : ℂ ↦ (w - 1)⁻¹) =ᶠ[𝓝 w]
          fun z : ℂ ↦ (-1 : ℂ) ^ k * (k ! : ℂ) * (z - 1)⁻¹ ^ (k + 1) := by
        filter_upwards [hopen.mem_nhds hw] with z hz
        exact ih hz
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have h1 : HasDerivAt (fun z : ℂ ↦ (z - 1)⁻¹) (-((w - 1)⁻¹ ^ 2)) w := by
        have hlin : HasDerivAt (fun z : ℂ ↦ z - 1) 1 w := (hasDerivAt_id w).sub_const 1
        have hne : w - 1 ≠ 0 := sub_ne_zero.mpr hw
        convert hlin.inv hne using 1
        field_simp [hne]
      have h2 : HasDerivAt (fun z : ℂ ↦ (z - 1)⁻¹ ^ (k + 1))
          (((k + 1 : ℕ) : ℂ) * (w - 1)⁻¹ ^ k * (-((w - 1)⁻¹ ^ 2))) w := by
        convert h1.pow (k + 1) using 1
        simp
      have h3 : HasDerivAt (fun z : ℂ ↦ (-1 : ℂ) ^ k * (k ! : ℂ) * (z - 1)⁻¹ ^ (k + 1))
          ((-1 : ℂ) ^ k * (k ! : ℂ) * (((k + 1 : ℕ) : ℂ) * (w - 1)⁻¹ ^ k * (-((w - 1)⁻¹ ^ 2)))) w :=
        h2.const_mul _
      rw [h3.deriv, pow_succ, Nat.factorial_succ]
      push_cast
      ring

private lemma differentiable_dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (isOpen_univ.mem_nhds (Set.mem_univ c))).mpr hf.differentiableOn

private lemma logMul_iterate_nonneg_real {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, 0 ≤ (a n).re ∧ (a n).im = 0) :
    ∀ k n : ℕ, 1 ≤ n →
      0 ≤ (((LSeries.logMul^[k] a) n)).re ∧ (((LSeries.logMul^[k] a) n)).im = 0 := by
  intro k
  induction k with
  | zero =>
      intro n _
      exact ha n
  | succ k ih =>
      intro n hn
      rw [Function.iterate_succ_apply']
      dsimp only [LSeries.logMul]
      have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity)]
      have hre : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      obtain ⟨ih_re, ih_im⟩ := ih n hn
      rw [hlog, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ih_im]
      exact ⟨by simp only [mul_zero, sub_zero]; exact mul_nonneg hre ih_re, by ring⟩

private lemma lseries_logMul_iterate_nonneg_real {a : ℕ → ℂ}
    (ha : ∀ n : ℕ, 0 ≤ (a n).re ∧ (a n).im = 0)
    (ha_abs : LSeries.abscissaOfAbsConv a ≤ 1) (k : ℕ) :
    0 ≤ (LSeries (LSeries.logMul^[k] a) 2).re ∧ (LSeries (LSeries.logMul^[k] a) 2).im = 0 := by
  have hab : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] a) < (2 : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt ha_abs (by simp only [Complex.re_ofNat]; exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have hsum : LSeriesSummable (LSeries.logMul^[k] a) 2 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re hab
  have hre_term : ∀ n : ℕ, 0 ≤ (LSeries.term (LSeries.logMul^[k] a) 2 n).re ∧
      (LSeries.term (LSeries.logMul^[k] a) 2 n).im = 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    obtain ⟨hre, him⟩ := logMul_iterate_nonneg_real ha k n (Nat.pos_of_ne_zero hn)
    have hpow : (n : ℂ) ^ (2 : ℂ) = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [LSeries.term_of_ne_zero hn, hpow, div_eq_mul_inv, ← Complex.ofReal_inv,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him]
    exact ⟨by simp only [mul_zero, sub_zero]; exact mul_nonneg hre (inv_nonneg.mpr (sq_nonneg _)), by ring⟩
  have hts_re := (Complex.reCLM.hasSum hsum.hasSum).tsum_eq
  have hts_im := (Complex.imCLM.hasSum hsum.hasSum).tsum_eq
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hts_re hts_im
  rw [LSeries, ← hts_re, ← hts_im]
  have hzero : ∀ n, (LSeries.term (LSeries.logMul^[k] a) 2 n).im = 0 :=
    fun n ↦ (hre_term n).2
  exact ⟨tsum_nonneg fun n ↦ (hre_term n).1, by simp_rw [hzero]; exact tsum_zero⟩

private noncomputable def estermannG (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F 1 * dslope zetaOne 1 z + zetaOne z * dslope F 1 z

private lemma estermannG_differentiable {F : ℂ → ℂ} (hF_diff : Differentiable ℂ F) :
    Differentiable ℂ (estermannG F) :=
  ((differentiable_dslope_entire differentiable_zetaOne 1).const_mul (F 1)).add
    (differentiable_zetaOne.mul (differentiable_dslope_entire hF_diff 1))

private lemma estermannG_eq (F : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) :
    estermannG F z = riemannZeta z * F z - F 1 / (z - 1) := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  dsimp only [estermannG]
  rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_module, slope_def_module,
    zetaOne_one, zetaOne_eq_sub_one_mul hz, smul_eq_mul, smul_eq_mul]
  field_simp [hz1]
  ring

private lemma estermannG_coeff_bound {C_ζ B : ℝ} (hC_ζ : 0 < C_ζ) (hB : 0 ≤ B)
    (hzeta_sphere : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ), ‖riemannZeta z‖ ≤ C_ζ)
    {F : ℂ → ℂ} (hF_diff : Differentiable ℂ F)
    (hF_ball : ∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ), ‖F z‖ ≤ B) (k : ℕ) :
    ‖(k ! : ℂ)⁻¹ * iteratedDeriv k (estermannG F) 2‖ ≤ (C_ζ + 2) * B * (2 / 3 : ℝ) ^ k := by
  have h1_ball : (1 : ℂ) ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    norm_num
  have hF1_le : ‖F 1‖ ≤ B := hF_ball 1 h1_ball
  have hG_sphere : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ),
      ‖estermannG F z‖ ≤ (C_ζ + 2) * B := by
    intro z hz
    have hz_norm : ‖z - 2‖ = 3 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz_sub_ge : 1 / 2 ≤ ‖z - 1‖ := by
      have hrev := norm_sub_norm_le (z - 2) (-1 : ℂ)
      rw [show (z - 2) - (-1 : ℂ) = z - 1 by ring, norm_neg, norm_one, hz_norm] at hrev
      linarith
    have hz_ne1 : z ≠ 1 := fun h ↦ by subst h; norm_num at hz_sub_ge
    have hz_ball : z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ) := Metric.sphere_subset_closedBall hz
    rw [estermannG_eq F hz_ne1]
    have h1 := hzeta_sphere z hz
    have h2 := hF_ball z hz_ball
    have hinv : ‖(z - 1)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
      exact (inv_anti₀ (by norm_num) hz_sub_ge).trans_eq this
    calc
      ‖riemannZeta z * F z - F 1 / (z - 1)‖
        ≤ ‖riemannZeta z * F z‖ + ‖F 1 / (z - 1)‖ := norm_sub_le _ _
      _ = ‖riemannZeta z‖ * ‖F z‖ + ‖F 1‖ * ‖(z - 1)⁻¹‖ := by
          rw [norm_mul, div_eq_mul_inv, norm_mul]
      _ ≤ C_ζ * B + B * 2 := add_le_add (mul_le_mul h1 h2 (norm_nonneg _) hC_ζ.le)
          (mul_le_mul hF1_le hinv (norm_nonneg _) hB)
      _ = (C_ζ + 2) * B := by ring
  have hcauchy := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (c := (2 : ℂ)) (by norm_num : (0 : ℝ) < 3 / 2) k
    (((estermannG_differentiable hF_diff).differentiableOn) :
      DifferentiableOn ℂ (estermannG F) (Metric.closedBall (2 : ℂ) (3 / 2 : ℝ)))
  have hint_bd : ‖∮ z in C((2 : ℂ), (3 / 2 : ℝ)), (1 / (z - 2) ^ (k + 1)) • estermannG F z‖ ≤
      2 * Real.pi * (3 / 2 : ℝ) * (((C_ζ + 2) * B) / (3 / 2 : ℝ) ^ (k + 1)) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) fun z hz ↦ ?_
    have hzn : ‖z - 2‖ = 3 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [norm_smul, norm_div, norm_one, norm_pow, hzn, one_div, mul_comm, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hG_sphere z hz) (by positivity)
  rw [hcauchy, norm_smul] at hint_bd
  have hnorm_lhs : ‖2 * (Real.pi : ℂ) * I / (k ! : ℂ)‖ * ‖iteratedDeriv k (estermannG F) 2‖ =
      (2 * Real.pi) * ‖(k ! : ℂ)⁻¹ * iteratedDeriv k (estermannG F) 2‖ := by
    rw [div_eq_mul_inv, norm_mul, norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, norm_inv]
    ring
  rw [hnorm_lhs] at hint_bd
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hsub : ((C_ζ + 2) * B) / (3 / 2 : ℝ) ^ (k + 1) =
      (C_ζ + 2) * B * ((2 / 3 : ℝ) ^ k * (2 / 3 : ℝ)) := by
    have h1 : ((3 / 2 : ℝ) ^ (k + 1))⁻¹ = (2 / 3 : ℝ) ^ k * (2 / 3 : ℝ) := by
      rw [← inv_pow, show (3 / 2 : ℝ)⁻¹ = (2 / 3 : ℝ) by norm_num, pow_succ]
    rw [div_eq_mul_inv _ ((3 / 2 : ℝ) ^ (k + 1)), h1]
  have hrhs : 2 * Real.pi * (3 / 2 : ℝ) * (((C_ζ + 2) * B) / (3 / 2 : ℝ) ^ (k + 1)) =
      (2 * Real.pi) * ((C_ζ + 2) * B * (2 / 3 : ℝ) ^ k) := by
    rw [hsub]
    ring
  rw [hrhs] at hint_bd
  exact le_of_mul_le_mul_left hint_bd h2pi

private lemma estermannG_iteratedDeriv {F : ℂ → ℂ} {a : ℕ → ℂ}
    (hF_diff : Differentiable ℂ F) (ha_abs : LSeries.abscissaOfAbsConv a ≤ 1)
    (h_eq : ∀ s : ℂ, 1 < s.re → riemannZeta s * F s = LSeries a s) (k : ℕ) :
    iteratedDeriv k (estermannG F) 2 =
      (-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) 2 -
        F 1 * ((-1 : ℂ) ^ k * (k ! : ℂ)) := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
  have h2mem : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by norm_num
  have hG_nhd2 : estermannG F =ᶠ[𝓝 (2 : ℂ)] fun w ↦ LSeries a w - F 1 * (w - 1)⁻¹ := by
    filter_upwards [hopen.mem_nhds h2mem] with w hw
    have hw1 : w ≠ 1 := fun h ↦ by subst h; simp at hw
    rw [estermannG_eq F hw1, h_eq w hw, div_eq_mul_inv]
  have hL_cont : ContDiffAt ℂ k (LSeries a) 2 := by
    have hdiff_on : DifferentiableOn ℂ (fun w ↦ riemannZeta w * F w) {w : ℂ | 1 < w.re} := by
      intro w hw
      have hw1 : w ≠ 1 := fun h ↦ by subst h; simp at hw
      exact ((differentiableAt_riemannZeta hw1).mul (hF_diff w)).differentiableWithinAt
    have hcont_prod : ContDiffAt ℂ k (fun w ↦ riemannZeta w * F w) 2 :=
      (((hdiff_on.analyticOnNhd hopen).contDiffOn hopen.uniqueDiffOn).contDiffAt
        (hopen.mem_nhds h2mem)).of_le le_top
    have hev_eq : LSeries a =ᶠ[𝓝 (2 : ℂ)] fun w ↦ riemannZeta w * F w := by
      filter_upwards [hopen.mem_nhds h2mem] with w hw
      exact (h_eq w hw).symm
    exact hcont_prod.congr_of_eventuallyEq hev_eq
  have hinv_cont : ContDiffAt ℂ k (fun w : ℂ ↦ F 1 * (w - 1)⁻¹) 2 := by
    have hdiff_inv : DifferentiableOn ℂ (fun w : ℂ ↦ F 1 * (w - 1)⁻¹) {w | 1 < w.re} := by
      refine DifferentiableOn.const_mul (DifferentiableOn.inv ?_ ?_) (F 1)
      · exact differentiable_id.differentiableOn.sub_const (1 : ℂ)
      · intro w hw
        exact sub_ne_zero.mpr fun h ↦ by
          have hre := congrArg Complex.re h
          simp only [Complex.one_re] at hre
          have : (1 : ℝ) < w.re := hw
          linarith
    exact ((hdiff_inv.analyticOnNhd hopen).contDiffOn hopen.uniqueDiffOn).contDiffAt
      (hopen.mem_nhds h2mem) |>.of_le le_top
  rw [hG_nhd2.iteratedDeriv_eq k]
  change iteratedDeriv k (LSeries a - fun w : ℂ ↦ F 1 * (w - 1)⁻¹) 2 = _
  rw [iteratedDeriv_sub hL_cont hinv_cont,
    iteratedDeriv_const_mul_field,
    LSeries_iteratedDeriv k (lt_of_le_of_lt ha_abs
      (by simp only [Complex.re_ofNat]; exact_mod_cast (by norm_num : (1 : ℝ) < 2))),
    iteratedDeriv_inv_sub_one k (by norm_num : (2 : ℂ) ∈ {w : ℂ | w ≠ 1})]
  simp only [show (2 : ℂ) - 1 = 1 by norm_num, inv_one, one_pow, mul_one]

private lemma estermann_cseq_lower_bound {a : ℕ → ℂ}
    (ha_nn : ∀ n : ℕ, 0 ≤ (a n).re ∧ (a n).im = 0)
    (ha_one : a 1 = 1) (ha_abs : LSeries.abscissaOfAbsConv a ≤ 1) :
    (∀ k : ℕ, 0 ≤ (k ! : ℝ)⁻¹ * (LSeries (LSeries.logMul^[k] a) 2).re) ∧
      1 ≤ ((0 ! : ℝ)⁻¹ * (LSeries (LSeries.logMul^[0] a) 2).re) := by
  refine ⟨fun k ↦ mul_nonneg (by positivity) (lseries_logMul_iterate_nonneg_real ha_nn ha_abs k).1, ?_⟩
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, Function.iterate_zero, id_eq]
  have hsum2 : LSeriesSummable a 2 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (lt_of_le_of_lt ha_abs (by simp only [Complex.re_ofNat]; exact_mod_cast (by norm_num : (1 : ℝ) < 2)))
  have hsum_re : Summable fun n ↦ (LSeries.term a 2 n).re :=
    (Complex.reCLM.hasSum hsum2.hasSum).summable
  have hterm_nn : ∀ n : ℕ, 0 ≤ (LSeries.term a 2 n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    have hpow : (n : ℂ) ^ (2 : ℂ) = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [LSeries.term_of_ne_zero hn, hpow, div_eq_mul_inv, ← Complex.ofReal_inv,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, (ha_nn n).2, zero_mul, sub_zero]
    exact mul_nonneg (ha_nn n).1 (by positivity)
  have hts_re := (Complex.reCLM.hasSum hsum2.hasSum).tsum_eq
  simp only [Complex.reCLM_apply] at hts_re
  rw [LSeries, ← hts_re]
  have h1 : (LSeries.term a 2 1).re = 1 := by simp [LSeries.term, ha_one]
  rw [← h1]
  exact hsum_re.le_tsum 1 (fun n _ ↦ hterm_nn n)

private lemma estermann_term_re_eq {G : ℂ → ℂ} {a : ℕ → ℂ} {F : ℂ → ℂ} {β : ℝ} (k : ℕ)
    (hiter : iteratedDeriv k G 2 =
      (-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) 2 - F 1 * ((-1 : ℂ) ^ k * (k ! : ℂ))) :
    (((k ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ k • iteratedDeriv k G 2)).re =
      ((k ! : ℝ)⁻¹ * (LSeries (LSeries.logMul^[k] a) 2).re) * (2 - β) ^ k -
        (F 1).re * (2 - β) ^ k := by
  rw [smul_eq_mul, smul_eq_mul, hiter]
  have hsub_eq : ((β : ℂ) - 2) ^ k = (-1 : ℂ) ^ k * (((2 - β : ℝ) ^ k : ℝ) : ℂ) := by
    rw [show (β : ℂ) - 2 = (-1 : ℂ) * ((2 - β : ℝ) : ℂ) by push_cast; ring, mul_pow]
    push_cast
    rfl
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hcalc : (k ! : ℂ)⁻¹ * ((-1 : ℂ) ^ k * (((2 - β : ℝ) ^ k : ℝ) : ℂ)) *
      ((-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) 2 - F 1 * ((-1 : ℂ) ^ k * (k ! : ℂ))) =
      ((((k ! : ℝ)⁻¹ * (2 - β) ^ k : ℝ) : ℂ)) * LSeries (LSeries.logMul^[k] a) 2 -
        F 1 * (((2 - β : ℝ) ^ k : ℝ) : ℂ) := by
    have hk_ne : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    calc
      (k ! : ℂ)⁻¹ * ((-1 : ℂ) ^ k * (((2 - β : ℝ) ^ k : ℝ) : ℂ)) *
          ((-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) 2 - F 1 * ((-1 : ℂ) ^ k * (k ! : ℂ)))
        = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * (((k ! : ℂ)⁻¹ * (((2 - β : ℝ) ^ k : ℝ) : ℂ)) *
            LSeries (LSeries.logMul^[k] a) 2) -
          ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((k ! : ℂ)⁻¹ * (k ! : ℂ)) *
            F 1 * (((2 - β : ℝ) ^ k : ℝ) : ℂ) := by ring
      _ = ((((k ! : ℝ)⁻¹ * (2 - β) ^ k : ℝ) : ℂ)) * LSeries (LSeries.logMul^[k] a) 2 -
          F 1 * (((2 - β : ℝ) ^ k : ℝ) : ℂ) := by
          rw [hsign, inv_mul_cancel₀ hk_ne]
          push_cast
          ring
  rw [hsub_eq, ← mul_assoc, hcalc, Complex.sub_re, Complex.re_ofReal_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private noncomputable def estermannTerm (G : ℂ → ℂ) (β : ℝ) (k : ℕ) : ℂ :=
  (k ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ k • iteratedDeriv k G 2

private lemma estermann_tail_bound {C_ζ B β : ℝ} (hC_ζ : 0 < C_ζ) (hB : 0 ≤ B)
    (hβ_lo : 3 / 4 ≤ β) (hβ_lt : β < 1) {G : ℂ → ℂ} (hG_diff : Differentiable ℂ G)
    (hcoeff_bd : ∀ k : ℕ, ‖(k ! : ℂ)⁻¹ * iteratedDeriv k G 2‖ ≤ (C_ζ + 2) * B * (2 / 3 : ℝ) ^ k)
    (N : ℕ) :
    HasSum (fun k ↦ (estermannTerm G β k).re) (G (β : ℂ)).re ∧
      |∑' m : ℕ, (estermannTerm G β (m + N)).re| ≤ 6 * ((C_ζ + 2) * B) * (5 / 6 : ℝ) ^ N := by
  have ht_re_hasSum : HasSum (fun k ↦ (estermannTerm G β k).re) (G (β : ℂ)).re := by
    have ht0 := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_of_entire hG_diff 2 (β : ℂ))
    simp only [Complex.reCLM_apply] at ht0
    simpa only [estermannTerm] using ht0
  refine ⟨ht_re_hasSum, ?_⟩
  have hsplit := (hasSum_nat_add_iff' (f := fun k ↦ (estermannTerm G β k).re) N).2 ht_re_hasSum
  have hr_pos : 0 ≤ 2 - β := by linarith only [hβ_lt]
  have hprod_le : (2 / 3 : ℝ) * (2 - β) ≤ 5 / 6 := by linarith only [hβ_lo]
  have hterm_bd : ∀ m : ℕ, ‖(estermannTerm G β (m + N)).re‖ ≤
      ((C_ζ + 2) * B * (5 / 6 : ℝ) ^ N) * (5 / 6 : ℝ) ^ m := by
    intro m
    let k := m + N
    have hre_norm : ‖(estermannTerm G β k).re‖ ≤ ‖estermannTerm G β k‖ := by
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (estermannTerm G β k)
    have htk_norm : ‖estermannTerm G β k‖ ≤ (C_ζ + 2) * B * (2 / 3 : ℝ) ^ k * (2 - β) ^ k := by
      dsimp only [estermannTerm]
      rw [smul_eq_mul, smul_eq_mul, mul_left_comm, norm_mul, norm_pow,
        show (β : ℂ) - 2 = ((-(2 - β) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr_pos]
      rw [mul_comm ((2 - β) ^ k)]
      exact mul_le_mul_of_nonneg_right (hcoeff_bd k) (pow_nonneg hr_pos k)
    calc
      ‖(estermannTerm G β k).re‖ ≤ ‖estermannTerm G β k‖ := hre_norm
      _ ≤ (C_ζ + 2) * B * (2 / 3 : ℝ) ^ k * (2 - β) ^ k := htk_norm
      _ = (C_ζ + 2) * B * ((2 / 3 : ℝ) * (2 - β)) ^ k := by
          rw [mul_assoc _ ((2 / 3 : ℝ) ^ k), ← mul_pow]
      _ ≤ (C_ζ + 2) * B * (5 / 6 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprod_le k) (by positivity)
      _ = ((C_ζ + 2) * B * (5 / 6 : ℝ) ^ N) * (5 / 6 : ℝ) ^ m := by
          dsimp only [k]
          rw [pow_add]
          ring
  have hsum_geom : Summable fun m : ℕ ↦ ((C_ζ + 2) * B * (5 / 6 : ℝ) ^ N) * (5 / 6 : ℝ) ^ m :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc
    |∑' m : ℕ, (estermannTerm G β (m + N)).re| = ‖∑' m : ℕ, (estermannTerm G β (m + N)).re‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' m : ℕ, ‖(estermannTerm G β (m + N)).re‖ := norm_tsum_le_tsum_norm (hsplit.summable.norm)
    _ ≤ ∑' m : ℕ, ((C_ζ + 2) * B * (5 / 6 : ℝ) ^ N) * (5 / 6 : ℝ) ^ m :=
        hsplit.summable.norm.tsum_le_tsum hterm_bd hsum_geom
    _ = ((C_ζ + 2) * B * (5 / 6 : ℝ) ^ N) * ∑' m : ℕ, (5 / 6 : ℝ) ^ m := tsum_mul_left
    _ = ((C_ζ + 2) * B * (5 / 6 : ℝ) ^ N) * (1 - 5 / 6 : ℝ)⁻¹ := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 6 * ((C_ζ + 2) * B) * (5 / 6 : ℝ) ^ N := by norm_num; ring

private lemma estermann_taylor_lower_bound :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ (F : ℂ → ℂ) (a : ℕ → ℂ) (B : ℝ),
      0 ≤ B →
      Differentiable ℂ F →
      (∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ), ‖F z‖ ≤ B) →
      (∀ n : ℕ, 0 ≤ (a n).re ∧ (a n).im = 0) →
      a 1 = 1 →
      LSeries.abscissaOfAbsConv a ≤ 1 →
      (∀ s : ℂ, 1 < s.re → riemannZeta s * F s = LSeries a s) →
      ∀ {β : ℝ}, 3 / 4 ≤ β → β < 1 →
        (riemannZeta (β : ℂ) * F (β : ℂ)).re ≤ 0 →
        ∀ N : ℕ, 1 ≤ N →
          1 - 6 * (C_E * B) * (5 / 6 : ℝ) ^ N ≤
            (F 1).re * ((2 - β) ^ N / (1 - β)) := by
  obtain ⟨C_ζ, hC_ζ, hzeta_sphere⟩ := riemannZeta_bound_sphere_two
  refine ⟨C_ζ + 2, by positivity, fun F a B hB hF_diff hF_ball ha_nn ha_one ha_abs h_eq
      {β} hβ_lo hβ_lt h_neg N hN ↦ ?_⟩
  have hG_diff : Differentiable ℂ (estermannG F) := estermannG_differentiable hF_diff
  have hcoeff_bd : ∀ k : ℕ,
      ‖(k ! : ℂ)⁻¹ * iteratedDeriv k (estermannG F) 2‖ ≤ (C_ζ + 2) * B * (2 / 3 : ℝ) ^ k :=
    estermannG_coeff_bound hC_ζ hB hzeta_sphere hF_diff hF_ball
  have hiterG : ∀ k : ℕ, iteratedDeriv k (estermannG F) 2 =
      (-1 : ℂ) ^ k * LSeries (LSeries.logMul^[k] a) 2 - F 1 * ((-1 : ℂ) ^ k * (k ! : ℂ)) :=
    estermannG_iteratedDeriv hF_diff ha_abs h_eq
  obtain ⟨hcseq_nn, hcseq_0⟩ := estermann_cseq_lower_bound ha_nn ha_one ha_abs
  obtain ⟨ht_re_hasSum, htail_bd⟩ :=
    estermann_tail_bound hC_ζ hB hβ_lo hβ_lt hG_diff hcoeff_bd N
  let t : ℕ → ℂ := estermannTerm (estermannG F) β
  let cseq : ℕ → ℝ := fun k ↦ (k ! : ℝ)⁻¹ * (LSeries (LSeries.logMul^[k] a) 2).re
  have hsplit := (hasSum_nat_add_iff' (f := fun k ↦ (t k).re) N).2 ht_re_hasSum
  have hsum_eq : ∑ k ∈ Finset.range N, (t k).re + ∑' m : ℕ, (t (m + N)).re =
      (estermannG F (β : ℂ)).re := by
    rw [hsplit.tsum_eq]
    ring
  have hsum_N_eval : ∑ k ∈ Finset.range N, (t k).re =
      ∑ k ∈ Finset.range N, cseq k * (2 - β) ^ k -
        (F 1).re * (((2 - β) ^ N - 1) / (1 - β)) := by
    have hcongr : ∑ k ∈ Finset.range N, (t k).re =
        ∑ k ∈ Finset.range N, (cseq k * (2 - β) ^ k - (F 1).re * (2 - β) ^ k) :=
      Finset.sum_congr rfl fun k _ ↦ by
        dsimp only [t, estermannTerm]
        exact estermann_term_re_eq k (hiterG k)
    rw [hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hgeom : ∑ k ∈ Finset.range N, (2 - β) ^ k = ((2 - β) ^ N - 1) / (1 - β) := by
      have hne1 : (2 - β : ℝ) ≠ 1 := by linarith only [hβ_lt]
      rw [geom_sum_eq hne1, show (2 - β : ℝ) - 1 = 1 - β by ring]
    rw [hgeom]
  have hc_sum_ge : 1 ≤ ∑ k ∈ Finset.range N, cseq k * (2 - β) ^ k := by
    have h0mem : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
    have hge : cseq 0 * (2 - β) ^ 0 ≤ ∑ k ∈ Finset.range N, cseq k * (2 - β) ^ k :=
      Finset.single_le_sum
        (fun k _ ↦ mul_nonneg (hcseq_nn k) (pow_nonneg (by linarith only [hβ_lt]) _)) h0mem
    have h0 : 1 ≤ cseq 0 * (2 - β) ^ 0 := by
      dsimp only [cseq]
      simpa using hcseq_0
    exact h0.trans hge
  have hG_beta : (estermannG F (β : ℂ)).re ≤ (F 1).re / (1 - β) := by
    have hne : (β : ℂ) ≠ 1 := by exact_mod_cast hβ_lt.ne
    rw [estermannG_eq F hne, Complex.sub_re]
    have hdiv_eq : (F 1 / ((β : ℂ) - 1)).re = -((F 1).re / (1 - β)) := by
      rw [show (β : ℂ) - 1 = (-(1 - β : ℝ) : ℂ) by push_cast; ring,
        div_neg, Complex.neg_re, Complex.div_ofReal_re]
    linarith only [h_neg, hdiv_eq]
  have htail_lo : -(6 * ((C_ζ + 2) * B) * (5 / 6 : ℝ) ^ N) ≤ ∑' m : ℕ, (t (m + N)).re :=
    (abs_le.mp htail_bd).1
  calc
    1 - 6 * ((C_ζ + 2) * B) * (5 / 6 : ℝ) ^ N
      ≤ ∑ k ∈ Finset.range N, cseq k * (2 - β) ^ k + ∑' m : ℕ, (t (m + N)).re := by
          linarith only [hc_sum_ge, htail_lo]
    _ = ∑ k ∈ Finset.range N, (t k).re + ∑' m : ℕ, (t (m + N)).re +
          (F 1).re * (((2 - β) ^ N - 1) / (1 - β)) := by rw [hsum_N_eval]; ring
    _ = (estermannG F (β : ℂ)).re + (F 1).re * (((2 - β) ^ N - 1) / (1 - β)) := by
          rw [hsum_eq]
    _ ≤ (F 1).re / (1 - β) + (F 1).re * (((2 - β) ^ N - 1) / (1 - β)) := by
          linarith only [hG_beta]
    _ = (F 1).re * ((2 - β) ^ N / (1 - β)) := by
        have hne : 1 - β ≠ 0 := by linarith only [hβ_lt]
        field_simp [hne]
        ring

private lemma estermann_taylor_half_lower_bound :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ (F : ℂ → ℂ) (a : ℕ → ℂ) (B : ℝ),
      0 ≤ B →
      Differentiable ℂ F →
      (∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ), ‖F z‖ ≤ B) →
      (∀ n : ℕ, 0 ≤ (a n).re ∧ (a n).im = 0) →
      a 1 = 1 →
      LSeries.abscissaOfAbsConv a ≤ 1 →
      (∀ s : ℂ, 1 < s.re → riemannZeta s * F s = LSeries a s) →
      ∀ {β : ℝ}, 3 / 4 ≤ β → β < 1 →
        (riemannZeta (β : ℂ) * F (β : ℂ)).re ≤ 0 →
        ∃ N : ℕ, 1 ≤ N ∧
          (N : ℝ) ≤ Real.log (12 * (C_E * B + 1)) / Real.log (6 / 5) + 2 ∧
          (1 / 2 : ℝ) ≤ (F 1).re * ((2 - β) ^ N / (1 - β)) := by
  obtain ⟨C_E, hC_E, hmain⟩ := estermann_taylor_lower_bound
  refine ⟨C_E, hC_E, fun F a B hB hF_diff hF_ball ha_nn ha_one ha_abs h_eq
      {β} hβ_lo hβ_lt h_neg ↦ ?_⟩
  let N : ℕ := Nat.ceil (Real.log (12 * (C_E * B + 1)) / Real.log (6 / 5)) + 1
  have h12_ge : 12 ≤ 12 * (C_E * B + 1) := by nlinarith
  have hlog65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hlog12_pos : 0 < Real.log (12 * (C_E * B + 1)) := Real.log_pos (by linarith)
  have hratio_nn : 0 ≤ Real.log (12 * (C_E * B + 1)) / Real.log (6 / 5) :=
    div_nonneg hlog12_pos.le hlog65.le
  have hN_ge1 : 1 ≤ N := Nat.le_add_left 1 _
  have hN_le : (N : ℝ) ≤ Real.log (12 * (C_E * B + 1)) / Real.log (6 / 5) + 2 := by
    have hceil := Nat.ceil_lt_add_one hratio_nn
    dsimp only [N]
    push_cast
    linarith
  have hN_ge_ratio : Real.log (12 * (C_E * B + 1)) / Real.log (6 / 5) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by dsimp only [N]; push_cast; linarith)
  have hpow65 : 12 * (C_E * B + 1) ≤ (6 / 5 : ℝ) ^ N := by
    have h1 : Real.log (12 * (C_E * B + 1)) ≤ (N : ℝ) * Real.log (6 / 5) := by
      rwa [div_le_iff₀ hlog65] at hN_ge_ratio
    rw [← Real.log_pow (6 / 5 : ℝ) N] at h1
    have hexp := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by linarith), Real.exp_log (by positivity)] at hexp
  have hpow56 : (5 / 6 : ℝ) ^ N ≤ 1 / (12 * (C_E * B + 1)) := by
    rw [show (5 / 6 : ℝ) = (6 / 5 : ℝ)⁻¹ by norm_num, inv_pow, one_div]
    exact inv_anti₀ (by linarith) hpow65
  have htail_half : 6 * (C_E * B) * (5 / 6 : ℝ) ^ N ≤ 1 / 2 := by
    have hne : C_E * B + 1 ≠ 0 := by positivity
    calc
      6 * (C_E * B) * (5 / 6 : ℝ) ^ N
        ≤ 6 * (C_E * B) * (1 / (12 * (C_E * B + 1))) :=
          mul_le_mul_of_nonneg_left hpow56 (by positivity)
      _ = (1 / 2 : ℝ) * ((C_E * B) / (C_E * B + 1)) := by field_simp [hne]; ring
      _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) (by norm_num)
      _ = 1 / 2 := mul_one _
  have hbd := hmain F a B hB hF_diff hF_ball ha_nn ha_one ha_abs h_eq hβ_lo hβ_lt h_neg N hN_ge1
  exact ⟨N, hN_ge1, hN_le, by linarith⟩

end EstermannEngine

section PageTheorem

open scoped ComplexOrder

private lemma zetaMul_nonneg_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hr : IsReal χ) (n : ℕ) :
    0 ≤ (χ.zetaMul n).re ∧ (χ.zetaMul n).im = 0 := by
  have hsq : χ ^ 2 = 1 := (isReal_iff_sq_eq_one χ).mp hr
  have h := Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg hsq n)
  exact ⟨h.1, h.2.symm⟩

private lemma zetaMul_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.zetaMul 1 = 1 :=
  χ.isMultiplicative_zetaMul.map_one

private lemma zetaMul_abscissa {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (χ.zetaMul : ℕ → ℂ) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact χ.LSeriesSummable_zetaMul (by simpa using hy)

private lemma zetaMul_LSeries_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * DirichletCharacter.LFunction χ s = LSeries (χ.zetaMul : ℕ → ℂ) s := by
  rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution']
  · rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    congr 1
    · simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← ArithmeticFunction.natCoe_apply]
    · exact LSeries_congr χ.apply_eq_toArithmeticFunction_apply s
  · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  · refine (LSeriesSummable_congr s fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr ?_
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs

private lemma page_LFunction_ball_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 1000 * (q : ℝ) ^ 2 := by
  intro z hz
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hz_dist : ‖z - 2‖ ≤ 3 / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre : 1 / 2 ≤ z.re := by
    have h := (Complex.abs_re_le_norm (z - 2)).trans hz_dist
    simp only [Complex.sub_re, Complex.re_ofNat] at h
    linarith [(abs_le.mp h).1]
  have him : |z.im| ≤ 3 / 2 := by
    have h := (Complex.abs_im_le_norm (z - 2)).trans hz_dist
    simpa using h
  have hbd := norm_LFunction_re_ge_half_le hχ hre
  have hq_poly : (q : ℝ) + 48 * (q : ℝ) ^ 2 + 2 ≤ 51 * (q : ℝ) ^ 2 := by nlinarith
  have him_sq : (|z.im| + 2) ^ 2 ≤ 13 := by nlinarith [abs_nonneg z.im]
  calc
    ‖DirichletCharacter.LFunction χ z‖ ≤ ((q : ℝ) + 48 * (q : ℝ) ^ 2 + 2) * (|z.im| + 2) ^ 2 := hbd
    _ ≤ (51 * (q : ℝ) ^ 2) * 13 := mul_le_mul hq_poly him_sq (sq_nonneg _) (by positivity)
    _ ≤ 1000 * (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]

private lemma page_LFunction_real_pos_of_no_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hr : IsReal χ) {β : ℝ} (hβ_le : β ≤ 1)
    (hno : ∀ σ ∈ Set.Icc β 1, DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) :
    0 < (DirichletCharacter.LFunction χ (β : ℂ)).re := by
  let f : ℝ → ℝ := fun x ↦ (DirichletCharacter.LFunction χ (x : ℂ)).re
  have hf_cont : Continuous f :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal)
  have hf1 : 0 < f 1 := by simpa [f] using LFunction_one_pos_of_isReal hχ hr
  by_contra hle
  push Not at hle
  obtain ⟨σ, hσ_mem, hσ_zero⟩ := intermediate_value_Icc hβ_le hf_cont.continuousOn ⟨hle, hf1.le⟩
  have hzero : DirichletCharacter.LFunction χ (σ : ℂ) = 0 :=
    Complex.ext hσ_zero (LFunction_real_im_zero hχ hr σ)
  exact hno σ hσ_mem hzero

private lemma page_lower_bound_of_no_zero_aux :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧ ∀ {q : ℕ} [NeZero q], 2 ≤ q →
      ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 → IsReal χ →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          (∀ σ ∈ Set.Icc (1 - δ / Real.log ((q : ℝ) + 2)) 1,
            DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
          δ / (2 * Real.exp 1 * Real.log ((q : ℝ) + 2)) ≤
            (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨C_E, hC_E, hhalf⟩ := estermann_taylor_half_lower_bound
  let K : ℝ := 12 * (1000 * C_E + 1)
  have hK_ge : 12 ≤ K := by dsimp only [K]; nlinarith
  have hlog65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
  let M : ℝ := (2 + Real.log K) / Real.log (6 / 5) + 2
  have hM_pos : 0 < M := by positivity
  let δ₀ : ℝ := min (1 / 4) (1 / M)
  have hδ₀_pos : 0 < δ₀ := lt_min (by norm_num) (one_div_pos.mpr hM_pos)
  refine ⟨δ₀, hδ₀_pos, min_le_left _ _, fun {q} _ hq {χ} hχ hr δ hδ_pos hδ_le hno ↦ ?_⟩
  let L : ℝ := Real.log ((q : ℝ) + 2)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL_ge1 : 1 ≤ L := by
    have hexp : Real.exp 1 ≤ (q : ℝ) + 2 := Real.exp_one_lt_d9.le.trans (by linarith)
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hexp)
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge1
  have hδ_le_quarter : δ ≤ 1 / 4 := hδ_le.trans (min_le_left _ _)
  have hδ_le_invM : δ ≤ 1 / M := hδ_le.trans (min_le_right _ _)
  let β : ℝ := 1 - δ / L
  have hdiv_pos : 0 < δ / L := div_pos hδ_pos hL_pos
  have hβ_lt : β < 1 := sub_lt_self 1 hdiv_pos
  have hβ_lo : 3 / 4 ≤ β := by
    have hdiv_le : δ / L ≤ 1 / 4 := by
      calc
        δ / L ≤ (1 / 4) / 1 := div_le_div₀ (by norm_num) hδ_le_quarter zero_lt_one hL_ge1
        _ = 1 / 4 := div_one _
    dsimp only [β]
    rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num]
    exact sub_le_sub_left hdiv_le 1
  have hβ_Ioo : β ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, hβ_lt⟩
  have hLβ_pos : 0 < (DirichletCharacter.LFunction χ (β : ℂ)).re :=
    page_LFunction_real_pos_of_no_zero hχ hr hβ_lt.le hno
  have hζ_neg := riemannZeta_neg_on_Ioo hβ_Ioo
  have hprod_nonpos : (riemannZeta (β : ℂ) * DirichletCharacter.LFunction χ (β : ℂ)).re ≤ 0 := by
    have hζ_le0 : (riemannZeta (β : ℂ)).re ≤ 0 :=
      hζ_neg.2.trans (div_nonpos_of_nonneg_of_nonpos hβ_Ioo.1.le (by linarith))
    rw [Complex.mul_re, hζ_neg.1, LFunction_real_im_zero hχ hr β, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hζ_le0 hLβ_pos.le
  obtain ⟨N, _, hN_le, hhalf_bd⟩ := hhalf (DirichletCharacter.LFunction χ) (χ.zetaMul : ℕ → ℂ)
    (1000 * (q : ℝ) ^ 2) (by positivity) (DirichletCharacter.differentiable_LFunction hχ)
    (page_LFunction_ball_bound hχ) (zetaMul_nonneg_real hr) (zetaMul_one χ)
    (zetaMul_abscissa χ) (fun s hs ↦ zetaMul_LSeries_eq χ hs) hβ_lo hβ_lt hprod_nonpos
  have hN_le_ML : (N : ℝ) ≤ M * L := by
    have hq_sq : (q : ℝ) ^ 2 ≤ ((q : ℝ) + 2) ^ 2 := by nlinarith
    have h1_sq : (1 : ℝ) ≤ ((q : ℝ) + 2) ^ 2 := by nlinarith
    have harg_le : 12 * (C_E * (1000 * (q : ℝ) ^ 2) + 1) ≤ K * ((q : ℝ) + 2) ^ 2 := by
      dsimp only [K]
      nlinarith
    have hlog_arg : Real.log (12 * (C_E * (1000 * (q : ℝ) ^ 2) + 1)) ≤
        Real.log K + 2 * L := by
      have hpos1 : 0 < 12 * (C_E * (1000 * (q : ℝ) ^ 2) + 1) := by positivity
      calc
        Real.log (12 * (C_E * (1000 * (q : ℝ) ^ 2) + 1))
          ≤ Real.log (K * ((q : ℝ) + 2) ^ 2) := Real.log_le_log hpos1 harg_le
        _ = Real.log K + Real.log (((q : ℝ) + 2) ^ 2) :=
            Real.log_mul (by positivity) (by positivity)
        _ = Real.log K + 2 * L := by
            rw [Real.log_pow]
            dsimp only [L]
            ring
    have hlog_le_prod : Real.log K + 2 * L ≤ (2 + Real.log K) * L := by
      nlinarith [hL_ge1, hlogK]
    calc
      (N : ℝ) ≤ Real.log (12 * (C_E * (1000 * (q : ℝ) ^ 2) + 1)) / Real.log (6 / 5) + 2 := hN_le
      _ ≤ ((2 + Real.log K) * L) / Real.log (6 / 5) + 2 * L :=
          add_le_add (div_le_div_of_nonneg_right (hlog_arg.trans hlog_le_prod) hlog65.le)
            (by linarith [hL_ge1])
      _ = M * L := by dsimp only [M]; ring
  have hpow_le_exp : (2 - β) ^ N ≤ Real.exp 1 := by
    have hadd_exp : 2 - β ≤ Real.exp (1 - β) := by
      linarith [Real.add_one_le_exp (1 - β)]
    have hN_mul_le : (N : ℝ) * (1 - β) ≤ 1 := by
      have h1β : 1 - β = δ / L := by dsimp only [β]; ring
      have hMδ : M * δ ≤ 1 := by
        rw [mul_comm]
        exact (le_div_iff₀ hM_pos).mp hδ_le_invM
      calc
        (N : ℝ) * (1 - β) = (N : ℝ) * (δ / L) := by rw [h1β]
        _ ≤ (M * L) * (δ / L) := mul_le_mul_of_nonneg_right hN_le_ML (by positivity)
        _ = M * δ := by field_simp [hL_pos.ne']
        _ ≤ 1 := hMδ
    calc
      (2 - β) ^ N ≤ (Real.exp (1 - β)) ^ N := pow_le_pow_left₀ (by linarith) hadd_exp N
      _ = Real.exp ((N : ℝ) * (1 - β)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hN_mul_le
  have hL1_pos : 0 < (DirichletCharacter.LFunction χ 1).re := LFunction_one_pos_of_isReal hχ hr
  have h1β_pos : 0 < 1 - β := by dsimp only [β]; rw [sub_sub_cancel]; exact div_pos hδ_pos hL_pos
  have hbound1 : 1 / 2 ≤ (DirichletCharacter.LFunction χ 1).re * (Real.exp 1 / (δ / L)) := by
    have hfrac_le : (2 - β) ^ N / (1 - β) ≤ Real.exp 1 / (δ / L) := by
      rw [show 1 - β = δ / L by dsimp only [β]; ring]
      exact div_le_div_of_nonneg_right hpow_le_exp (div_pos hδ_pos hL_pos).le
    exact hhalf_bd.trans (mul_le_mul_of_nonneg_left hfrac_le hL1_pos.le)
  have hcoeff_pos : 0 < δ / (2 * Real.exp 1 * L) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hbound1 (div_pos hδ_pos hL_pos).le
  have hsim1 : (1 / 2 : ℝ) * (δ / L) = δ / (2 * L) := by ring
  have hsim2 : (DirichletCharacter.LFunction χ 1).re * (Real.exp 1 / (δ / L)) * (δ / L) =
      (DirichletCharacter.LFunction χ 1).re * Real.exp 1 := by
    have hne : δ / L ≠ 0 := (div_pos hδ_pos hL_pos).ne'
    field_simp [hne]
  rw [hsim1, hsim2] at hmul
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  calc
    δ = (2 * L) * (δ / (2 * L)) := by field_simp [hL_pos.ne']
    _ ≤ (2 * L) * ((DirichletCharacter.LFunction χ 1).re * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = (DirichletCharacter.LFunction χ 1).re * (2 * Real.exp 1 * L) := by ring

/-- Effective lower bound for `L(1, χ)` when `L(s, χ)` has no real zero near `s = 1`.
There exists an absolute constant `c > 0` such that if `χ ≠ 1` is a real Dirichlet character
modulo `q ≥ 2` and `L(s, χ)` does not vanish on `[1 - δ / log (q + 2), 1]` for some `δ > 0`,
then `c * min δ 1 / log (q + 2) ≤ (LFunction χ 1).re`. -/
theorem page_theorem_of_no_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q},
      χ ≠ 1 → IsReal χ → ∀ δ : ℝ, 0 < δ →
        (∀ σ ∈ Set.Icc (1 - δ / Real.log ((q : ℝ) + 2)) 1,
          DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
        c * min δ 1 / Real.log ((q : ℝ) + 2) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨δ₀, hδ₀_pos, hδ₀_le, haux⟩ := page_lower_bound_of_no_zero_aux
  refine ⟨δ₀ / (2 * Real.exp 1), by positivity, fun {q} _ hq {χ} hχ hr δ hδ_pos hno ↦ ?_⟩
  let δ' : ℝ := min δ δ₀
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hδ₀_pos
  have hδ'_le : δ' ≤ δ₀ := min_le_right _ _
  have hL_pos : 0 < Real.log ((q : ℝ) + 2) := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    exact Real.log_pos (by linarith)
  have hno' : ∀ σ ∈ Set.Icc (1 - δ' / Real.log ((q : ℝ) + 2)) 1,
      DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
    intro σ hσ
    apply hno σ
    refine ⟨?_, hσ.2⟩
    have hdiv : δ' / Real.log ((q : ℝ) + 2) ≤ δ / Real.log ((q : ℝ) + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hL_pos.le
    exact (sub_le_sub_left hdiv 1).trans hσ.1
  have hbd := haux hq hχ hr δ' hδ'_pos hδ'_le hno'
  have hmin_le : δ₀ * min δ 1 ≤ δ' := by
    refine le_min ?_ ?_
    · calc
        δ₀ * min δ 1 ≤ 1 * δ := mul_le_mul (by linarith) (min_le_left _ _)
            (le_min hδ_pos.le zero_le_one) zero_le_one
        _ = δ := one_mul δ
    · exact mul_le_of_le_one_right hδ₀_pos.le (min_le_right _ _)
  calc
    (δ₀ / (2 * Real.exp 1)) * min δ 1 / Real.log ((q : ℝ) + 2)
      = (δ₀ * min δ 1) / (2 * Real.exp 1 * Real.log ((q : ℝ) + 2)) := by ring
    _ ≤ δ' / (2 * Real.exp 1 * Real.log ((q : ℝ) + 2)) :=
        div_le_div_of_nonneg_right hmin_le (by positivity)
    _ ≤ (DirichletCharacter.LFunction χ 1).re := hbd

/-- Page's theorem on real zeros and `L(1, χ)` values in a modulus range `2 ≤ q ≤ Q`.
There exist absolute constants `c_P > 0` and `c₁ > 0` such that for every `Q ≥ 2`,
there is at most one primitive real non-principal character `exc = ⟨q₀, χ₀⟩` such that
for every primitive real character `χ ≠ 1` modulo `q` with `2 ≤ (q : ℝ) ≤ Q` and
`⟨q, χ⟩ ≠ exc`, `L(s, χ)` has no zero in `[1 - c_P / log (Q + 2), 1]` and
`c₁ / log (Q + 2) ≤ (LFunction χ 1).re`. -/
theorem page_theorem :
    ∃ c_P c₁ : ℝ, 0 < c_P ∧ 0 < c₁ ∧ ∀ Q : ℝ, 2 ≤ Q →
      ∃ exc : Σ q : ℕ, DirichletCharacter ℂ q,
        ∀ {q : ℕ} [NeZero q], 2 ≤ q → (q : ℝ) ≤ Q →
          ∀ {χ : DirichletCharacter ℂ q}, χ.IsPrimitive → IsReal χ → χ ≠ 1 →
            (⟨q, χ⟩ : Σ m : ℕ, DirichletCharacter ℂ m) ≠ exc →
            (∀ σ ∈ Set.Icc (1 - c_P / Real.log (Q + 2)) 1,
              DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) ∧
            c₁ / Real.log (Q + 2) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨c_L, hc_L, hlandau⟩ := landau_two_characters
  obtain ⟨c₀, hc₀, hnozero⟩ := page_theorem_of_no_zero
  let c_P : ℝ := min (c_L / 2) (1 / 4)
  have hc_P_pos : 0 < c_P := lt_min (by positivity) (by norm_num)
  refine ⟨c_P, c₀ * c_P, hc_P_pos, mul_pos hc₀ hc_P_pos, fun Q hQ ↦ ?_⟩
  have hLQ_ge1 : 1 ≤ Real.log (Q + 2) := by
    have hexp : Real.exp 1 ≤ Q + 2 := Real.exp_one_lt_d9.le.trans (by linarith)
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hexp)
  have hLQ_pos : 0 < Real.log (Q + 2) := lt_of_lt_of_le zero_lt_one hLQ_ge1
  have hcP_div : c_P / Real.log (Q + 2) ≤ 1 / 4 := by
    calc
      c_P / Real.log (Q + 2) ≤ (1 / 4) / 1 :=
          div_le_div₀ (by norm_num) (min_le_right _ _) zero_lt_one hLQ_ge1
      _ = 1 / 4 := div_one _
  have hno_to_L1 : ∀ {q : ℕ} [NeZero q], 2 ≤ q → (q : ℝ) ≤ Q →
      ∀ {χ : DirichletCharacter ℂ q}, IsReal χ → χ ≠ 1 →
        (∀ σ ∈ Set.Icc (1 - c_P / Real.log (Q + 2)) 1,
          DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
        c₀ * c_P / Real.log (Q + 2) ≤ (DirichletCharacter.LFunction χ 1).re := by
    intro q _ hq hqQ χ hr hχ hno
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hLq_pos : 0 < Real.log ((q : ℝ) + 2) := Real.log_pos (by linarith)
    let δ : ℝ := c_P * Real.log ((q : ℝ) + 2) / Real.log (Q + 2)
    have hδ_pos : 0 < δ := by positivity
    have hδ_le1 : δ ≤ 1 := by
      have hlog_le : Real.log ((q : ℝ) + 2) ≤ Real.log (Q + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hcP_le1 : c_P ≤ 1 := (min_le_right _ _).trans (by norm_num)
      calc
        δ ≤ 1 * (Real.log ((q : ℝ) + 2) / Real.log (Q + 2)) := by
            dsimp only [δ]; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hcP_le1 (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ((div_le_one hLQ_pos).mpr hlog_le) zero_le_one
        _ = 1 := one_mul 1
    have hno_scaled : ∀ σ ∈ Set.Icc (1 - δ / Real.log ((q : ℝ) + 2)) 1,
        DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
      have hdiv_eq : δ / Real.log ((q : ℝ) + 2) = c_P / Real.log (Q + 2) := by
        dsimp only [δ]
        field_simp [hLq_pos.ne', hLQ_pos.ne']
      simpa only [hdiv_eq] using hno
    have hbd := hnozero hq hχ hr δ hδ_pos hno_scaled
    have heq_lhs : c₀ * min δ 1 / Real.log ((q : ℝ) + 2) = c₀ * c_P / Real.log (Q + 2) := by
      rw [min_eq_left hδ_le1]
      dsimp only [δ]
      field_simp [hLq_pos.ne', hLQ_pos.ne']
    rwa [heq_lhs] at hbd
  by_cases hEx : ∃ (q₀ : ℕ) (_ : NeZero q₀), 2 ≤ q₀ ∧ (q₀ : ℝ) ≤ Q ∧
      ∃ χ₀ : DirichletCharacter ℂ q₀, χ₀.IsPrimitive ∧ IsReal χ₀ ∧ χ₀ ≠ 1 ∧
        ∃ β₀ ∈ Set.Icc (1 - c_P / Real.log (Q + 2)) 1,
          DirichletCharacter.LFunction χ₀ (β₀ : ℂ) = 0
  · obtain ⟨q₀, hnz₀, hq₀_ge, hq₀_le, χ₀, hp₀, hr₀, hχ₀, β₀, hβ₀_mem, hβ₀_zero⟩ := hEx
    refine ⟨⟨q₀, χ₀⟩, fun {q} _ hq hqQ {χ} hp hr hχ hneq ↦ ?_⟩
    have hno : ∀ σ ∈ Set.Icc (1 - c_P / Real.log (Q + 2)) 1,
        DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
      intro β hβ_mem hβ_zero
      have hsub_ge : (3 / 4 : ℝ) ≤ 1 - c_P / Real.log (Q + 2) := by
        have := sub_le_sub_left hcP_div 1
        linarith only [this]
      have hβ_pos : 0 < β := by linarith only [hβ_mem.1, hsub_ge]
      have hβ₀_pos : 0 < β₀ := by linarith only [hβ₀_mem.1, hsub_ge]
      have hmin := hlandau hp hp₀ hr hr₀ hχ hχ₀ hneq hβ_pos hβ₀_pos hβ_zero hβ₀_zero
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have hq₀2 : (2 : ℝ) ≤ q₀ := by exact_mod_cast hq₀_ge
      have hprod_le : (q : ℝ) * q₀ + 2 ≤ (Q + 2) ^ 2 := by nlinarith
      have hlog_le : Real.log ((q : ℝ) * q₀ + 2) ≤ 2 * Real.log (Q + 2) := by
        calc
          Real.log ((q : ℝ) * q₀ + 2) ≤ Real.log ((Q + 2) ^ 2) :=
              Real.log_le_log (by positivity) hprod_le
          _ = 2 * Real.log (Q + 2) := by rw [Real.log_pow]; ring
      have hcL_le : c_P / Real.log (Q + 2) ≤ c_L / Real.log ((q : ℝ) * q₀ + 2) := by
        calc
          c_P / Real.log (Q + 2) ≤ (c_L / 2) / Real.log (Q + 2) :=
              div_le_div_of_nonneg_right (min_le_left _ _) hLQ_pos.le
          _ = c_L / (2 * Real.log (Q + 2)) := by ring
          _ ≤ c_L / Real.log ((q : ℝ) * q₀ + 2) :=
              div_le_div_of_nonneg_left hc_L.le (Real.log_pos (by nlinarith)) hlog_le
      have hmin_ge : 1 - c_P / Real.log (Q + 2) ≤ min β β₀ := le_min hβ_mem.1 hβ₀_mem.1
      have hcL_sub : 1 - c_L / Real.log ((q : ℝ) * q₀ + 2) ≤ 1 - c_P / Real.log (Q + 2) :=
        sub_le_sub_left hcL_le 1
      linarith only [hmin, hcL_sub, hmin_ge]
    exact ⟨hno, hno_to_L1 hq hqQ hr hχ hno⟩
  · refine ⟨⟨1, 1⟩, fun {q} _ hq hqQ {χ} hp hr hχ _ ↦ ?_⟩
    have hno : ∀ σ ∈ Set.Icc (1 - c_P / Real.log (Q + 2)) 1,
        DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
      intro β hβ_mem hβ_zero
      exact hEx ⟨q, inferInstance, hq, hqQ, χ, hp, hr, hχ, β, hβ_mem, hβ_zero⟩
    exact ⟨hno, hno_to_L1 hq hqQ hr hχ hno⟩

/-- Page's theorem over a power range `2 ≤ q ≤ Q ^ A` (`Q ≥ 2`, `A ≥ 1`).
There exist absolute constants `c_P > 0` and `c₁ > 0` such that outside at most one
exceptional primitive real character, every primitive real character `χ ≠ 1` with `2 ≤ q ≤ Q ^ A`
has no real zero in `[1 - c_P / (A * log (Q + 2)), 1]` and satisfies
`c₁ / (A * log (Q + 2)) ≤ (LFunction χ 1).re`. -/
theorem page_theorem_pow_range :
    ∃ c_P c₁ : ℝ, 0 < c_P ∧ 0 < c₁ ∧ ∀ (Q A : ℝ), 2 ≤ Q → 1 ≤ A →
      ∃ exc : Σ q : ℕ, DirichletCharacter ℂ q,
        ∀ {q : ℕ} [NeZero q], 2 ≤ q → (q : ℝ) ≤ Q ^ A →
          ∀ {χ : DirichletCharacter ℂ q}, χ.IsPrimitive → IsReal χ → χ ≠ 1 →
            (⟨q, χ⟩ : Σ m : ℕ, DirichletCharacter ℂ m) ≠ exc →
            (∀ σ ∈ Set.Icc (1 - c_P / (A * Real.log (Q + 2))) 1,
              DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) ∧
            c₁ / (A * Real.log (Q + 2)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨c_P, c₁, hc_P, hc₁, hpage⟩ := page_theorem
  refine ⟨c_P / 2, c₁ / 2, by positivity, by positivity, fun Q A hQ hA ↦ ?_⟩
  have hQpow_ge2 : 2 ≤ Q ^ A :=
    hQ.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith) hA)
  obtain ⟨exc, hexc⟩ := hpage (Q ^ A) hQpow_ge2
  refine ⟨exc, fun {q} _ hq hq_le {χ} hp hr hχ hneq ↦ ?_⟩
  obtain ⟨hno, hval⟩ := hexc hq hq_le hp hr hχ hneq
  have hlog2_le : Real.log 2 ≤ Real.log (Q + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogQ_le : Real.log Q ≤ Real.log (Q + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog_bound : Real.log (Q ^ A + 2) ≤ 2 * A * Real.log (Q + 2) := by
    have hpow2 : Q ^ A + 2 ≤ 2 * Q ^ A := by linarith
    calc
      Real.log (Q ^ A + 2) ≤ Real.log (2 * Q ^ A) := Real.log_le_log (by positivity) hpow2
      _ = Real.log 2 + Real.log (Q ^ A) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 2 + A * Real.log Q := by rw [Real.log_rpow (by linarith)]
      _ ≤ 1 * Real.log (Q + 2) + A * Real.log (Q + 2) :=
          add_le_add (by rw [one_mul]; exact hlog2_le)
            (mul_le_mul_of_nonneg_left hlogQ_le (by linarith))
      _ ≤ (A + A) * Real.log (Q + 2) := by
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right (add_le_add hA le_rfl) (Real.log_nonneg (by linarith))
      _ = 2 * A * Real.log (Q + 2) := by ring
  have hlog_pos : 0 < Real.log (Q ^ A + 2) := Real.log_pos (by linarith)
  refine ⟨fun σ hσ ↦ hno σ ⟨?_, hσ.2⟩, ?_⟩
  · have hdiv : c_P / 2 / (A * Real.log (Q + 2)) ≤ c_P / Real.log (Q ^ A + 2) := by
      calc
        c_P / 2 / (A * Real.log (Q + 2)) = c_P / (2 * A * Real.log (Q + 2)) := by ring
        _ ≤ c_P / Real.log (Q ^ A + 2) := div_le_div_of_nonneg_left hc_P.le hlog_pos hlog_bound
    exact (sub_le_sub_left hdiv 1).trans hσ.1
  · calc
      c₁ / 2 / (A * Real.log (Q + 2)) = c₁ / (2 * A * Real.log (Q + 2)) := by ring
      _ ≤ c₁ / Real.log (Q ^ A + 2) := div_le_div_of_nonneg_left hc₁.le hlog_pos hlog_bound
      _ ≤ (DirichletCharacter.LFunction χ 1).re := hval

end PageTheorem

section SiegelTheorem

private lemma isReal_mul_local {q : ℕ} {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) : IsReal (ψ₁ * ψ₂) := by
  intro x
  change (ψ₁ x * ψ₂ x).im = 0
  rw [Complex.mul_im, hr₁ x, hr₂ x, mul_zero, zero_mul, add_zero]

private noncomputable def realCharArith {q : ℕ} (ψ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (ψ n).re, by simp⟩

private lemma realCharArith_isMultiplicative {q : ℕ} {ψ : DirichletCharacter ℂ q}
    (hr : IsReal ψ) : (realCharArith ψ).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [realCharArith]
  · intro m n _
    rcases eq_or_ne m 0 with rfl | hm
    · simp [realCharArith]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [realCharArith]
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    simp only [realCharArith, ArithmeticFunction.coe_mk, hmn, hm, hn, ↓reduceIte,
      Nat.cast_mul, map_mul]
    rw [Complex.mul_re, hr (m : ZMod q), hr (n : ZMod q), mul_zero, sub_zero]

private lemma realCharArith_prime_pow {q : ℕ} {ψ : DirichletCharacter ℂ q}
    (hr : IsReal ψ) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    realCharArith ψ (p ^ k) = (ψ p).re ^ k := by
  induction k with
  | zero => simp [realCharArith]
  | succ k ih =>
      have hpk1 : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp
      have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp
      have ih' : (ψ ((p ^ k : ℕ) : ZMod q)).re = (ψ p).re ^ k := by
        simpa only [realCharArith, ArithmeticFunction.coe_mk, hpk, ↓reduceIte] using ih
      simp only [realCharArith, ArithmeticFunction.coe_mk, hpk1, ↓reduceIte]
      rw [pow_succ, Nat.cast_mul, map_mul, Complex.mul_re, hr ((p ^ k : ℕ) : ZMod q),
        hr (p : ZMod q), mul_zero, sub_zero, ih', ← pow_succ]

private lemma realCharArith_quad_val {q : ℕ} {ψ : DirichletCharacter ℂ q}
    (hr : IsReal ψ) (p : ℕ) :
    (ψ p).re = 0 ∨ (ψ p).re = 1 ∨ (ψ p).re = -1 := by
  have hsq : ψ ^ 2 = 1 := (isReal_iff_sq_eq_one ψ).mp hr
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq p with h | h | h
  · left; simpa using congrArg Complex.re h
  · right; left; simpa using congrArg Complex.re h
  · right; right; simpa using congrArg Complex.re h

private lemma arith_mul_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ f a * g b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.pow_div hik hp.pos]

private lemma geom_neg_one_sum_eq (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i = if Even n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hn : Even n
      · have hodd : Odd (n + 1) := hn.add_one
        have hnot : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr hodd
        simp [hn, hnot, hodd.neg_one_pow]
      · have hev : Even (n + 1) := (Nat.not_even_iff_odd.mp hn).add_one
        simp [hn, hev, hev.neg_one_pow]

private lemma geom_neg_one_sum_nonneg (n : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i := by
  rw [geom_neg_one_sum_eq]
  split_ifs <;> norm_num

private lemma mul_geom_neg_one_sum_nonneg (y : ℝ) (n : ℕ) :
    0 ≤ y ^ n * ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i := by
  rw [geom_neg_one_sum_eq]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := hn
    rw [mul_one, ← two_mul, pow_mul]
    exact pow_nonneg (sq_nonneg y) m
  · simp

private lemma geom_quad_sum_nonneg {y : ℝ} (hy : y = 0 ∨ y = 1 ∨ y = -1) (n : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), y ^ i := by
  rcases hy with rfl | rfl | rfl
  · exact Finset.sum_nonneg fun i _ ↦ pow_nonneg le_rfl i
  · exact Finset.sum_nonneg fun i _ ↦ pow_nonneg zero_le_one i
  · exact geom_neg_one_sum_nonneg n

private noncomputable def fourFoldMulR {q : ℕ} (ψ₁ ψ₂ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realCharArith ψ₁) *
    (realCharArith ψ₂ * realCharArith (ψ₁ * ψ₂))

private lemma fourFoldMulR_isMultiplicative {q : ℕ} {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) :
    (fourFoldMulR ψ₁ ψ₂).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      (realCharArith_isMultiplicative hr₁)).mul
    ((realCharArith_isMultiplicative hr₂).mul
      (realCharArith_isMultiplicative (isReal_mul_local hr₁ hr₂)))

private lemma fourFoldMulR_prime_pow_nonneg {q : ℕ} {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ fourFoldMulR ψ₁ ψ₂ (p ^ k) := by
  have hx := realCharArith_quad_val hr₁ p
  have hy := realCharArith_quad_val hr₂ p
  have hr₁₂ : IsReal (ψ₁ * ψ₂) := isReal_mul_local hr₁ hr₂
  have hprod_re : ((ψ₁ * ψ₂) p).re = (ψ₁ p).re * (ψ₂ p).re := by
    change (ψ₁ (p : ZMod q) * ψ₂ (p : ZMod q)).re = _
    rw [Complex.mul_re, hr₁ (p : ZMod q), hr₂ (p : ZMod q), mul_zero, sub_zero]
  have hz_pk : ∀ t : ℕ, (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (p ^ t) = 1 :=
    fun t ↦ by
      simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        pow_ne_zero t hp.ne_zero, ↓reduceIte, Nat.cast_one]
  have h1_pk : ∀ t : ℕ, realCharArith ψ₁ (p ^ t) = (ψ₁ p).re ^ t :=
    fun t ↦ realCharArith_prime_pow hr₁ hp.ne_zero t
  have h2_pk : ∀ t : ℕ, realCharArith ψ₂ (p ^ t) = (ψ₂ p).re ^ t :=
    fun t ↦ realCharArith_prime_pow hr₂ hp.ne_zero t
  have h12_pk : ∀ t : ℕ, realCharArith (ψ₁ * ψ₂) (p ^ t) = ((ψ₁ p).re * (ψ₂ p).re) ^ t :=
    fun t ↦ by rw [realCharArith_prime_pow hr₁₂ hp.ne_zero t, hprod_re]
  rcases hx with hx0 | hx1 | hxm1
  · dsimp only [fourFoldMulR]
    rw [arith_mul_prime_pow _ _ hp k]
    have hA_eq : ∀ i : ℕ,
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realCharArith ψ₁) (p ^ i) = 1 := by
      intro i
      rw [arith_mul_prime_pow _ _ hp i]
      have hterm : ∀ t ∈ Finset.range (i + 1),
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (p ^ t) *
            realCharArith ψ₁ (p ^ (i - t)) = (0 : ℝ) ^ (i - t) := by
        intro t _
        rw [hz_pk t, h1_pk (i - t), hx0, one_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single i]
      · simp
      · intro t ht hti
        have hlt : 0 < i - t := by
          have := Finset.mem_range.mp ht
          omega
        exact zero_pow hlt.ne'
      · intro hi_mem
        exact False.elim (hi_mem (Finset.mem_range.mpr (Nat.lt_succ_self i)))
    have hB_eq : ∀ j : ℕ,
        (realCharArith ψ₂ * realCharArith (ψ₁ * ψ₂)) (p ^ j) = (ψ₂ p).re ^ j := by
      intro j
      rw [arith_mul_prime_pow _ _ hp j]
      have hterm : ∀ b ∈ Finset.range (j + 1),
          realCharArith ψ₂ (p ^ b) * realCharArith (ψ₁ * ψ₂) (p ^ (j - b)) =
            (ψ₂ p).re ^ b * (0 : ℝ) ^ (j - b) := by
        intro b _
        rw [h2_pk b, h12_pk (j - b), hx0, zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single j]
      · simp
      · intro b hb hbj
        have hlt : 0 < j - b := by
          have := Finset.mem_range.mp hb
          omega
        simp [zero_pow hlt.ne']
      · intro hj_mem
        exact False.elim (hj_mem (Finset.mem_range.mpr (Nat.lt_succ_self j)))
    have hsum_eq : ∑ i ∈ Finset.range (k + 1),
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realCharArith ψ₁) (p ^ i) *
          (realCharArith ψ₂ * realCharArith (ψ₁ * ψ₂)) (p ^ (k - i)) =
        ∑ i ∈ Finset.range (k + 1), (ψ₂ p).re ^ (k - i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hA_eq i, hB_eq (k - i), one_mul]
    rw [hsum_eq]
    have hrefl := Finset.sum_range_reflect (fun i ↦ (ψ₂ p).re ^ i) (k + 1)
    simp only [Nat.add_sub_cancel_right] at hrefl
    rw [hrefl]
    exact geom_quad_sum_nonneg hy k
  · have hcomm : fourFoldMulR ψ₁ ψ₂ =
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realCharArith ψ₂) *
          (realCharArith ψ₁ * realCharArith (ψ₁ * ψ₂)) := by
      dsimp only [fourFoldMulR]
      ring
    rw [hcomm, arith_mul_prime_pow _ _ hp k]
    refine Finset.sum_nonneg fun i hi ↦ mul_nonneg ?_ ?_
    · rw [arith_mul_prime_pow _ _ hp i]
      have hterm : ∀ t ∈ Finset.range (i + 1),
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (p ^ t) *
            realCharArith ψ₂ (p ^ (i - t)) = (ψ₂ p).re ^ (i - t) := by
        intro t _
        rw [hz_pk t, h2_pk (i - t), one_mul]
      rw [Finset.sum_congr rfl hterm]
      have hrefl := Finset.sum_range_reflect (fun t ↦ (ψ₂ p).re ^ t) (i + 1)
      simp only [Nat.add_sub_cancel_right] at hrefl
      rw [hrefl]
      exact geom_quad_sum_nonneg hy i
    · rw [arith_mul_prime_pow _ _ hp (k - i)]
      have hterm : ∀ b ∈ Finset.range (k - i + 1),
          realCharArith ψ₁ (p ^ b) * realCharArith (ψ₁ * ψ₂) (p ^ (k - i - b)) =
            (ψ₂ p).re ^ (k - i - b) := by
        intro b _
        rw [h1_pk b, h12_pk (k - i - b), hx1, one_pow, one_mul, one_mul]
      rw [Finset.sum_congr rfl hterm]
      have hrefl := Finset.sum_range_reflect (fun b ↦ (ψ₂ p).re ^ b) (k - i + 1)
      simp only [Nat.add_sub_cancel_right] at hrefl
      rw [hrefl]
      exact geom_quad_sum_nonneg hy (k - i)
  · dsimp only [fourFoldMulR]
    rw [arith_mul_prime_pow _ _ hp k]
    refine Finset.sum_nonneg fun i hi ↦ mul_nonneg ?_ ?_
    · rw [arith_mul_prime_pow _ _ hp i]
      have hterm : ∀ t ∈ Finset.range (i + 1),
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (p ^ t) *
            realCharArith ψ₁ (p ^ (i - t)) = (-1 : ℝ) ^ (i - t) := by
        intro t _
        rw [hz_pk t, h1_pk (i - t), hxm1, one_mul]
      rw [Finset.sum_congr rfl hterm]
      have hrefl := Finset.sum_range_reflect (fun t ↦ (-1 : ℝ) ^ t) (i + 1)
      simp only [Nat.add_sub_cancel_right] at hrefl
      rw [hrefl]
      exact geom_neg_one_sum_nonneg i
    · rw [arith_mul_prime_pow _ _ hp (k - i)]
      have hterm : ∀ b ∈ Finset.range (k - i + 1),
          realCharArith ψ₂ (p ^ b) * realCharArith (ψ₁ * ψ₂) (p ^ (k - i - b)) =
            (ψ₂ p).re ^ (k - i) * (-1 : ℝ) ^ (k - i - b) := by
        intro b hb
        have hble : b ≤ k - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        rw [h2_pk b, h12_pk (k - i - b), hxm1, mul_pow, ← mul_assoc, mul_comm ((ψ₂ p).re ^ b),
          mul_assoc, ← pow_add, show b + (k - i - b) = k - i by omega, mul_comm]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hrefl := Finset.sum_range_reflect (fun b ↦ (-1 : ℝ) ^ b) (k - i + 1)
      simp only [Nat.add_sub_cancel_right] at hrefl
      rw [hrefl]
      exact mul_geom_neg_one_sum_nonneg (ψ₂ p).re (k - i)

private lemma fourFoldMulR_nonneg {q : ℕ} {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) (n : ℕ) :
    0 ≤ fourFoldMulR ψ₁ ψ₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization (fourFoldMulR ψ₁ ψ₂)
    (fourFoldMulR_isMultiplicative hr₁ hr₂) hn, Finsupp.prod, Nat.support_factorization]
  exact Finset.prod_nonneg fun p hp ↦
    fourFoldMulR_prime_pow_nonneg hr₁ hr₂ (Nat.prime_of_mem_primeFactors hp) _

private noncomputable def fourFoldMulC {q : ℕ} (ψ₁ ψ₂ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  fun n ↦ (fourFoldMulR ψ₁ ψ₂ n : ℂ)

private lemma fourFoldMulC_nonneg_real {q : ℕ} {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) (n : ℕ) :
    0 ≤ (fourFoldMulC ψ₁ ψ₂ n).re ∧ (fourFoldMulC ψ₁ ψ₂ n).im = 0 :=
  ⟨by simpa [fourFoldMulC] using fourFoldMulR_nonneg hr₁ hr₂ n, by simp [fourFoldMulC]⟩

private lemma fourFoldMulC_one {q : ℕ} {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) :
    fourFoldMulC ψ₁ ψ₂ 1 = 1 := by
  simp [fourFoldMulC, (fourFoldMulR_isMultiplicative hr₁ hr₂).map_one]

private lemma toC_mul_eq (f g : ArithmeticFunction ℝ) :
    (fun n ↦ ((f * g) n : ℂ)) = LSeries.convolution (fun n ↦ (f n : ℂ)) (fun n ↦ (g n : ℂ)) := by
  ext n
  simp [ArithmeticFunction.mul_apply, LSeries.convolution_def]

private lemma LSeriesSummable_toC_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℂ)) s := by
  refine (LSeriesSummable_congr s fun {n} hn ↦ ?_).mpr (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn, ↓reduceIte,
    Nat.cast_one, Complex.ofReal_one]

private lemma LSeriesSummable_toC_realCharArith {q : ℕ} (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (realCharArith ψ n : ℂ)) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ ?_) hs
  by_cases hn : n = 0
  · simp [realCharArith, hn]
  · simp only [realCharArith, ArithmeticFunction.coe_mk, hn, ↓reduceIte, Complex.norm_real,
      Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (norm_char_le_one ψ (n : ZMod q))

private lemma fourFoldMulC_summable {q : ℕ} (ψ₁ ψ₂ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fourFoldMulC ψ₁ ψ₂) s := by
  unfold fourFoldMulC fourFoldMulR
  rw [toC_mul_eq, toC_mul_eq, toC_mul_eq]
  exact ((LSeriesSummable_toC_zeta hs).convolution (LSeriesSummable_toC_realCharArith ψ₁ hs)).convolution
    ((LSeriesSummable_toC_realCharArith ψ₂ hs).convolution
      (LSeriesSummable_toC_realCharArith (ψ₁ * ψ₂) hs))

private lemma fourFoldMulC_abscissa {q : ℕ} (ψ₁ ψ₂ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (fourFoldMulC ψ₁ ψ₂) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    fourFoldMulC_summable ψ₁ ψ₂ (by simpa using hy)

private lemma fourFoldMulC_LSeries_eq {q : ℕ} [NeZero q] {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hr₁ : IsReal ψ₁) (hr₂ : IsReal ψ₂) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s *
      (DirichletCharacter.LFunction ψ₁ s * DirichletCharacter.LFunction ψ₂ s *
        DirichletCharacter.LFunction (ψ₁ * ψ₂) s) =
      LSeries (fourFoldMulC ψ₁ ψ₂) s := by
  have hr₁₂ : IsReal (ψ₁ * ψ₂) := isReal_mul_local hr₁ hr₂
  have hz_eq : LSeries (fun n ↦ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℂ)) s =
      riemannZeta s := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    exact LSeries_congr (fun {n} hn ↦ by
      simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn, ↓reduceIte,
        Nat.cast_one, Complex.ofReal_one]) s
  have hchar_eq : ∀ (ψ : DirichletCharacter ℂ q), IsReal ψ →
      LSeries (fun n ↦ (realCharArith ψ n : ℂ)) s = DirichletCharacter.LFunction ψ s := by
    intro ψ hrψ
    rw [DirichletCharacter.LFunction_eq_LSeries ψ hs]
    refine LSeries_congr (fun {n} hn ↦ ?_) s
    simp only [realCharArith, ArithmeticFunction.coe_mk, hn, ↓reduceIte]
    exact Complex.ext rfl (hrψ (n : ZMod q)).symm
  have hs0 := LSeriesSummable_toC_zeta hs
  have hs1 := LSeriesSummable_toC_realCharArith ψ₁ hs
  have hs2 := LSeriesSummable_toC_realCharArith ψ₂ hs
  have hs12 := LSeriesSummable_toC_realCharArith (ψ₁ * ψ₂) hs
  unfold fourFoldMulC fourFoldMulR
  rw [toC_mul_eq, toC_mul_eq, toC_mul_eq,
    LSeries_convolution' (hs0.convolution hs1) (hs2.convolution hs12),
    LSeries_convolution' hs0 hs1, LSeries_convolution' hs2 hs12,
    hz_eq, hchar_eq ψ₁ hr₁, hchar_eq ψ₂ hr₂, hchar_eq (ψ₁ * ψ₂) hr₁₂]
  ring

private lemma harmonic_sum_le_one_add_log (q : ℕ) (hq : 1 ≤ q) :
    ∑ m ∈ Finset.Icc 1 q, (m : ℝ)⁻¹ ≤ 1 + Real.log (q : ℝ) := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
      rw [hsplit, Finset.sum_insert hnot]
      have hstep : ((k + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
        have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
        have hk1_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
        have hexp := Real.add_one_le_exp (-((k + 1 : ℕ) : ℝ)⁻¹)
        have hratio : (k : ℝ) / ((k + 1 : ℕ) : ℝ) = -((k + 1 : ℕ) : ℝ)⁻¹ + 1 := by
          push_cast
          field_simp [hk1_pos.ne']
          ring
        rw [← hratio] at hexp
        have hlog := Real.log_le_log (div_pos hk_pos (by exact_mod_cast hk1_pos)) hexp
        rw [Real.log_div hk_pos.ne' (by positivity), Real.log_exp] at hlog
        linarith
      linarith

private lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime) :
    ∀ {t : Finset ℕ}, p ∣ ∏ r ∈ t, r → ∃ r ∈ t, p ∣ r := by
  intro t
  induction t using Finset.induction_on with
  | empty =>
      simp [hp.not_dvd_one]
  | insert a s has ih =>
      rw [Finset.prod_insert has]
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with ha | hs
      · exact ⟨a, Finset.mem_insert_self a s, ha⟩
      · obtain ⟨r, hr, hpr⟩ := ih hs
        exact ⟨r, Finset.mem_insert_of_mem hr, hpr⟩

private lemma prod_primeFactors_one_add_inv_le (q : ℕ) (hq : 1 ≤ q) :
    ∏ p ∈ q.primeFactors, (1 + (p : ℝ)⁻¹) ≤ 1 + Real.log (q : ℝ) := by
  rw [Finset.prod_one_add]
  let g : Finset ℕ → ℕ := fun t ↦ ∏ p ∈ t, p
  have hval : ∀ t ∈ q.primeFactors.powerset, ∏ p ∈ t, (p : ℝ)⁻¹ = ((g t : ℕ) : ℝ)⁻¹ := by
    intro t _
    rw [Finset.prod_inv_distrib, Nat.cast_prod]
  have hmem : ∀ t ∈ q.primeFactors.powerset, g t ∈ Finset.Icc 1 q := by
    intro t ht
    have hsub : t ⊆ q.primeFactors := Finset.mem_powerset.mp ht
    have hdvd_pf : g t ∣ ∏ p ∈ q.primeFactors, p :=
      Finset.prod_dvd_prod_of_subset _ _ id hsub
    have hdvd : g t ∣ q := hdvd_pf.trans (Nat.prod_primeFactors_dvd q)
    have hpos : 0 < q := hq
    have hg_pos : 0 < g t := Nat.pos_of_dvd_of_pos hdvd hpos
    exact Finset.mem_Icc.mpr ⟨hg_pos, Nat.le_of_dvd hpos hdvd⟩
  have hinj : Set.InjOn g (q.primeFactors.powerset : Set (Finset ℕ)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hs₁ := Finset.mem_powerset.mp ht₁
    have hs₂ := Finset.mem_powerset.mp ht₂
    ext p
    constructor
    · intro hp₁
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (hs₁ hp₁)
      have hdvd : p ∣ g t₂ := by rw [← heq]; exact Finset.dvd_prod_of_mem _ hp₁
      obtain ⟨r, hr₂, hpr⟩ := prime_dvd_finset_prod hp hdvd
      have hr : r.Prime := Nat.prime_of_mem_primeFactors (hs₂ hr₂)
      rwa [(Nat.prime_dvd_prime_iff_eq hp hr).mp hpr]
    · intro hp₂
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (hs₂ hp₂)
      have hdvd : p ∣ g t₁ := by rw [heq]; exact Finset.dvd_prod_of_mem _ hp₂
      obtain ⟨r, hr₁, hpr⟩ := prime_dvd_finset_prod hp hdvd
      have hr : r.Prime := Nat.prime_of_mem_primeFactors (hs₁ hr₁)
      rwa [(Nat.prime_dvd_prime_iff_eq hp hr).mp hpr]
  calc
    ∑ t ∈ q.primeFactors.powerset, ∏ p ∈ t, (p : ℝ)⁻¹
      = ∑ t ∈ q.primeFactors.powerset, ((g t : ℕ) : ℝ)⁻¹ := Finset.sum_congr rfl hval
    _ = ∑ m ∈ q.primeFactors.powerset.image g, (m : ℝ)⁻¹ :=
        (Finset.sum_image (f := fun m : ℕ ↦ (m : ℝ)⁻¹)
          (fun t₁ ht₁ t₂ ht₂ h ↦ hinj ht₁ ht₂ h)).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 q, (m : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hmem) (fun _ _ _ ↦ by positivity)
    _ ≤ 1 + Real.log (q : ℝ) := harmonic_sum_le_one_add_log q hq

private lemma telescoping_inv_diff (q : ℕ) (hq : 1 ≤ q) :
    ∑ m ∈ Finset.Ico 2 (q + 1), (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) = 1 - (q : ℝ)⁻¹ := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ k + 1), ih]
      push_cast
      ring

private lemma prod_primeFactors_one_add_sq_inv_le (q : ℕ) (hq : 1 ≤ q) :
    ∏ p ∈ q.primeFactors, (1 + ((p : ℝ) ^ 2 - 1)⁻¹) ≤ Real.exp 1 := by
  have h1 : ∏ p ∈ q.primeFactors, (1 + ((p : ℝ) ^ 2 - 1)⁻¹) ≤
      ∏ p ∈ q.primeFactors, Real.exp (((p : ℝ) ^ 2 - 1)⁻¹) := by
    refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) (fun p _ ↦ ?_)
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    · linarith [Real.add_one_le_exp (((p : ℝ) ^ 2 - 1)⁻¹)]
  rw [← Real.exp_sum] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have hterm : ∀ p ∈ q.primeFactors, ((p : ℝ) ^ 2 - 1)⁻¹ ≤ ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hmul : ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ = ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
      field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
      ring
    rw [hmul]
    exact inv_anti₀ (by nlinarith) (by nlinarith)
  have hsub : q.primeFactors ⊆ Finset.Ico 2 (q + 1) := by
    intro p hp
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    exact Finset.mem_Ico.mpr ⟨hp_pr.two_le, Nat.lt_succ_of_le (Nat.le_of_dvd hq hdvd)⟩
  have hnonneg : ∀ m ∈ Finset.Ico 2 (q + 1), (0 : ℝ) ≤ ((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹ := by
    intro m hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.mp hm).1
    have : (m : ℝ) - 1 ≤ m := by linarith
    exact sub_nonneg.mpr (inv_anti₀ (by linarith) this)
  have htel := telescoping_inv_diff q hq
  calc
    ∑ p ∈ q.primeFactors, ((p : ℝ) ^ 2 - 1)⁻¹
      ≤ ∑ p ∈ q.primeFactors, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ Finset.Ico 2 (q + 1), (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ ↦ hnonneg m hm)
    _ = 1 - (q : ℝ)⁻¹ := htel
    _ ≤ 1 := by linarith [show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity]

private lemma euler_factor_prod_lower_bound {q : ℕ} (hq : 1 ≤ q) :
    1 / (Real.exp 1 * (1 + Real.log (q : ℝ))) ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hfac_pos : ∀ p ∈ q.primeFactors, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) hp2).trans_eq (by norm_num)
    linarith
  have hprod_pos : 0 < ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos hfac_pos
  have hinv_eq : ∀ p ∈ q.primeFactors,
      (1 - (p : ℝ)⁻¹)⁻¹ = (1 + (p : ℝ)⁻¹) * (1 + ((p : ℝ) ^ 2 - 1)⁻¹) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2_ne : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h1p : 1 - (p : ℝ)⁻¹ ≠ 0 := (hfac_pos p hp).ne'
    field_simp [hp0, hp1, hp2_ne, h1p]
    ring
  have hinv_bd : (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ ≤
      Real.exp 1 * (1 + Real.log (q : ℝ)) := by
    rw [← Finset.prod_inv_distrib, Finset.prod_congr rfl hinv_eq, Finset.prod_mul_distrib]
    calc
      (∏ p ∈ q.primeFactors, (1 + (p : ℝ)⁻¹)) *
          (∏ p ∈ q.primeFactors, (1 + ((p : ℝ) ^ 2 - 1)⁻¹))
        ≤ (1 + Real.log (q : ℝ)) * Real.exp 1 :=
          mul_le_mul (prod_primeFactors_one_add_inv_le q hq)
            (prod_primeFactors_one_add_sq_inv_le q hq)
            (Finset.prod_nonneg fun p hp ↦ by
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
              have : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
              positivity)
            (by positivity)
      _ = Real.exp 1 * (1 + Real.log (q : ℝ)) := by ring
  rw [one_div]
  have hinv2 := inv_anti₀ (inv_pos.mpr hprod_pos) hinv_bd
  rwa [inv_inv] at hinv2

private lemma log_add_two_le_rpow {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr : 0 < r) :
    Real.log ((q : ℝ) + 2) ≤ (2 / r) * (q : ℝ) ^ r := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < q := by linarith
  have hle : (q : ℝ) + 2 ≤ (q : ℝ) ^ 2 := by nlinarith
  have hlog_sq : Real.log ((q : ℝ) + 2) ≤ 2 * Real.log (q : ℝ) := by
    calc
      Real.log ((q : ℝ) + 2) ≤ Real.log ((q : ℝ) ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (q : ℝ) := by rw [Real.log_pow]; ring
  have hlog_rpow : r * Real.log (q : ℝ) ≤ (q : ℝ) ^ r := by
    rw [← Real.log_rpow hq_pos]
    linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq_pos r)]
  have hlog_q : Real.log (q : ℝ) ≤ (1 / r) * (q : ℝ) ^ r := by
    calc
      Real.log (q : ℝ) = (1 / r) * (r * Real.log (q : ℝ)) := by field_simp [hr.ne']
      _ ≤ (1 / r) * (q : ℝ) ^ r := mul_le_mul_of_nonneg_left hlog_rpow (by positivity)
  calc
    Real.log ((q : ℝ) + 2) ≤ 2 * Real.log (q : ℝ) := hlog_sq
    _ ≤ 2 * ((1 / r) * (q : ℝ) ^ r) := mul_le_mul_of_nonneg_left hlog_q (by norm_num)
    _ = (2 / r) * (q : ℝ) ^ r := by ring

private lemma log_mul_add_two_le_rpow {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    {r : ℝ} (hr : 0 < r) :
    Real.log ((q₁ : ℝ) * q₂ + 2) ≤ (Real.log ((q₂ : ℝ) + 2) + 1 / r) * (q₁ : ℝ) ^ r := by
  have hq₁_pos : (0 : ℝ) < q₁ := by exact_mod_cast (by omega : 0 < q₁)
  have hq₂_pos : (0 : ℝ) < q₂ := by exact_mod_cast (by omega : 0 < q₂)
  have hq₁_ge1 : (1 : ℝ) ≤ q₁ := by exact_mod_cast (by omega : 1 ≤ q₁)
  have hmul : (q₁ : ℝ) * q₂ + 2 ≤ (q₁ : ℝ) * ((q₂ : ℝ) + 2) := by
    have : (2 : ℝ) ≤ 2 * (q₁ : ℝ) := by linarith
    nlinarith
  have hlog_rpow : Real.log (q₁ : ℝ) ≤ (1 / r) * (q₁ : ℝ) ^ r := by
    have h0 : r * Real.log (q₁ : ℝ) ≤ (q₁ : ℝ) ^ r := by
      rw [← Real.log_rpow hq₁_pos]
      linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq₁_pos r)]
    calc
      Real.log (q₁ : ℝ) = (1 / r) * (r * Real.log (q₁ : ℝ)) := by field_simp [hr.ne']
      _ ≤ (1 / r) * (q₁ : ℝ) ^ r := mul_le_mul_of_nonneg_left h0 (by positivity)
  have hpow_ge1 : (1 : ℝ) ≤ (q₁ : ℝ) ^ r := Real.one_le_rpow hq₁_ge1 hr.le
  calc
    Real.log ((q₁ : ℝ) * q₂ + 2) ≤ Real.log ((q₁ : ℝ) * ((q₂ : ℝ) + 2)) :=
        Real.log_le_log (by positivity) hmul
    _ = Real.log (q₁ : ℝ) + Real.log ((q₂ : ℝ) + 2) :=
        Real.log_mul hq₁_pos.ne' (by positivity)
    _ ≤ (1 / r) * (q₁ : ℝ) ^ r + Real.log ((q₂ : ℝ) + 2) * (q₁ : ℝ) ^ r := by
        refine add_le_add hlog_rpow ?_
        have hln : 0 ≤ Real.log ((q₂ : ℝ) + 2) := Real.log_nonneg (by linarith)
        exact le_mul_of_one_le_right hln hpow_ge1
    _ = (Real.log ((q₂ : ℝ) + 2) + 1 / r) * (q₁ : ℝ) ^ r := by ring

private lemma changeLevel_euler_factor_norm_le {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) :
    ‖∏ p ∈ (q₁ * q₂).primeFactors, (1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤
      (2 : ℝ) ^ q₂.primeFactors.card := by
  rw [norm_prod]
  let f : ℕ → ℝ := fun p ↦ if p ∈ q₂.primeFactors then 2 else 1
  have hle : ∀ p ∈ (q₁ * q₂).primeFactors,
      ‖1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ f p := by
    intro p hp
    have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp
    by_cases hp1 : p ∣ q₁
    · have hnu : ¬ IsUnit (p : ZMod q₁) := by
        rw [ZMod.isUnit_iff_coprime]
        exact hp_pr.dvd_iff_not_coprime.mp hp1
      rw [MulChar.map_nonunit _ hnu, zero_mul, sub_zero, norm_one]
      dsimp only [f]
      split_ifs <;> norm_num
    · have hpq12 : p ∣ q₁ * q₂ := Nat.dvd_of_mem_primeFactors hp
      have hp2 : p ∣ q₂ := (hp_pr.dvd_mul.mp hpq12).resolve_left hp1
      have hp2_mem : p ∈ q₂.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_pr, hp2, NeZero.ne q₂⟩
      have hpinv : ‖(p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 := by
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
        have hp_ge1 : (1 : ℝ) ≤ p := by exact_mod_cast hp_pr.one_le
        exact inv_le_one_of_one_le₀ hp_ge1
      have hbd : ‖1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 2 := by
        calc
          ‖1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ))‖
            ≤ ‖(1 : ℂ)‖ + ‖χ₁ p * (p : ℂ) ^ (-(1 : ℂ))‖ := norm_sub_le _ _
          _ = 1 + ‖χ₁ p‖ * ‖(p : ℂ) ^ (-(1 : ℂ))‖ := by rw [norm_one, norm_mul]
          _ ≤ 1 + 1 * 1 := add_le_add le_rfl (mul_le_mul (norm_char_le_one χ₁ _) hpinv
              (norm_nonneg _) zero_le_one)
          _ = 2 := by norm_num
      simpa only [f, hp2_mem, ↓reduceIte] using hbd
  have hsplit := (Finset.prod_filter_mul_prod_filter_not (q₁ * q₂).primeFactors
    (fun p ↦ p ∈ q₂.primeFactors) f).symm
  have hnot : ∏ p ∈ (q₁ * q₂).primeFactors with p ∉ q₂.primeFactors, f p = 1 :=
    Finset.prod_eq_one fun p hp ↦ by simp only [f, (Finset.mem_filter.mp hp).2, ↓reduceIte]
  have hyes : ∏ p ∈ (q₁ * q₂).primeFactors with p ∈ q₂.primeFactors, f p =
      (2 : ℝ) ^ ((q₁ * q₂).primeFactors.filter (· ∈ q₂.primeFactors)).card := by
    have h2 : ∏ p ∈ (q₁ * q₂).primeFactors with p ∈ q₂.primeFactors, f p =
        ∏ _p ∈ (q₁ * q₂).primeFactors with _ ∈ q₂.primeFactors, (2 : ℝ) :=
      Finset.prod_congr rfl fun p hp ↦ by simp only [f, (Finset.mem_filter.mp hp).2, ↓reduceIte]
    rw [h2, Finset.prod_const]
  have hcard : ((q₁ * q₂).primeFactors.filter (· ∈ q₂.primeFactors)).card ≤ q₂.primeFactors.card :=
    Finset.card_le_card fun p hp ↦ (Finset.mem_filter.mp hp).2
  calc
    ∏ p ∈ (q₁ * q₂).primeFactors, ‖1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ))‖
      ≤ ∏ p ∈ (q₁ * q₂).primeFactors, f p := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) hle
    _ = (2 : ℝ) ^ ((q₁ * q₂).primeFactors.filter (· ∈ q₂.primeFactors)).card * 1 := by
        rw [hsplit, hnot, hyes]
    _ = (2 : ℝ) ^ ((q₁ * q₂).primeFactors.filter (· ∈ q₂.primeFactors)).card := mul_one _
    _ ≤ (2 : ℝ) ^ q₂.primeFactors.card := pow_le_pow_right₀ (by norm_num) hcard

private lemma siegel_distinct_zero_case_bound {ε : ℝ} (hε : 0 < ε)
    {q₂ : ℕ} [NeZero q₂] (hq₂ : 2 ≤ q₂) {χ₂ : DirichletCharacter ℂ q₂}
    (hp₂ : χ₂.IsPrimitive) (hr₂ : IsReal χ₂) (hχ₂ : χ₂ ≠ 1)
    {β₂ : ℝ} (hβ₂_lo : 3 / 4 ≤ β₂) (hβ₂_lt : β₂ < 1)
    (hβ₂_zero : DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0) :
    let ε₁ : ℝ := min ε (1 / 4)
    let δ₁ : ℝ := min (1 / 4) (ε₁ * Real.log (6 / 5) / 16)
    1 - δ₁ ≤ β₂ →
    ∃ C > 0, ∀ {q₁ : ℕ} [NeZero q₁], 2 ≤ q₁ → ∀ {χ₁ : DirichletCharacter ℂ q₁},
      χ₁.IsPrimitive → IsReal χ₁ → χ₁ ≠ 1 →
      (⟨q₁, χ₁⟩ : Σ m : ℕ, DirichletCharacter ℂ m) ≠ ⟨q₂, χ₂⟩ →
      C * (q₁ : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction χ₁ 1).re := by
  intro ε₁ δ₁ hβ₂_ge
  obtain ⟨C_E, hC_E, hhalf⟩ := estermann_taylor_half_lower_bound
  have hε₁_pos : 0 < ε₁ := lt_min hε (by norm_num)
  have hlog65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hδ₁_pos : 0 < δ₁ := lt_min (by norm_num) (by positivity)
  have h1β₂_pos : 0 < 1 - β₂ := by linarith
  let B₀ : ℝ := (1000 : ℝ) ^ 3 * (q₂ : ℝ) ^ 6
  have hB₀_pos : 0 < B₀ := by positivity
  let K₂ : ℝ := 12 * (C_E * B₀ + 1)
  have hK₂_ge : 12 ≤ K₂ := by dsimp only [K₂]; nlinarith
  let M₂ : ℝ := Real.log K₂ / Real.log (6 / 5) + 2
  have hM₂_pos : 0 < M₂ := by
    have : 0 < Real.log K₂ := Real.log_pos (by linarith)
    positivity
  let C_log : ℝ := 2 * (Real.log ((q₂ : ℝ) + 2) + 4 / ε₁)
  have hC_log_pos : 0 < C_log := by
    have : 0 ≤ Real.log ((q₂ : ℝ) + 2) := Real.log_nonneg (by linarith [show (2 : ℝ) ≤ q₂ by exact_mod_cast hq₂])
    positivity
  let C_big : ℝ := (2 : ℝ) ^ q₂.primeFactors.card * C_log ^ 2 * Real.exp (M₂ * δ₁) / (1 - β₂)
  have hC_big_pos : 0 < C_big := by positivity
  refine ⟨1 / (2 * C_big), by positivity, fun {q₁} _ hq₁ {χ₁} hp₁ hr₁ hχ₁ hneq ↦ ?_⟩
  let q : ℕ := q₁ * q₂
  have : NeZero q := inferInstance
  let ψ₁ : DirichletCharacter ℂ q := DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁
  let ψ₂ : DirichletCharacter ℂ q := DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂
  obtain ⟨hψ₁, hψ₂, hψ₁₂⟩ := changeLevel_ne_one_of_distinct_primitive hp₁ hp₂ hr₁ hχ₁ hχ₂ hneq
  have hrψ₁ : IsReal ψ₁ := changeLevel_isReal (dvd_mul_right q₁ q₂) hr₁
  have hrψ₂ : IsReal ψ₂ := changeLevel_isReal (dvd_mul_left q₂ q₁) hr₂
  let F : ℂ → ℂ := fun s ↦ DirichletCharacter.LFunction ψ₁ s *
    DirichletCharacter.LFunction ψ₂ s * DirichletCharacter.LFunction (ψ₁ * ψ₂) s
  have hF_diff : Differentiable ℂ F :=
    ((DirichletCharacter.differentiable_LFunction hψ₁).mul
      (DirichletCharacter.differentiable_LFunction hψ₂)).mul
      (DirichletCharacter.differentiable_LFunction hψ₁₂)
  have hF_ball : ∀ z ∈ Metric.closedBall (2 : ℂ) (3 / 2 : ℝ), ‖F z‖ ≤ B₀ * (q₁ : ℝ) ^ 6 := by
    intro z hz
    have h1 := page_LFunction_ball_bound hψ₁ z hz
    have h2 := page_LFunction_ball_bound hψ₂ z hz
    have h12 := page_LFunction_ball_bound hψ₁₂ z hz
    dsimp only [F]
    rw [norm_mul, norm_mul]
    have hprod := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h12
      (norm_nonneg _) (by positivity)
    have heq : (1000 * (q : ℝ) ^ 2) * (1000 * (q : ℝ) ^ 2) * (1000 * (q : ℝ) ^ 2) =
        B₀ * (q₁ : ℝ) ^ 6 := by
      dsimp only [B₀, q]
      push_cast
      ring
    exact hprod.trans_eq heq
  have hF_zero : (riemannZeta (β₂ : ℂ) * F (β₂ : ℂ)).re ≤ 0 := by
    have hψ₂_zero : DirichletCharacter.LFunction ψ₂ (β₂ : ℂ) = 0 := by
      dsimp only [ψ₂]
      rw [LFunction_changeLevel_eq (dvd_mul_left q₂ q₁) χ₂ (Or.inl hχ₂), hβ₂_zero, zero_mul]
    have hFz : F (β₂ : ℂ) = 0 := by dsimp only [F]; rw [hψ₂_zero, mul_zero, zero_mul]
    rw [hFz, mul_zero, Complex.zero_re]
  obtain ⟨N, _, hN_le, hhalf_bd⟩ := hhalf F (fourFoldMulC ψ₁ ψ₂) (B₀ * (q₁ : ℝ) ^ 6)
    (by positivity) hF_diff hF_ball (fourFoldMulC_nonneg_real hrψ₁ hrψ₂)
    (fourFoldMulC_one hrψ₁ hrψ₂) (fourFoldMulC_abscissa ψ₁ ψ₂)
    (fun s hs ↦ fourFoldMulC_LSeries_eq hrψ₁ hrψ₂ hs) hβ₂_lo hβ₂_lt hF_zero
  have hq₁_ge2 : (2 : ℝ) ≤ q₁ := by exact_mod_cast hq₁
  have hq₁_ge1 : (1 : ℝ) ≤ q₁ := by linarith
  have hN_bound : (N : ℝ) ≤ M₂ + (6 / Real.log (6 / 5)) * Real.log (q₁ : ℝ) := by
    have h1_le : (1 : ℝ) ≤ (q₁ : ℝ) ^ 6 := by exact one_le_pow₀ hq₁_ge1
    have harg : 12 * (C_E * (B₀ * (q₁ : ℝ) ^ 6) + 1) ≤ K₂ * (q₁ : ℝ) ^ 6 := by
      dsimp only [K₂]
      nlinarith
    have hlog_arg : Real.log (12 * (C_E * (B₀ * (q₁ : ℝ) ^ 6) + 1)) ≤
        Real.log K₂ + 6 * Real.log (q₁ : ℝ) := by
      calc
        Real.log (12 * (C_E * (B₀ * (q₁ : ℝ) ^ 6) + 1))
          ≤ Real.log (K₂ * (q₁ : ℝ) ^ 6) := Real.log_le_log (by positivity) harg
        _ = Real.log K₂ + Real.log ((q₁ : ℝ) ^ 6) := Real.log_mul (by positivity) (by positivity)
        _ = Real.log K₂ + 6 * Real.log (q₁ : ℝ) := by rw [Real.log_pow]; ring
    calc
      (N : ℝ) ≤ Real.log (12 * (C_E * (B₀ * (q₁ : ℝ) ^ 6) + 1)) / Real.log (6 / 5) + 2 := hN_le
      _ ≤ (Real.log K₂ + 6 * Real.log (q₁ : ℝ)) / Real.log (6 / 5) + 2 := by
          gcongr
      _ = M₂ + (6 / Real.log (6 / 5)) * Real.log (q₁ : ℝ) := by dsimp only [M₂]; ring
  have hpow_bd : (2 - β₂) ^ N ≤ Real.exp (M₂ * δ₁) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁) := by
    have hadd : 2 - β₂ ≤ Real.exp δ₁ := by
      have : 2 - β₂ ≤ Real.exp (1 - β₂) := by linarith [Real.add_one_le_exp (1 - β₂)]
      exact this.trans (Real.exp_le_exp.mpr (by linarith))
    have hexp_mul : (N : ℝ) * δ₁ ≤ M₂ * δ₁ + (6 * δ₁ / Real.log (6 / 5)) * Real.log (q₁ : ℝ) := by
      calc
        (N : ℝ) * δ₁ ≤ (M₂ + (6 / Real.log (6 / 5)) * Real.log (q₁ : ℝ)) * δ₁ :=
            mul_le_mul_of_nonneg_right hN_bound hδ₁_pos.le
        _ = M₂ * δ₁ + (6 * δ₁ / Real.log (6 / 5)) * Real.log (q₁ : ℝ) := by ring
    have hcoeff_exp : 6 * δ₁ / Real.log (6 / 5) ≤ (3 / 8 : ℝ) * ε₁ := by
      have hδ₁_le : δ₁ ≤ ε₁ * Real.log (6 / 5) / 16 := min_le_right _ _
      calc
        6 * δ₁ / Real.log (6 / 5) ≤ 6 * (ε₁ * Real.log (6 / 5) / 16) / Real.log (6 / 5) := by
            gcongr
        _ = (3 / 8 : ℝ) * ε₁ := by field_simp [hlog65.ne']; ring
    calc
      (2 - β₂) ^ N ≤ (Real.exp δ₁) ^ N := pow_le_pow_left₀ (by linarith) hadd N
      _ = Real.exp ((N : ℝ) * δ₁) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (M₂ * δ₁ + (6 * δ₁ / Real.log (6 / 5)) * Real.log (q₁ : ℝ)) :=
          Real.exp_le_exp.mpr hexp_mul
      _ = Real.exp (M₂ * δ₁) * Real.exp ((6 * δ₁ / Real.log (6 / 5)) * Real.log (q₁ : ℝ)) :=
          Real.exp_add _ _
      _ = Real.exp (M₂ * δ₁) * (q₁ : ℝ) ^ (6 * δ₁ / Real.log (6 / 5)) := by
          rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < q₁), mul_comm (Real.log (q₁ : ℝ))]
      _ ≤ Real.exp (M₂ * δ₁) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq₁_ge1 hcoeff_exp)
            (Real.exp_pos _).le
  have hL1_pos : 0 < (DirichletCharacter.LFunction χ₁ 1).re := LFunction_one_pos_of_isReal hχ₁ hr₁
  have hL1_norm : ‖DirichletCharacter.LFunction χ₁ 1‖ = (DirichletCharacter.LFunction χ₁ 1).re := by
    have him : (DirichletCharacter.LFunction χ₁ 1).im = 0 := LFunction_real_im_zero hχ₁ hr₁ 1
    have hre_eq : DirichletCharacter.LFunction χ₁ 1 = ((DirichletCharacter.LFunction χ₁ 1).re : ℂ) :=
      Complex.ext rfl him
    rw [hre_eq, Complex.norm_real, Real.norm_of_nonneg hL1_pos.le, Complex.ofReal_re]
  have hψ₁_bd : ‖DirichletCharacter.LFunction ψ₁ 1‖ ≤
      (DirichletCharacter.LFunction χ₁ 1).re * (2 : ℝ) ^ q₂.primeFactors.card := by
    dsimp only [ψ₁]
    rw [LFunction_changeLevel_eq (dvd_mul_right q₁ q₂) χ₁ (Or.inl hχ₁), norm_mul, hL1_norm]
    exact mul_le_mul_of_nonneg_left (changeLevel_euler_factor_norm_le χ₁) hL1_pos.le
  have hψ₂_bd : ‖DirichletCharacter.LFunction ψ₂ 1‖ ≤ C_log * (q₁ : ℝ) ^ (ε₁ / 4) := by
    have hlog_bd := log_mul_add_two_le_rpow hq₁ hq₂ (by positivity : 0 < ε₁ / 4)
    have heq_r : 2 * (Real.log ((q₂ : ℝ) + 2) + 1 / (ε₁ / 4)) = C_log := by
      dsimp only [C_log]
      ring
    calc
      ‖DirichletCharacter.LFunction ψ₂ 1‖ ≤ 2 * Real.log ((q : ℝ) + 2) :=
          norm_LFunction_one_le hψ₂
      _ ≤ 2 * ((Real.log ((q₂ : ℝ) + 2) + 1 / (ε₁ / 4)) * (q₁ : ℝ) ^ (ε₁ / 4)) := by
          dsimp only [q]; push_cast; exact mul_le_mul_of_nonneg_left hlog_bd (by norm_num)
      _ = C_log * (q₁ : ℝ) ^ (ε₁ / 4) := by rw [← mul_assoc, heq_r]
  have hψ₁₂_bd : ‖DirichletCharacter.LFunction (ψ₁ * ψ₂) 1‖ ≤ C_log * (q₁ : ℝ) ^ (ε₁ / 4) := by
    have hlog_bd := log_mul_add_two_le_rpow hq₁ hq₂ (by positivity : 0 < ε₁ / 4)
    have heq_r : 2 * (Real.log ((q₂ : ℝ) + 2) + 1 / (ε₁ / 4)) = C_log := by
      dsimp only [C_log]
      ring
    calc
      ‖DirichletCharacter.LFunction (ψ₁ * ψ₂) 1‖ ≤ 2 * Real.log ((q : ℝ) + 2) :=
          norm_LFunction_one_le hψ₁₂
      _ ≤ 2 * ((Real.log ((q₂ : ℝ) + 2) + 1 / (ε₁ / 4)) * (q₁ : ℝ) ^ (ε₁ / 4)) := by
          dsimp only [q]; push_cast; exact mul_le_mul_of_nonneg_left hlog_bd (by norm_num)
      _ = C_log * (q₁ : ℝ) ^ (ε₁ / 4) := by rw [← mul_assoc, heq_r]
  have hF1_bd : (F 1).re ≤ (DirichletCharacter.LFunction χ₁ 1).re *
      ((2 : ℝ) ^ q₂.primeFactors.card * C_log ^ 2) * (q₁ : ℝ) ^ (ε₁ / 2) := by
    have hre : (F 1).re ≤ ‖F 1‖ := Complex.re_le_norm (F 1)
    have hnormF : ‖F 1‖ = ‖DirichletCharacter.LFunction ψ₁ 1‖ *
        ‖DirichletCharacter.LFunction ψ₂ 1‖ * ‖DirichletCharacter.LFunction (ψ₁ * ψ₂) 1‖ := by
      dsimp only [F]
      rw [norm_mul, norm_mul]
    have hpow_add : (q₁ : ℝ) ^ (ε₁ / 4) * (q₁ : ℝ) ^ (ε₁ / 4) = (q₁ : ℝ) ^ (ε₁ / 2) := by
      rw [← Real.rpow_add (by linarith)]
      ring_nf
    calc
      (F 1).re ≤ ‖F 1‖ := hre
      _ = ‖DirichletCharacter.LFunction ψ₁ 1‖ * ‖DirichletCharacter.LFunction ψ₂ 1‖ *
          ‖DirichletCharacter.LFunction (ψ₁ * ψ₂) 1‖ := hnormF
      _ ≤ ((DirichletCharacter.LFunction χ₁ 1).re * (2 : ℝ) ^ q₂.primeFactors.card) *
          (C_log * (q₁ : ℝ) ^ (ε₁ / 4)) * (C_log * (q₁ : ℝ) ^ (ε₁ / 4)) :=
          mul_le_mul (mul_le_mul hψ₁_bd hψ₂_bd (norm_nonneg _) (by positivity))
            hψ₁₂_bd (norm_nonneg _) (by positivity)
      _ = (DirichletCharacter.LFunction χ₁ 1).re *
          ((2 : ℝ) ^ q₂.primeFactors.card * C_log ^ 2) *
          ((q₁ : ℝ) ^ (ε₁ / 4) * (q₁ : ℝ) ^ (ε₁ / 4)) := by ring
      _ = (DirichletCharacter.LFunction χ₁ 1).re *
          ((2 : ℝ) ^ q₂.primeFactors.card * C_log ^ 2) * (q₁ : ℝ) ^ (ε₁ / 2) := by rw [hpow_add]
  have hmain_bd : 1 / 2 ≤ (DirichletCharacter.LFunction χ₁ 1).re * C_big * (q₁ : ℝ) ^ ε := by
    have hpow_comb : (q₁ : ℝ) ^ (ε₁ / 2) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁) ≤ (q₁ : ℝ) ^ ε := by
      rw [← Real.rpow_add (by linarith)]
      refine Real.rpow_le_rpow_of_exponent_le hq₁_ge1 ?_
      have : ε₁ ≤ ε := min_le_left _ _
      linarith
    have hF1_nn : 0 ≤ (DirichletCharacter.LFunction χ₁ 1).re *
        ((2 : ℝ) ^ q₂.primeFactors.card * C_log ^ 2) * (q₁ : ℝ) ^ (ε₁ / 2) := by positivity
    have hpow_div : (2 - β₂) ^ N / (1 - β₂) ≤
        (Real.exp (M₂ * δ₁) / (1 - β₂)) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁) := by
      calc
        (2 - β₂) ^ N / (1 - β₂) ≤ (Real.exp (M₂ * δ₁) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁)) / (1 - β₂) :=
            div_le_div_of_nonneg_right hpow_bd h1β₂_pos.le
        _ = (Real.exp (M₂ * δ₁) / (1 - β₂)) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁) := by ring
    have hF1_re_nn : 0 ≤ (F 1).re := by
      by_contra hneg
      push Not at hneg
      have hnonpos : (F 1).re * ((2 - β₂) ^ N / (1 - β₂)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le (div_nonneg (pow_nonneg (by linarith) _) h1β₂_pos.le)
      linarith
    calc
      1 / 2 ≤ (F 1).re * ((2 - β₂) ^ N / (1 - β₂)) := hhalf_bd
      _ ≤ ((DirichletCharacter.LFunction χ₁ 1).re *
            ((2 : ℝ) ^ q₂.primeFactors.card * C_log ^ 2) * (q₁ : ℝ) ^ (ε₁ / 2)) *
          ((Real.exp (M₂ * δ₁) / (1 - β₂)) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁)) :=
          mul_le_mul hF1_bd hpow_div (div_nonneg (pow_nonneg (by linarith) _) h1β₂_pos.le) hF1_nn
      _ = (DirichletCharacter.LFunction χ₁ 1).re * C_big *
          ((q₁ : ℝ) ^ (ε₁ / 2) * (q₁ : ℝ) ^ ((3 / 8 : ℝ) * ε₁)) := by
          dsimp only [C_big]
          ring
      _ ≤ (DirichletCharacter.LFunction χ₁ 1).re * C_big * (q₁ : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hpow_comb (by positivity)
  have hq_pow_pos : 0 < (q₁ : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith)]
  calc
    1 / (2 * C_big) * ((q₁ : ℝ) ^ ε)⁻¹ = (1 / 2) / (C_big * (q₁ : ℝ) ^ ε) := by
        field_simp [hC_big_pos.ne', hq_pow_pos.ne']
    _ ≤ ((DirichletCharacter.LFunction χ₁ 1).re * C_big * (q₁ : ℝ) ^ ε) / (C_big * (q₁ : ℝ) ^ ε) :=
        div_le_div_of_nonneg_right hmain_bd (by positivity)
    _ = (DirichletCharacter.LFunction χ₁ 1).re := by
        have hne : C_big * (q₁ : ℝ) ^ ε ≠ 0 := by positivity
        field_simp [hne]

/-- Siegel's theorem for primitive real characters: for every `ε > 0`, there exists an
ineffective constant `C > 0` (depending only on `ε`) such that for every primitive real
non-principal Dirichlet character `χ` modulo `q ≥ 2`, `C * (q : ℝ) ^ (-ε) ≤ (LFunction χ 1).re`. -/
theorem siegel_theorem_primitive (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q},
      χ.IsPrimitive → IsReal χ → χ ≠ 1 →
      C * (q : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨c_P, hc_P, hnozero⟩ := page_theorem_of_no_zero
  let ε₁ : ℝ := min ε (1 / 4)
  let δ₁ : ℝ := min (1 / 4) (ε₁ * Real.log (6 / 5) / 16)
  have hε₁_pos : 0 < ε₁ := lt_min hε (by norm_num)
  have hlog65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hδ₁_pos : 0 < δ₁ := lt_min (by norm_num) (by positivity)
  have hδ₁_le : δ₁ ≤ 1 / 4 := min_le_left _ _
  by_cases hEx : ∃ (q₂ : ℕ) (_ : NeZero q₂), 2 ≤ q₂ ∧
      ∃ χ₂ : DirichletCharacter ℂ q₂, χ₂.IsPrimitive ∧ IsReal χ₂ ∧ χ₂ ≠ 1 ∧
        ∃ β₂ ∈ Set.Icc (1 - δ₁) 1, DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0
  · obtain ⟨q₂, hnz₂, hq₂, χ₂, hp₂, hr₂, hχ₂, β₂, hβ₂_mem, hβ₂_zero⟩ := hEx
    have hβ₂_lo : 3 / 4 ≤ β₂ := by linarith [hβ₂_mem.1]
    have hβ₂_lt : β₂ < 1 := by
      rcases eq_or_lt_of_le hβ₂_mem.2 with rfl | hlt
      · exact False.elim (LFunction_ne_zero_on_re_one χ₂ (by norm_num) (Or.inl hχ₂) hβ₂_zero)
      · exact hlt
    obtain ⟨C_diff, hC_diff_pos, hdiff⟩ := siegel_distinct_zero_case_bound hε hq₂ hp₂ hr₂ hχ₂
      hβ₂_lo hβ₂_lt hβ₂_zero hβ₂_mem.1
    have hL2_pos : 0 < (DirichletCharacter.LFunction χ₂ 1).re := LFunction_one_pos_of_isReal hχ₂ hr₂
    let C_eq : ℝ := (DirichletCharacter.LFunction χ₂ 1).re * (q₂ : ℝ) ^ ε
    have hC_eq_pos : 0 < C_eq := by positivity
    refine ⟨min C_diff C_eq, lt_min hC_diff_pos hC_eq_pos, fun {q₁} _ hq₁ {χ₁} hp₁ hr₁ hχ₁ ↦ ?_⟩
    by_cases hsame : (⟨q₁, χ₁⟩ : Σ m : ℕ, DirichletCharacter ℂ m) = ⟨q₂, χ₂⟩
    · have hq_eq : q₁ = q₂ := congrArg Sigma.fst hsame
      subst hq_eq
      have hχ_eq : χ₁ = χ₂ := eq_of_heq (Sigma.ext_iff.mp hsame).2
      subst hχ_eq
      calc
        min C_diff C_eq * (q₁ : ℝ) ^ (-ε) ≤ C_eq * (q₁ : ℝ) ^ (-ε) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = (DirichletCharacter.LFunction χ₁ 1).re * ((q₁ : ℝ) ^ ε * (q₁ : ℝ) ^ (-ε)) := by
            dsimp only [C_eq]; ring
        _ = (DirichletCharacter.LFunction χ₁ 1).re := by
            rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < q₁)), add_neg_cancel,
              Real.rpow_zero, mul_one]
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
        (hdiff hq₁ hp₁ hr₁ hχ₁ hsame)
  · let C₁ : ℝ := c_P * min δ₁ 1 * (ε / 2)
    have hC₁_pos : 0 < C₁ := by positivity
    refine ⟨C₁, hC₁_pos, fun {q} _ hq {χ} hp hr hχ ↦ ?_⟩
    have hL_ge1 : 1 ≤ Real.log ((q : ℝ) + 2) := by
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have hexp : Real.exp 1 ≤ (q : ℝ) + 2 := Real.exp_one_lt_d9.le.trans (by linarith)
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hexp)
    have hno : ∀ σ ∈ Set.Icc (1 - δ₁ / Real.log ((q : ℝ) + 2)) 1,
        DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
      intro σ hσ hσ_zero
      have hdiv : δ₁ / Real.log ((q : ℝ) + 2) ≤ δ₁ := div_le_self hδ₁_pos.le hL_ge1
      have hmem : σ ∈ Set.Icc (1 - δ₁) 1 := ⟨by linarith [hσ.1], hσ.2⟩
      exact hEx ⟨q, inferInstance, hq, χ, hp, hr, hχ, σ, hmem, hσ_zero⟩
    have hpage := hnozero hq hχ hr δ₁ hδ₁_pos hno
    have hlog_bd := log_add_two_le_rpow hq hε
    have hlog_pos : 0 < Real.log ((q : ℝ) + 2) := by linarith
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    calc
      C₁ * (q : ℝ) ^ (-ε) = c_P * min δ₁ 1 / ((2 / ε) * (q : ℝ) ^ ε) := by
          rw [Real.rpow_neg hq_pos.le]
          dsimp only [C₁]
          field_simp [hε.ne']
      _ ≤ c_P * min δ₁ 1 / Real.log ((q : ℝ) + 2) :=
          div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_bd
      _ ≤ (DirichletCharacter.LFunction χ 1).re := hpage

/-- Siegel's theorem for all real Dirichlet characters: for every `ε > 0`, there exists an
ineffective constant `C > 0` such that for every real non-principal Dirichlet character `χ`
modulo `q ≥ 2`, `C * (q : ℝ) ^ (-ε) ≤ (LFunction χ 1).re`. -/
theorem siegel_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q},
      IsReal χ → χ ≠ 1 →
      C * (q : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨C₀, hC₀_pos, hsieg⟩ := siegel_theorem_primitive (ε / 2) (by positivity)
  let C_log : ℝ := Real.exp 1 * (1 + 4 / ε)
  have hC_log_pos : 0 < C_log := by positivity
  refine ⟨C₀ / C_log, by positivity, fun {q} _ hq {χ} hr hχ ↦ ?_⟩
  let d : ℕ := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have : NeZero d := ⟨fun h ↦ NeZero.ne q (by simpa [h] using hd)⟩
  let χs : DirichletCharacter ℂ d := χ.primitiveCharacter
  have hχ_eq : χ = DirichletCharacter.changeLevel hd χs :=
    (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
  have hχs_prim : χs.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hχs_ne : χs ≠ 1 := fun h ↦ hχ (by rw [hχ_eq, h, map_one])
  have hds_ge3 : 3 ≤ d := three_le_conductor_of_ne_one hχ
  have hds_ge2 : 2 ≤ d := by omega
  have hχs_real : IsReal χs := by
    rw [isReal_iff_sq_eq_one]
    apply DirichletCharacter.changeLevel_injective hd
    rw [map_pow, ← hχ_eq, (isReal_iff_sq_eq_one χ).mp hr, map_one]
  have hsieg_d : C₀ * (d : ℝ) ^ (-(ε / 2)) ≤ (DirichletCharacter.LFunction χs 1).re :=
    hsieg hds_ge2 hχs_prim hχs_real hχs_ne
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd_le_q : (d : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hd
  have hpow_dq : (q : ℝ) ^ (-(ε / 2)) ≤ (d : ℝ) ^ (-(ε / 2)) := by
    rw [Real.rpow_neg hq_pos.le, Real.rpow_neg hd_pos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hd_pos _)
      (Real.rpow_le_rpow hd_pos.le hd_le_q (by positivity))
  have hsieg_q : C₀ * (q : ℝ) ^ (-(ε / 2)) ≤ (DirichletCharacter.LFunction χs 1).re :=
    (mul_le_mul_of_nonneg_left hpow_dq hC₀_pos.le).trans hsieg_d
  have hL_fac : DirichletCharacter.LFunction χ 1 = DirichletCharacter.LFunction χs 1 *
      ∏ p ∈ q.primeFactors, (1 - χs p * (p : ℂ) ^ (-(1 : ℂ))) := by
    conv_lhs => rw [hχ_eq]
    exact LFunction_changeLevel_eq hd χs (Or.inl hχs_ne)
  let fac : ℕ → ℝ := fun p ↦ 1 - (χs p).re * (p : ℝ)⁻¹
  have hfac_prod_eq : ∏ p ∈ q.primeFactors, (1 - χs p * (p : ℂ) ^ (-(1 : ℂ))) =
      ((∏ p ∈ q.primeFactors, fac p : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [Complex.cpow_neg_one]
    apply Complex.ext
    · simp [fac, Complex.mul_re, hχs_real (p : ZMod d)]
    · simp [Complex.mul_im, hχs_real (p : ZMod d)]
  have hre_eq : (DirichletCharacter.LFunction χ 1).re =
      (DirichletCharacter.LFunction χs 1).re * ∏ p ∈ q.primeFactors, fac p := by
    rw [hL_fac, hfac_prod_eq, mul_comm, Complex.re_ofReal_mul, mul_comm]
  have hfac_ge : ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) ≤ ∏ p ∈ q.primeFactors, fac p := by
    refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) (fun p _ ↦ ?_)
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    · have hχ_re : (χs p).re ≤ 1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans
        (norm_char_le_one χs (p : ZMod d)))).2
      have hpinv_nn : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      dsimp only [fac]
      nlinarith
  have heuler := euler_factor_prod_lower_bound (by omega : 1 ≤ q)
  have hlog_bd : Real.exp 1 * (1 + Real.log (q : ℝ)) ≤ C_log * (q : ℝ) ^ (ε / 2) := by
    have hq_ge1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hpow_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ (ε / 2) := Real.one_le_rpow hq_ge1 (by positivity)
    have hlog_rpow : Real.log (q : ℝ) ≤ (2 / ε) * (q : ℝ) ^ (ε / 2) := by
      have h0 : (ε / 2) * Real.log (q : ℝ) ≤ (q : ℝ) ^ (ε / 2) := by
        rw [← Real.log_rpow hq_pos]
        linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hq_pos (ε / 2))]
      calc
        Real.log (q : ℝ) = (2 / ε) * ((ε / 2) * Real.log (q : ℝ)) := by field_simp [hε.ne']
        _ ≤ (2 / ε) * (q : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left h0 (by positivity)
    have hsum_bd : 1 + Real.log (q : ℝ) ≤ (1 + 4 / ε) * (q : ℝ) ^ (ε / 2) := by
      calc
        1 + Real.log (q : ℝ) ≤ 1 * (q : ℝ) ^ (ε / 2) + (2 / ε) * (q : ℝ) ^ (ε / 2) :=
            add_le_add (by simpa using hpow_ge1) hlog_rpow
        _ ≤ (1 + 4 / ε) * (q : ℝ) ^ (ε / 2) := by
            rw [← add_mul]
            have h24 : 2 / ε ≤ 4 / ε := div_le_div_of_nonneg_right (by norm_num) hε.le
            refine mul_le_mul_of_nonneg_right (by linarith only [h24])
              (by positivity)
    dsimp only [C_log]
    calc
      Real.exp 1 * (1 + Real.log (q : ℝ)) ≤ Real.exp 1 * ((1 + 4 / ε) * (q : ℝ) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left hsum_bd (Real.exp_pos 1).le
      _ = Real.exp 1 * (1 + 4 / ε) * (q : ℝ) ^ (ε / 2) := by ring
  have heuler2 : (1 / C_log) * (q : ℝ) ^ (-(ε / 2)) ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hq_pow_pos : 0 < (q : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hq_pos (ε / 2)
    have hlog_pos : 0 < Real.exp 1 * (1 + Real.log (q : ℝ)) := by
      have hln : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
      exact mul_pos (Real.exp_pos 1) (by linarith)
    calc
      (1 / C_log) * (q : ℝ) ^ (-(ε / 2)) = 1 / (C_log * (q : ℝ) ^ (ε / 2)) := by
          rw [Real.rpow_neg hq_pos.le]
          field_simp [hC_log_pos.ne', hq_pow_pos.ne']
      _ ≤ 1 / (Real.exp 1 * (1 + Real.log (q : ℝ))) :=
          div_le_div_of_nonneg_left zero_le_one hlog_pos hlog_bd
      _ ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := heuler
  have heuler_fac : (1 / C_log) * (q : ℝ) ^ (-(ε / 2)) ≤ ∏ p ∈ q.primeFactors, fac p :=
    heuler2.trans hfac_ge
  have hprod_ge : (C₀ / C_log) * (q : ℝ) ^ (-ε) =
      (C₀ * (q : ℝ) ^ (-(ε / 2))) * ((1 / C_log) * (q : ℝ) ^ (-(ε / 2))) := by
    have hpow_eq : (q : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2)) = (q : ℝ) ^ (-ε) := by
      rw [← Real.rpow_add hq_pos]
      ring_nf
    calc
      (C₀ / C_log) * (q : ℝ) ^ (-ε) = (C₀ * (1 / C_log)) * ((q : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2))) := by
          rw [hpow_eq]; ring
      _ = (C₀ * (q : ℝ) ^ (-(ε / 2))) * ((1 / C_log) * (q : ℝ) ^ (-(ε / 2))) := by ring
  rw [hre_eq, hprod_ge]
  exact mul_le_mul hsieg_q heuler_fac (by positivity) (LFunction_one_pos_of_isReal hχs_ne hχs_real).le

/-- Siegel's theorem zero-free bound: for every `ε > 0`, there exists an ineffective constant
`c > 0` such that for every real non-principal Dirichlet character `χ` modulo `q ≥ 2` and every
real `β` with `LFunction χ β = 0`, we have `β ≤ 1 - c * (q : ℝ) ^ (-ε)`. -/
theorem siegel_zero_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ c > 0, ∀ {q : ℕ} [NeZero q], 2 ≤ q → ∀ {χ : DirichletCharacter ℂ q},
      IsReal χ → χ ≠ 1 → ∀ β : ℝ,
      DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      β ≤ 1 - c * (q : ℝ) ^ (-ε) := by
  obtain ⟨C_S, hC_S, hsieg⟩ := siegel_theorem (ε / 3) (by positivity)
  obtain ⟨C_d, hC_d, hderiv⟩ := norm_deriv_LFunction_near_one_le
  let K_sq : ℝ := (6 / ε) ^ 2
  have hK_sq_pos : 0 < K_sq := by positivity
  let c : ℝ := min (1 / (4 * (6 / ε))) (C_S / (C_d * K_sq))
  have hc_pos : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc_pos, fun {q} _ hq {χ} hr hχ β hzero ↦ ?_⟩
  have hβ_lt : β < 1 := by
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_on_re_one χ (by simpa using hge) (Or.inl hχ) hzero
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < q := by linarith
  have hlog_ge1 : 1 ≤ Real.log ((q : ℝ) + 2) := by
    have hexp : Real.exp 1 ≤ (q : ℝ) + 2 := Real.exp_one_lt_d9.le.trans (by linarith)
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hexp)
  have hlog_pos : 0 < Real.log ((q : ℝ) + 2) := by linarith
  have hlog_rpow := log_add_two_le_rpow hq (by positivity : 0 < ε / 3)
  by_cases hnear : β < 1 - 1 / (4 * Real.log ((q : ℝ) + 2))
  · have hlog_le : Real.log ((q : ℝ) + 2) ≤ (6 / ε) * (q : ℝ) ^ ε := by
      have hle : (q : ℝ) ^ (ε / 3) ≤ (q : ℝ) ^ ε :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have heq : 2 / (ε / 3) = 6 / ε := by ring
      rw [heq] at hlog_rpow
      exact hlog_rpow.trans (mul_le_mul_of_nonneg_left hle (by positivity))
    have hdiv_ge : c * (q : ℝ) ^ (-ε) ≤ 1 / (4 * Real.log ((q : ℝ) + 2)) := by
      rw [Real.rpow_neg hq_pos.le]
      calc
        c * ((q : ℝ) ^ ε)⁻¹ ≤ (1 / (4 * (6 / ε))) * ((q : ℝ) ^ ε)⁻¹ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = 1 / (4 * ((6 / ε) * (q : ℝ) ^ ε)) := by ring
        _ ≤ 1 / (4 * Real.log ((q : ℝ) + 2)) :=
            div_le_div_of_nonneg_left zero_le_one (by positivity)
              (mul_le_mul_of_nonneg_left hlog_le (by norm_num))
    linarith
  · push Not at hnear
    let g : ℝ → ℂ := fun t ↦ DirichletCharacter.LFunction χ (t : ℂ)
    have hg_diff : ∀ t : ℝ, HasDerivAt g (deriv (DirichletCharacter.LFunction χ) (t : ℂ)) t :=
      fun t ↦ (DirichletCharacter.differentiable_LFunction hχ (t : ℂ)).hasDerivAt.comp_ofReal
    have hmvt := (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
      (fun t _ ↦ (hg_diff t).differentiableAt)
      (fun t ht ↦ by rw [(hg_diff t).deriv]; exact hderiv hq hχ t ht.1 ht.2)
      ⟨hnear, hβ_lt.le⟩ ⟨by linarith [show 0 < 1 / (4 * Real.log ((q : ℝ) + 2)) by positivity], le_rfl⟩
    have hL1_pos : 0 < (DirichletCharacter.LFunction χ 1).re := LFunction_one_pos_of_isReal hχ hr
    have hL1_norm : ‖g 1 - g β‖ = (DirichletCharacter.LFunction χ 1).re := by
      dsimp only [g]
      rw [hzero, sub_zero]
      have him : (DirichletCharacter.LFunction χ 1).im = 0 := LFunction_real_im_zero hχ hr 1
      have h1 : DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ) =
          ((DirichletCharacter.LFunction χ 1).re : ℂ) := by
        rw [Complex.ofReal_one]
        exact Complex.ext rfl him
      rw [h1, Complex.norm_real, Real.norm_of_nonneg hL1_pos.le]
    rw [hL1_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hβ_lt.le)] at hmvt
    have hsieg_bd := hsieg hq hr hχ
    have hlog_sq_bd : (Real.log ((q : ℝ) + 2)) ^ 2 ≤ K_sq * (q : ℝ) ^ (2 * ε / 3) := by
      have heq_e : (q : ℝ) ^ (ε / 3) * (q : ℝ) ^ (ε / 3) = (q : ℝ) ^ (2 * ε / 3) := by
        rw [← Real.rpow_add hq_pos]
        ring_nf
      calc
        (Real.log ((q : ℝ) + 2)) ^ 2 ≤ ((6 / ε) * (q : ℝ) ^ (ε / 3)) ^ 2 := by
            have hle : Real.log ((q : ℝ) + 2) ≤ (6 / ε) * (q : ℝ) ^ (ε / 3) :=
              hlog_rpow.trans_eq (by ring)
            exact pow_le_pow_left₀ hlog_pos.le hle 2
        _ = K_sq * ((q : ℝ) ^ (ε / 3) * (q : ℝ) ^ (ε / 3)) := by dsimp only [K_sq]; ring
        _ = K_sq * (q : ℝ) ^ (2 * ε / 3) := by rw [heq_e]
    have hmain : C_S * (q : ℝ) ^ (-(ε / 3)) ≤ C_d * K_sq * (q : ℝ) ^ (2 * ε / 3) * (1 - β) := by
      calc
        C_S * (q : ℝ) ^ (-(ε / 3)) ≤ (DirichletCharacter.LFunction χ 1).re := hsieg_bd
        _ ≤ C_d * (Real.log ((q : ℝ) + 2)) ^ 2 * (1 - β) := hmvt
        _ ≤ C_d * (K_sq * (q : ℝ) ^ (2 * ε / 3)) * (1 - β) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sq_bd hC_d.le)
              (sub_nonneg.mpr hβ_lt.le)
        _ = C_d * K_sq * (q : ℝ) ^ (2 * ε / 3) * (1 - β) := by ring
    have h1β_ge : c * (q : ℝ) ^ (-ε) ≤ 1 - β := by
      have hden_pos : 0 < C_d * K_sq * (q : ℝ) ^ (2 * ε / 3) := by positivity
      calc
        c * (q : ℝ) ^ (-ε) ≤ (C_S / (C_d * K_sq)) * (q : ℝ) ^ (-ε) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = (C_S * (q : ℝ) ^ (-(ε / 3))) / (C_d * K_sq * (q : ℝ) ^ (2 * ε / 3)) := by
            rw [Real.rpow_neg hq_pos.le, Real.rpow_neg hq_pos.le]
            have hadd_e : (q : ℝ) ^ ε = (q : ℝ) ^ (ε / 3) * (q : ℝ) ^ (2 * ε / 3) := by
              rw [← Real.rpow_add hq_pos]; ring_nf
            rw [hadd_e]
            field_simp [hC_d.ne', hK_sq_pos.ne', (Real.rpow_pos_of_pos hq_pos _).ne']
        _ ≤ (C_d * K_sq * (q : ℝ) ^ (2 * ε / 3) * (1 - β)) / (C_d * K_sq * (q : ℝ) ^ (2 * ε / 3)) :=
            div_le_div_of_nonneg_right hmain hden_pos.le
        _ = 1 - β := by field_simp [hden_pos.ne']
    linarith

end SiegelTheorem






