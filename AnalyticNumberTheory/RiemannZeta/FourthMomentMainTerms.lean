import AnalyticNumberTheory.RiemannZeta.FourthMomentApproximation
import AnalyticNumberTheory.AnalyticTools.GeometricMeanSquares
import Mathlib.Data.Nat.Log

/-!
# Unweighted main terms in the fourth moment

A contour to the left of the origin separates the ordinary divisor polynomial from the
smoothed sum. The remaining long interval is divided into geometrically growing blocks.
-/

open Complex Real MeasureTheory Filter Set Finset
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools

namespace AnalyticNumberTheory.RiemannZeta

/-- The unweighted part of the original or the reflected divisor sum. -/
noncomputable def fourthMomentMainTerm (N : ℕ) (neg : Bool) (t : ℝ) : ℂ :=
  let u := if neg then -t else t
  (xiCompletionFactor ((1/2:ℂ)+u*I)^2 / xiCompletionFactor ((1/2:ℂ)+t*I)^2) *
    divisorPolynomial N ((1/2:ℂ)+u*I)

private theorem factor_half_ne_zero (t : ℝ) : xiCompletionFactor ((1/2:ℂ)+t*I) ≠ 0 := by
  let s := (1/2:ℂ)+t*I
  have hs : s.re = 1/2 := by simp [s]
  have h₀ : s ≠ 0 := by intro h; rw [h,Complex.zero_re] at hs; norm_num at hs
  have h₁ : s ≠ 1 := by intro h; rw [h,Complex.one_re] at hs; norm_num at hs
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (1/2:ℂ) ≠ 0) h₀) (sub_ne_zero.mpr h₁))
    (Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num))

/-- The reflected phase has modulus one, so the two unweighted pieces have the norms of
the ordinary divisor polynomials at the respective heights. -/
theorem norm_fourthMomentMainTerm (N : ℕ) (neg : Bool) (t : ℝ) :
    ‖fourthMomentMainTerm N neg t‖ = ‖divisorPolynomial N ((1/2:ℂ)+(if neg then -t else t:ℝ)*I)‖ := by
  have hh : ((1/2:ℂ)+(-t:ℝ)*I) = conj ((1/2:ℂ)+t*I) := by
    rw [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_one,map_ofNat,Complex.ofReal_neg]; ring
  cases neg
  · change ‖(xiCompletionFactor ((1/2:ℂ)+t*I)^2/xiCompletionFactor ((1/2:ℂ)+t*I)^2)*_‖ = _
    rw [div_self (pow_ne_zero 2 (factor_half_ne_zero t)),one_mul]
  · simp only [fourthMomentMainTerm,ite_true,hh,norm_mul,norm_div,norm_pow,xiCompletionFactor_conj,Complex.norm_conj]
    rw [div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr (factor_half_ne_zero t))),one_mul]

/-- The finite divisor polynomial takes conjugate values at conjugate arguments. -/
theorem divisorPolynomial_conj (N : ℕ) (s : ℂ) :
    divisorPolynomial N (conj s) = conj (divisorPolynomial N s) := by
  simp only [divisorPolynomial,AnalyticNumberTheory.DirichletSeries.dirichletPoly,map_sum,map_mul,map_natCast]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [← map_neg,Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),map_natCast]

/-- At the same height the main terms from the two sides have the same modulus. -/
theorem norm_fourthMomentMainTerm_eq (N : ℕ) (neg : Bool) (t : ℝ) :
    ‖fourthMomentMainTerm N neg t‖ = ‖divisorPolynomial N ((1/2:ℂ)+t*I)‖ := by
  rw [norm_fourthMomentMainTerm]
  cases neg
  · rfl
  · have hh : ((1/2:ℂ)+(-t:ℝ)*I) = conj ((1/2:ℂ)+t*I) := by
      rw [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_one,map_ofNat,Complex.ofReal_neg]; ring
    simp only [ite_true,hh,divisorPolynomial_conj,Complex.norm_conj]

/-- Differences of unweighted main terms have the same modulus in both directions. -/
theorem norm_fourthMomentMainTerm_sub (M N : ℕ) (neg : Bool) (t : ℝ) :
    ‖fourthMomentMainTerm M neg t-fourthMomentMainTerm N neg t‖ =
      ‖divisorPolynomial M ((1/2:ℂ)+t*I)-divisorPolynomial N ((1/2:ℂ)+t*I)‖ := by
  let s := (1/2:ℂ)+t*I
  have hne : xiCompletionFactor s^2 ≠ 0 := pow_ne_zero 2 (factor_half_ne_zero t)
  cases neg
  · change ‖xiCompletionFactor s^2/xiCompletionFactor s^2*divisorPolynomial M s -
      xiCompletionFactor s^2/xiCompletionFactor s^2*divisorPolynomial N s‖ = _
    rw [div_self hne,one_mul,one_mul]
  · have hh : ((1/2:ℂ)+(-t:ℝ)*I) = conj s := by
      dsimp only [s]
      rw [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_one,map_ofNat,Complex.ofReal_neg]; ring
    simp only [fourthMomentMainTerm,ite_true,hh,← mul_sub,divisorPolynomial_conj,← map_sub,
      norm_mul,norm_div,norm_pow,xiCompletionFactor_conj,Complex.norm_conj]
    change ‖xiCompletionFactor s‖^2/‖xiCompletionFactor s‖^2*_ = _
    rw [div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr (factor_half_ne_zero t))),one_mul]

/-- Each unweighted piece varies continuously with height. -/
theorem continuous_fourthMomentMainTerm (N : ℕ) (neg : Bool) : Continuous (fourthMomentMainTerm N neg) := by
  let s (t : ℝ) := (1/2:ℂ)+t*I
  let u (t : ℝ) := if neg then -t else t
  have hu : Continuous u := by cases neg <;> first | exact continuous_id.neg | exact continuous_id
  have hs : Continuous s := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have ha : Continuous (fun t => xiCompletionFactor (s t)) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_xiCompletionFactor (by simp [s] : 0 < (s t).re)).continuousAt.comp hs.continuousAt
  have hpoly : Continuous (fun t : ℝ => divisorPolynomial N (s t)) := by
    simpa only [s,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using divisorPolynomial_continuous N (1/2)
  exact ((((ha.comp hu).pow 2).div (ha.pow 2) (fun t => pow_ne_zero _ (factor_half_ne_zero t))).mul (hpoly.comp hu))

/-- Uniform bounded remainder after separating ordinary divisor polynomials of any chosen
length and writing the rest as short negative-line pieces and positive-line differences. -/
theorem norm_zeta_sq_sub_fourthMomentMainTerms_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {T t : ℝ}, 2 ≤ T → t ∈ Icc T (2*T) → ∀ N : ℕ,
      let M := ⌈T^2⌉₊
      let p (neg : Bool) := fourthMomentMainTerm N neg t + fourthMomentPiece (-(1/4)) N neg t +
        (fourthMomentPiece 4 M neg t - fourthMomentPiece 4 N neg t)
      ‖riemannZeta ((1/2:ℂ)+t*I)^2 - (p false+p true)‖ ≤ B := by
  obtain ⟨B,hB,h⟩ := norm_zeta_sq_sub_fourthMomentPieces_le (by norm_num : (0:ℝ)<1)
  refine ⟨B,hB,?_⟩
  intro T t hT ht N
  let M := ⌈T^2⌉₊
  have hh := h hT ht
  rw [show (1:ℝ)+1=2 by norm_num,Real.rpow_two] at hh
  have hs (neg : Bool) : fourthMomentMainTerm N neg t + fourthMomentPiece (-(1/4)) N neg t +
       (fourthMomentPiece 4 M neg t-fourthMomentPiece 4 N neg t) = fourthMomentPiece 1 M neg t := by
    have he := fourthMomentPiece_sub_neg (a := 1/4) (b := 4) (by norm_num) (by norm_num) (by norm_num) hT ht N neg
    change fourthMomentPiece 4 N neg t-fourthMomentPiece (-(1/4)) N neg t = fourthMomentMainTerm N neg t at he
    rw [← he, fourthMomentPiece_eq_of_pos (a := 1) (b := 4) (by norm_num) (by norm_num) hT ht M neg]
    ring
  change ‖_ - ((_ + _ + _) + (_ + _ + _))‖ ≤ _
  rw [hs false,hs true]
  exact hh

/-- A geometric partition of `(N,M]` combines mean-square bounds for contiguous blocks.
The exponent two in the geometric decay absorbs the number of blocks. -/
theorem fourthMomentPiece_tail_mean_sq {T B : ℝ} (hT : 2 ≤ T) (hB : 0 ≤ B)
    {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) (neg : Bool)
    (hblock : ∀ j : ℕ, let X := 2^j*N
      X ≤ M → (∫ t in T..2*T, ‖fourthMomentPiece 4 (min M (2*X)) neg t - fourthMomentPiece 4 X neg t‖^2) ≤
        B*(1/4:ℝ)^j) :
    (∫ t in T..2*T, ‖fourthMomentPiece 4 M neg t-fourthMomentPiece 4 N neg t‖^2) ≤ 4*B := by
  let J := Nat.log 2 M + 1
  let X (j : ℕ) := min M (2^j*N)
  let f (j : ℕ) (t : ℝ) := fourthMomentPiece 4 (X (j+1)) neg t-fourthMomentPiece 4 (X j) neg t
  have hX0 : X 0 = N := by simp [X,min_eq_right hNM]
  have hXM : X J = M := by
    apply min_eq_left
    have hh : M < 2^J := Nat.lt_pow_succ_log_self (by decide) M
    exact hh.le.trans (Nat.le_mul_of_pos_right _ hN)
  have he (t : ℝ) : ∑ j ∈ range J, f j t = fourthMomentPiece 4 M neg t-fourthMomentPiece 4 N neg t := by
    simpa only [f,hX0,hXM] using Finset.sum_range_sub (fun i => fourthMomentPiece 4 (X i) neg t) J
  have hcont (n : ℕ) := continuousOn_fourthMomentPiece (c := 4) (by norm_num) (by norm_num) hT n neg
  simp_rw [← he]
  apply integral_norm_sum_sq_le_geometric (by linarith) hB J f (fun j _ => (hcont _).sub (hcont _))
  intro j _
  have hnext : 2^(j+1)*N = 2*(2^j*N) := by rw [pow_succ]; ring
  by_cases hb : 2^j*N ≤ M
  · simpa only [f,X,min_eq_right hb,hnext] using hblock j hb
  · have h₁ : M ≤ 2^j*N := le_of_not_ge hb
    have h₂ : M ≤ 2^(j+1)*N := by rw [hnext]; omega
    simp [f,X,min_eq_left h₁,min_eq_left h₂]
    positivity

end AnalyticNumberTheory.RiemannZeta
