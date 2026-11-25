import AnalyticNumberTheory.RiemannZeta.FourthMomentDiagonalComparison
import AnalyticNumberTheory.DivisorProblems.DivisorSquareAsymptotic
import AnalyticNumberTheory.SieveMethods.WeightedMeanValues

/-!
# Cubic logarithmic error for the short divisor polynomials

The weighted Hilbert inequality bounds the off-diagonal by the unweighted
sum of the squared divisor coefficients, saving one logarithm. The
arithmetic diagonal may be evaluated at the real cutoff before rounding.
-/

noncomputable section
open Complex Real Finset Filter MeasureTheory
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DivisorProblems
open AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.RiemannZeta

/-- The squared short divisor polynomial has a mean-square error of size
N (1+log N)³ throughout every dyadic interval. -/
theorem divisorPolynomial_dyadic_mean_square_sharp {N : ℕ} (hN : 1≤N) (T : ℝ) :
    |(∫t in T..2*T,‖divisorPolynomial N ((1/2:ℂ)+t*I)‖^2)-T*fourthMomentDiagonal N| ≤
      4*weightedHilbertConstant*N*(1+Real.log N)^3 := by
  have H := weighted_dirichletPoly_mean_square (fun n => (n.divisors.card:ℂ)) N (1/2) T (2*T)
  simp only [Complex.norm_natCast,show -2*(1/2:ℝ) = -1 by norm_num,Real.rpow_neg_one,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,show 2*T-T=T by ring] at H
  have hsum : (∑n∈Icc 1 N,(n:ℝ)*(n.divisors.card:ℝ)^2*(n:ℝ)⁻¹)=∑n∈Icc 1 N,(n.divisors.card:ℝ)^2 := by
    apply sum_congr rfl;intro n hn
    have h : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hn).1)
    field_simp
  rw [hsum] at H
  have hs := sum_Icc_card_divisors_sq_le N
  rw [max_eq_left hN] at hs
  simp only [←div_eq_mul_inv] at H
  exact H.trans ((mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) weightedHilbertConstant_pos.le)).trans_eq (by ring))

/-- Logarithmic main term of the two short polynomials with the cutoff
T/(4π), including the oscillatory product of the two main terms. -/
theorem fourthMoment_mainTerms_dyadic_sharp :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ}, 8*π≤T → let N := ⌊T/(4*π)⌋₊
      |(∫t in T..2*T,‖fourthMomentMainTerm N false t+fourthMomentMainTerm N true t‖^2)-
        (1/(2*π^2))*T*(Real.log T)^4|≤ C*T*(1+Real.log T)^3 := by
  obtain ⟨B,hB,HB⟩ := divisor_square_harmonic_error
  let d := 4*π
  let c := 1/(4*π^2)
  let A := 4*weightedHilbertConstant
  let F := 64+8/Real.log 2
  let D := 4*Real.log d*c
  have hd : 1<d := by dsimp [d];linarith [Real.pi_gt_three]
  have hd0 := zero_lt_one.trans hd
  have hc : 0<c := by dsimp [c];positivity
  have hF : 0<F := by dsimp [F];positivity
  have hA : 0<A := mul_pos (by norm_num) weightedHilbertConstant_pos
  have hD : 0<D := mul_pos (mul_pos (by norm_num) (log_pos hd)) hc
  refine ⟨2*(A+B+D+F),by positivity,?_⟩
  intro T ht N
  let x := T/d
  have hx : 2≤x := (le_div_iff₀ hd0).mpr (by dsimp [d];linarith)
  have ht2 : 2≤T := by linarith [Real.pi_gt_three]
  have ht0 : 0<T := by linarith
  have hxT : x≤T := div_le_self ht0.le hd.le
  have hn : 1≤N := Nat.le_floor (by simpa using (show 1≤x by linarith))
  have hnR : (1:ℝ)≤N := by exact_mod_cast hn
  have hnX : (N:ℝ)≤x := Nat.floor_le (by linarith)
  have hnT := hnX.trans hxT
  let l := Real.log T
  let w := (1+l)^3
  have hl : 0≤l := Real.log_nonneg (by linarith)
  have hw : 0≤w := by dsimp [w];positivity
  have hu : 0≤Real.log x := Real.log_nonneg (by linarith)
  have hu' : Real.log x≤l := Real.log_le_log (by linarith) hxT
  have hln : 0≤Real.log N := Real.log_nonneg hnR
  have hln' : Real.log N≤l := Real.log_le_log (by linarith) hnT
  have hnw : (1+Real.log N)^3≤w := pow_le_pow_left₀ (by linarith) (by dsimp [l] at *;linarith) 3
  have hxw : (1+Real.log x)^3≤w := pow_le_pow_left₀ (by linarith) (by linarith) 3
  let P := ∫t in T..2*T,‖divisorPolynomial N ((1/2:ℂ)+t*I)‖^2
  let X := ∫t in T..2*T,fourthMomentMainTerm N false t*conj (fourthMomentMainTerm N true t)
  have h₁ : |P-T*fourthMomentDiagonal N|≤A*T*w := (divisorPolynomial_dyadic_mean_square_sharp hn T).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hnT hA.le) hnw (by positivity) (mul_nonneg hA.le ht0.le))
  have h₂ : |X.re|≤F*T*w := (Complex.abs_re_le_norm X).trans ((norm_integral_fourthMomentMainTerm_mul_conj_le hn ht2 hnX).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hnT hF.le) hnw (by positivity) (mul_nonneg hF.le ht0.le)))
  have h₃ : |fourthMomentDiagonal N-c*(Real.log x)^4|≤B*w := (HB (x:=x) (by linarith)).trans
    (mul_le_mul_of_nonneg_left hxw hB.le)
  have hshift : |Real.log x-l|=Real.log d := by
    change |Real.log (T/d)-Real.log T|=_
    rw [Real.log_div ht0.ne' hd0.ne',sub_sub_cancel_left,abs_neg,abs_of_nonneg (Real.log_nonneg hd.le)]
  have hpow := abs_pow_sub_pow_le (Real.log x) l 4
  rw [hshift,abs_of_nonneg hu,abs_of_nonneg hl,max_eq_right hu'] at hpow
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hpow
  have h₄ : |c*(Real.log x)^4-c*l^4|≤D*w := by
    rw [←mul_sub,abs_mul,abs_of_pos hc]
    apply (mul_le_mul_of_nonneg_left hpow hc.le).trans
    have hlw : l^3≤w := pow_le_pow_left₀ hl (by linarith) 3
    exact (mul_le_mul_of_nonneg_left hlw hD.le).trans_eq' (by dsimp [D];ring)
  have hdg : |fourthMomentDiagonal N-c*l^4|≤(B+D)*w :=
    (abs_sub_le _ (c*(Real.log x)^4) _).trans ((add_le_add h₃ h₄).trans_eq (by ring))
  have hmul := mul_le_mul_of_nonneg_left hdg ht0.le
  rw [←abs_of_pos ht0,←abs_mul] at hmul
  rw [abs_of_pos ht0] at hmul
  rw [mul_sub] at hmul
  have he := integral_fourthMomentMainTerms_sq N T (2*T)
  change _=2*P+2*X.re at he
  rw [he,show 1/(2*π^2)=2*c by dsimp [c];ring]
  change |2*P+2*X.re-2*c*T*l^4|≤2*(A+B+D+F)*T*w
  rw [abs_le] at h₁ h₂ hmul ⊢
  constructor <;>linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hmul.1,hmul.2]

end AnalyticNumberTheory.RiemannZeta
