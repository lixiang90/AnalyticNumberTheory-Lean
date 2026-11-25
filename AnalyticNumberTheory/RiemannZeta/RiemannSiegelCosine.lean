import AnalyticNumberTheory.RiemannZeta.HurwitzLogFreeApproximation
import AnalyticNumberTheory.RiemannZeta.RiemannDualGamma
import AnalyticNumberTheory.RiemannZeta.HardyGammaPhase
import AnalyticNumberTheory.RiemannZeta.HurwitzApproximation

/-!
# The Riemann–Siegel cosine sum

On the critical line the reciprocal polynomial becomes the complex
conjugate of the direct polynomial after multiplication by Hardy's unit
gamma factor. Its real part is a sum of ordinary cosines.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
namespace AnalyticNumberTheory.RiemannZeta

/-- On the critical line Hardy's unit intertwines the reciprocal gamma factor with complex conjugation. -/
theorem hardyUnit_mul_dualGamma {t : ℝ} (ht : t≠0) :
    hardyGammaUnit t*riemannDualGamma (1/2+(t:ℂ)*I)=conj (hardyGammaUnit t) := by
  let s := (1/2:ℂ)+(t:ℂ)*I
  have hi : s.im=t := by simp [s]
  have hs : 1-s=conj s := by simp [s,Complex.conj_ofNat];ring
  have hg : Gammaℝ s≠0 := Gammaℝ_ne_zero_of_re_pos (by simp [s])
  change (Gammaℝ s/(‖Gammaℝ s‖:ℝ))*riemannDualGamma s=conj (Gammaℝ s/(‖Gammaℝ s‖:ℝ))
  rw [riemannDualGamma_eq_ratio (hi ▸ ht),hs,Gammaℝ_conj,map_div₀,Complex.conj_ofReal]
  field_simp

/-- Rotating the difference of the two sharp Dirichlet polynomials by Hardy's
unit gives exactly the real cosine-sum error, for any truncation length. -/
theorem hardyZ_sub_cosines_eq {t : ℝ} (hti : t≠0) (N : ℕ) :
    let s := (1/2:ℂ)+(t:ℂ)*I
    ((hardyZ t-2*∑ m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1):ℝ):ℂ) =
      hardyGammaUnit t*(riemannZeta s-(∑ m∈range N,((m:ℂ)+1)^(-s))-
         riemannDualGamma s*(∑ m∈range N,((m:ℂ)+1)^(s-1))) := by
  intro s
  let P := ∑ m∈range N,((m:ℂ)+1)^(-s)
  let U := hardyGammaUnit t
  have hconj : (∑ m∈range N,((m:ℂ)+1)^(s-1))=conj P := by
    dsimp only [P];rw [map_sum];apply sum_congr rfl
    intro m hm
    have he : s-1=conj (-s) := by simp [s,Complex.conj_ofNat];ring
    rw [he,←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.cpow_conj]
    · simp
    · rw [Complex.arg_ofReal_of_nonneg (by positivity)];exact Real.pi_ne_zero.symm
  have hphase : U=Complex.exp ((U.arg:ℂ)*I) := by
    have h := Complex.norm_mul_exp_arg_mul_I U
    rw [norm_hardyGammaUnit] at h;simpa using h.symm
  have hp : (U*P).re=∑ m∈range N,Real.cos (U.arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1) := by
    dsimp only [P];rw [mul_sum,Complex.re_sum];apply sum_congr rfl
    intro m hm
    have hp : 0<(m:ℝ)+1 := by positivity
    rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,critical_monomial_eq hp]
    nth_rw 1 [hphase]
    rw [Complex.ofReal_neg]
    rw [show ∀ b : ℝ, Complex.exp ((U.arg:ℂ)*I)*((b:ℂ)*Complex.exp (I*(-((Real.log ((m:ℝ)+1):ℝ):ℂ))*(t:ℂ)))=
      (b:ℂ)*Complex.exp (((U.arg-t*Real.log ((m:ℝ)+1):ℝ):ℂ)*I) by
      intro b;rw [mul_left_comm,←Complex.exp_add];congr 2;push_cast;ring]
    rw [Complex.re_ofReal_mul,Complex.exp_ofReal_mul_I_re];ring
  rw [hconj]
  have hU : (hardyZ t:ℂ)-(U*P+conj (U*P))=U*(riemannZeta s-P-riemannDualGamma s*conj P) := by
    rw [hardyZ_eq_gammaUnit_mul_zeta,map_mul,←hardyUnit_mul_dualGamma hti];dsimp only [U,s];ring
  rw [Complex.add_conj,hp] at hU
  simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat] using hU

/-- Hardy's function as a finite cosine sum of length floor(sqrt(|t|/(2π))),
with error at most 604(2π)^{1/4}|t|^{-1/4}. The gamma phase is taken modulo
a full turn, which leaves every cosine unchanged. -/
theorem hardyZ_riemannSiegel_cosine {t : ℝ} (ht : 8*Real.pi≤|t|) :
    let N := ⌊Real.sqrt (|t|/(2*Real.pi))⌋₊
    |hardyZ t-2*∑ m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)| ≤
      604*(2*Real.pi)^(1/4:ℝ)*|t|^(-(1/4:ℝ)) := by
  intro N
  have hti : t≠0 := abs_pos.mp ((by positivity : 0<8*Real.pi).trans_le ht)
  have h := riemannSiegel_sharp_error ht
  have H := congrArg norm (hardyZ_sub_cosines_eq hti N)
  rw [Complex.norm_real,Real.norm_eq_abs,norm_mul,norm_hardyGammaUnit,one_mul] at H
  exact H.le.trans h

end AnalyticNumberTheory.RiemannZeta
