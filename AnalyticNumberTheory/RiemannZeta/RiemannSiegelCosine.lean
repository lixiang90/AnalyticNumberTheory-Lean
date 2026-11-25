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

private theorem hardyUnit_mul_dualGamma {t : ℝ} (ht : t≠0) :
    hardyGammaUnit t*riemannDualGamma (1/2+(t:ℂ)*I)=conj (hardyGammaUnit t) := by
  let s := (1/2:ℂ)+(t:ℂ)*I
  have hi : s.im=t := by simp [s]
  have hs : 1-s=conj s := by simp [s,Complex.conj_ofNat];ring
  have hg : Gammaℝ s≠0 := Gammaℝ_ne_zero_of_re_pos (by simp [s])
  change (Gammaℝ s/(‖Gammaℝ s‖:ℝ))*riemannDualGamma s=conj (Gammaℝ s/(‖Gammaℝ s‖:ℝ))
  rw [riemannDualGamma_eq_ratio (hi ▸ ht),hs,Gammaℝ_conj,map_div₀,Complex.conj_ofReal]
  field_simp

/-- Hardy's function as a finite cosine sum of length floor(sqrt(|t|/(2π))),
with error at most 604(2π)^{1/4}|t|^{-1/4}. The gamma phase is taken modulo
a full turn, which leaves every cosine unchanged. -/
theorem hardyZ_riemannSiegel_cosine {t : ℝ} (ht : 8*Real.pi≤|t|) :
    let N := ⌊Real.sqrt (|t|/(2*Real.pi))⌋₊
    |hardyZ t-2*∑ m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)| ≤
      604*(2*Real.pi)^(1/4:ℝ)*|t|^(-(1/4:ℝ)) := by
  intro N
  let s := (1/2:ℂ)+(t:ℂ)*I
  let P := ∑ m∈range N,((m:ℂ)+1)^(-s)
  let U := hardyGammaUnit t
  have hti : t≠0 := abs_pos.mp ((by positivity : 0<8*Real.pi).trans_le ht)
  have hconj : (∑ m∈range N,((m:ℂ)+1)^(s-1))=conj P := by
    dsimp only [P];rw [map_sum];apply sum_congr rfl
    intro m hm
    have he : s-1=conj (-s) := by simp [s,Complex.conj_ofNat];ring
    rw [he,←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.cpow_conj]
    · simp
    · rw [Complex.arg_ofReal_of_nonneg (by positivity)];exact Real.pi_ne_zero.symm
  have H := riemannSiegel_sharp_error ht
  change ‖riemannZeta s-P-riemannDualGamma s*(∑ m∈range N,((m:ℂ)+1)^(s-1))‖≤_ at H
  rw [hconj] at H
  have H' : ‖(hardyZ t:ℂ)-((U*P)+conj (U*P))‖ ≤ 604*(2*Real.pi)^(1/4:ℝ)*|t|^(-(1/4:ℝ)) := by
    rw [show (hardyZ t:ℂ)-((U*P)+conj (U*P))=U*(riemannZeta s-P-riemannDualGamma s*conj P) by
      rw [hardyZ_eq_gammaUnit_mul_zeta,map_mul,←hardyUnit_mul_dualGamma hti];dsimp only [U,s];ring,
      norm_mul,norm_hardyGammaUnit,one_mul]
    exact H
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
  rw [Complex.add_conj] at H'
  change ‖((hardyZ t:ℝ):ℂ)-((2*(U*P).re:ℝ):ℂ)‖≤_ at H'
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,hp] at H'
  exact H'

end AnalyticNumberTheory.RiemannZeta
