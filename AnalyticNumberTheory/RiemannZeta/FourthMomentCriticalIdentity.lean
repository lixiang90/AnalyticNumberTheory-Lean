import AnalyticNumberTheory.RiemannZeta.FourthMomentContourIntegrand
import AnalyticNumberTheory.RiemannZeta.FourthMomentReflection

/-!
# Exact critical-line expansion of the fourth moment

Reflection interchanges the direct and dual divisor polynomials and fixes
the error. Their two real mixed products with that error are equal. This
leaves one analytic cross integral with multiplicity four.
-/

noncomputable section
open Real Complex MeasureTheory
open scoped ComplexConjugate Interval
namespace AnalyticNumberTheory.RiemannZeta

private abbrev point (t : ℝ) : ℂ := (1/2:ℂ)+t*I

theorem fourthMomentError_critical_eq (N : ℕ) (t : ℝ) :
    fourthMomentError N ((1/2:ℂ)+t*I)=riemannZeta ((1/2:ℂ)+t*I)^2-
      (fourthMomentMainTerm N false t+fourthMomentMainTerm N true t) := by
  rw [fourthMomentMainTerm_false_eq_polynomial,fourthMomentMainTerm_true_eq_reflected,fourthMomentError]
  ring

theorem fourthMomentCrossTerm_critical_eq (N : ℕ) (t : ℝ) :
    fourthMomentCrossTerm N ((1/2:ℂ)+t*I)=fourthMomentError N ((1/2:ℂ)+t*I)*conj (fourthMomentMainTerm N false t) := by
  have hs : 1-point t = conj (point t) := by apply Complex.ext <;> simp [point] <;> ring
  rw [fourthMomentCrossTerm,fourthMomentMainTerm_false_eq_polynomial]
  change _*divisorPolynomial N (1-point t)=_
  rw [hs,divisorPolynomial_conj]

private theorem continuous_error (N : ℕ) : Continuous (fun t => fourthMomentError N (point t)) := by
  simp only [point,fourthMomentError_critical_eq]
  exact (continuous_riemannZeta_half.pow 2).sub ((continuous_fourthMomentMainTerm N false).add (continuous_fourthMomentMainTerm N true))

/-- Reflection of the error on the critical line. -/
theorem fourthMomentError_reflection (N : ℕ) (t : ℝ) :
    let s := (1/2:ℂ)+t*I
    riemannDualGamma s^2*conj (fourthMomentError N s)=fourthMomentError N s := by
  let s := point t
  let U := riemannDualGamma s^2
  have hs : s.re=1/2 := by simp [s,point]
  have hU : U*conj U=1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
    simp [U,norm_pow,norm_riemannDualGamma_critical hs]
  let P := fourthMomentMainTerm N false t
  have hr : fourthMomentError N s=riemannZeta s^2-(P+U*conj P) := by
    rw [fourthMomentError_critical_eq,fourthMomentMainTerm_true_eq_mul_conj]
  change U*conj (fourthMomentError N s)=fourthMomentError N s
  rw [hr,map_sub,map_add,map_mul,conj_conj,mul_sub,mul_add,←mul_assoc,hU,one_mul,
    show U*conj (riemannZeta s^2)=riemannZeta s^2 from riemannDualGamma_sq_mul_conj_zeta_sq hs]
  ring

/-- Exact pointwise separation into the polynomial energy, error energy
and one real mixed product. -/
theorem fourthMoment_critical_energy_identity (N : ℕ) (t : ℝ) :
    ‖riemannZeta ((1/2:ℂ)+t*I)‖^4 =
      ‖fourthMomentMainTerm N false t+fourthMomentMainTerm N true t‖^2+
      ‖fourthMomentError N ((1/2:ℂ)+t*I)‖^2+4*(fourthMomentCrossTerm N ((1/2:ℂ)+t*I)).re := by
  let s := point t
  let U := riemannDualGamma s^2
  let z := riemannZeta s^2
  let P := fourthMomentMainTerm N false t
  let Q := fourthMomentMainTerm N true t
  let R := fourthMomentError N s
  have hz : z=R+(P+Q) := by change _=fourthMomentError N (point t)+_;rw [fourthMomentError_critical_eq];dsimp [P,Q,z,s,point];ring
  have hU : U*conj U=1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
    simp [U,norm_pow,norm_riemannDualGamma_critical (show s.re=1/2 by simp [s,point])]
  have hR : U*conj R=R := fourthMomentError_reflection N t
  have hQ : Q=U*conj P := fourthMomentMainTerm_true_eq_mul_conj N t
  have hm : R*conj Q=conj (R*conj P) := by
    rw [hQ,map_mul,map_mul,conj_conj]
    calc _ = (U*conj R)*(conj U*P) := by rw [hR]
         _ = (U*conj U)*(conj R*P) := by ring
         _ = _ := by rw [hU,one_mul]
  have he (u v : ℂ) : ‖u+v‖^2=‖u‖^2+‖v‖^2+2*(u*conj v).re := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.conj_re,Complex.conj_im];ring
  have hp : ‖riemannZeta s‖^4=‖z‖^2 := by dsimp [z];rw [norm_pow];ring
  rw [fourthMomentCrossTerm_critical_eq]
  change ‖riemannZeta s‖^4=‖P+Q‖^2+‖R‖^2+4*(R*conj P).re
  rw [hp,hz,he,map_add,mul_add,Complex.add_re,hm,Complex.conj_re]
  ring

/-- Integrated fourth-moment identity. The cross term is the real part of
an integral of a holomorphic product. -/
theorem fourthMoment_integral_energy_identity (N : ℕ) (a b : ℝ) :
    (∫ t in a..b,‖riemannZeta ((1/2:ℂ)+t*I)‖^4)=
      (∫ t in a..b,‖fourthMomentMainTerm N false t+fourthMomentMainTerm N true t‖^2)+
      (∫ t in a..b,‖fourthMomentError N ((1/2:ℂ)+t*I)‖^2)+
      4*(∫ t in a..b,fourthMomentCrossTerm N ((1/2:ℂ)+t*I)).re := by
  let M := fun t => fourthMomentMainTerm N false t+fourthMomentMainTerm N true t
  let R := fun t => fourthMomentError N (point t)
  let X := fun t => fourthMomentCrossTerm N (point t)
  have hM : Continuous M := (continuous_fourthMomentMainTerm N false).add (continuous_fourthMomentMainTerm N true)
  have hR : Continuous R := continuous_error N
  have hX : Continuous X := by
    dsimp [X,point];simp_rw [fourthMomentCrossTerm_critical_eq]
    exact hR.mul (Complex.continuous_conj.comp (continuous_fourthMomentMainTerm N false))
  have hm := (hM.norm.pow 2).intervalIntegrable (μ:=volume) a b
  have hr := (hR.norm.pow 2).intervalIntegrable (μ:=volume) a b
  have hx := ((Complex.continuous_re.comp hX).intervalIntegrable (μ:=volume) a b).const_mul (4:ℝ)
  have hre := Complex.reCLM.intervalIntegral_comp_comm (hX.intervalIntegrable (μ:=volume) a b)
  change (∫t in a..b,(X t).re)=(∫t in a..b,X t).re at hre
  have h := intervalIntegral.integral_congr (μ:=volume) (a:=a) (b:=b) (fun t _ => fourthMoment_critical_energy_identity N t)
  apply h.trans
  change (∫t in a..b,‖M t‖^2+‖R t‖^2+4*(X t).re)=_
  rw [intervalIntegral.integral_add (f:=fun t => ‖M t‖^2+‖R t‖^2) (g:=fun t => 4*(X t).re) (hm.add hr) hx,
    intervalIntegral.integral_add (f:=fun t => ‖M t‖^2) (g:=fun t => ‖R t‖^2) hm hr,intervalIntegral.integral_const_mul,hre]

end AnalyticNumberTheory.RiemannZeta
