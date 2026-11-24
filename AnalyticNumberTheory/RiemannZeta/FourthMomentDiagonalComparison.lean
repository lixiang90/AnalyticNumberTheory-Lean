import AnalyticNumberTheory.RiemannZeta.FourthMomentShortPolynomials
import AnalyticNumberTheory.RiemannZeta.FourthMomentFrequencies
import AnalyticNumberTheory.AnalyticTools.SquareMeanComparison

/-!
# Comparison of the fourth zeta moment with its arithmetic diagonal

In the unweighted polynomials of length `⌊δT⌋`, the mean-square off-diagonal
costs at most a constant times `δ` times the diagonal. The mixed term and the
mean-square approximation error have lower logarithmic order.
-/

open Complex Real MeasureTheory Finset Set Filter
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.RiemannZeta

/-- Harmonic sum of the squared divisor function in the fourth-moment diagonal. -/
noncomputable def fourthMomentDiagonal (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (n.divisors.card:ℝ)^2/(n:ℝ)

/-- Integral of the squared sum of the two unweighted main terms, separating the
two equal diagonals and the oscillatory cross term. -/
theorem integral_fourthMomentMainTerms_sq (N : ℕ) (a b : ℝ) :
    (∫ t in a..b, ‖fourthMomentMainTerm N false t+fourthMomentMainTerm N true t‖^2) =
      2*(∫ t in a..b, ‖divisorPolynomial N ((1/2:ℂ)+t*I)‖^2) +
      2*(∫ t in a..b, fourthMomentMainTerm N false t*conj (fourthMomentMainTerm N true t)).re := by
  let A := fourthMomentMainTerm N false
  let B := fourthMomentMainTerm N true
  let D (t : ℝ) := divisorPolynomial N ((1/2:ℂ)+t*I)
  have hA := continuous_fourthMomentMainTerm N false
  have hB := continuous_fourthMomentMainTerm N true
  have hD : Continuous D := by simpa only [D,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using divisorPolynomial_continuous N (1/2)
  have hc : Continuous (fun t => A t*conj (B t)) := hA.mul (Complex.continuous_conj.comp hB)
  have he (t : ℝ) : ‖A t+B t‖^2 = 2*‖D t‖^2+2*(A t*conj (B t)).re := by
    have h (z w : ℂ) : ‖z+w‖^2 = ‖z‖^2+‖w‖^2+2*(z*conj w).re := by
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.conj_re,Complex.conj_im]
      ring
    rw [h,norm_fourthMomentMainTerm_eq N false t,norm_fourthMomentMainTerm_eq N true t]
    dsimp only [D]; ring
  have hr := Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) a b)
  change (∫ t in a..b, (A t*conj (B t)).re) = (∫ t in a..b, A t*conj (B t)).re at hr
  change (∫ t in a..b, ‖A t+B t‖^2) = _
  simp_rw [he]
  rw [intervalIntegral.integral_add (f := fun t => 2*‖D t‖^2) (g := fun t => 2*(A t*conj (B t)).re)
    (((hD.norm.pow 2).intervalIntegrable ..).const_mul _) (((Complex.continuous_re.comp hc).intervalIntegrable ..).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hr]

set_option maxHeartbeats 800000 in
/-- Uniform numerical comparison with the arithmetic diagonal. The adjustable parameters
are the polynomial length `δT` and the Young-inequality parameter `η`. -/
theorem fourthMoment_dyadic_diagonal_comparison {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hδπ : δ ≤ 1/(4*π)) :
    ∃ C > (0:ℝ), ∀ {T η : ℝ}, 2 ≤ T → 2 ≤ δ*T → 0 < η →
      let N := ⌊δ*T⌋₊
      let Z := ∫ t in T..2*T, ‖riemannZeta ((1/2:ℂ)+t*I)‖^4
      |Z-2*T*fourthMomentDiagonal N| ≤ η*Z +
        (1+1/η)*C*T*(1+Real.log T)^3 + 4*π*δ*T*fourthMomentDiagonal N := by
  obtain ⟨C,hC,h⟩ := zeta_sq_sub_short_mainTerms_mean_sq hδ hδ₁
  let A := 64+8/Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C+2*A,by positivity,?_⟩
  intro T η hT hx hη
  let N := ⌊δ*T⌋₊
  let D := fourthMomentDiagonal N
  let p (t : ℝ) := divisorPolynomial N ((1/2:ℂ)+t*I)
  let M (t : ℝ) := fourthMomentMainTerm N false t+fourthMomentMainTerm N true t
  let z (t : ℝ) := riemannZeta ((1/2:ℂ)+t*I)
  let Z := ∫ t in T..2*T, ‖z t‖^4
  let L := (1+Real.log T)^3
  have hT0 : 0 < T := by linarith
  have hab : T ≤ 2*T := by linarith
  have hN : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hNδ : (N:ℝ) ≤ δ*T := Nat.floor_le (by positivity)
  have hNT : (N:ℝ) ≤ T := hNδ.trans (mul_le_of_le_one_left hT0.le hδ₁)
  have hNπ : (N:ℝ) ≤ T/(4*π) := hNδ.trans ((mul_le_mul_of_nonneg_right hδπ hT0.le).trans_eq (by ring))
  have hD0 : 0 ≤ D := by unfold D fourthMomentDiagonal; exact Finset.sum_nonneg (fun n _ => by positivity)
  have hlog := Real.log_nonneg (by exact_mod_cast hN : 1 ≤ (N:ℝ))
  have hlogT := Real.log_nonneg (by linarith : 1 ≤ T)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : Continuous M := (continuous_fourthMomentMainTerm N false).add (continuous_fourthMomentMainTerm N true)
  have hpow (t : ℝ) : ‖z t^2‖^2 = ‖z t‖^4 := by rw [norm_pow]; ring
  have he := abs_integral_norm_sq_sub_le hab hη (f := fun t => z t^2) (g := M)
    (continuous_riemannZeta_half.pow 2).continuousOn hM.continuousOn
  have hiz : (∫ t in T..2*T, ‖z t^2‖^2) = Z := intervalIntegral.integral_congr (fun t _ => hpow t)
  rw [hiz] at he
  change |Z-(∫ t in T..2*T, ‖M t‖^2)| ≤ η*Z+(1+1/η)*(∫ t in T..2*T, ‖z t^2-M t‖^2) at he
  have hh := h hT hx
  change (∫ t in T..2*T, ‖z t^2-M t‖^2) ≤ C*T*L at hh
  have h₁ := he.trans (add_le_add (le_refl (η*Z)) (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1+1/η)))
  have hp := dirichletPoly_mean_sq_asymp (fun n => (n.divisors.card:ℂ)) N (1/2) hab
  simp only [Real.norm_eq_abs,Complex.norm_natCast,show -2*(1/2:ℝ) = -1 by norm_num,Real.rpow_neg_one,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,← div_eq_mul_inv,show 2*T-T=T by ring] at hp
  change |(∫ t in T..2*T, ‖p t‖^2)-T*D| ≤ 2*π*N*D at hp
  let X := ∫ t in T..2*T, fourthMomentMainTerm N false t*conj (fourthMomentMainTerm N true t)
  have hc : |X.re| ≤ A*T*L := by
    apply (Complex.abs_re_le_norm X).trans
    apply (norm_integral_fourthMomentMainTerm_mul_conj_le hN hT hNπ).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hNT hA.le)
      (pow_le_pow_left₀ (by linarith) (by linarith [Real.log_le_log (by exact_mod_cast hN : 0 < (N:ℝ)) hNT]) 3)
      (by positivity) (by positivity)
  have hm := integral_fourthMomentMainTerms_sq N T (2*T)
  change (∫ t in T..2*T, ‖M t‖^2) = 2*(∫ t in T..2*T, ‖p t‖^2)+2*X.re at hm
  have h₂ : |(∫ t in T..2*T, ‖M t‖^2)-2*T*D| ≤ 4*π*δ*T*D+2*A*T*L := by
    rw [hm]
    have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNδ Real.pi_pos.le) hD0
    apply abs_le.mpr
    constructor <;> linarith only [(abs_le.mp hp).1,(abs_le.mp hp).2,(abs_le.mp hc).1,(abs_le.mp hc).2,hn]
  change |Z-2*T*D| ≤ η*Z+(1+1/η)*(C+2*A)*T*L+4*π*δ*T*D
  apply (abs_sub_le _ (∫ t in T..2*T, ‖M t‖^2) _).trans
  have H := add_le_add h₁ h₂
  have hn : 0 ≤ (1/η)*(2*A*T*L) := by positivity
  linarith only [H,hn]

end AnalyticNumberTheory.RiemannZeta
