import AnalyticNumberTheory.RiemannZeta.MontgomeryDetectorKernel
import AnalyticNumberTheory.PrimeDistribution.InghamZeroDetector

/-!
# Montgomery's variable-length detector for zeta

Once the ordinate dominates the explicit correction from the pole at
one, the same finite polynomial and sixth-power critical convolution
work for every zero. There is no ordering condition on the two cutoffs.
-/

open Real Complex Filter Finset Set MeasureTheory
open scoped Topology ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- The unit coefficient and the mollifier tail in a Riesz mean, also
valid when the mollifier is longer than the Riesz cutoff. -/
theorem inghamRieszSum_six_split_independent {X : ℕ} (hX : 1≤X) {Y : ℝ} (hY : 1≤Y) (ρ : ℂ) :
    inghamRieszSum X 6 Y ρ=(inghamRieszWeight 6 Y 1:ℂ)+
      ∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ) := by
  by_cases h : (X:ℝ)≤Y
  · exact inghamRieszSum_six_split hX h ρ
  have hn : ⌊Y⌋₊≤X := by exact_mod_cast (Nat.floor_le (by linarith : 0≤Y)).trans (le_of_not_ge h)
  rw [Finset.Ioc_eq_empty_of_le hn,sum_empty,add_zero,inghamRieszSum]
  rw [sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,(Nat.one_le_floor_iff _).mpr hY⟩)]
  · simp [inghamDetectorCoeff_small hX]
  · intro n hn' hn₁
    simp [inghamDetectorCoeff_small ((mem_Icc.mp hn').2.trans hn),hn₁]

/-- At very low heights the pole at one may affect the detector. Above
this explicit ordinate its contribution is at most one sixteenth. -/
theorem montgomery_zeta_pole_correction {X : ℕ} {σ Y : ℝ} {ρ : ℂ} (hY : 1≤Y)
    (hβ : σ≤ρ.re) (hβ' : ρ.re≤1) (hγ : 96*Y^(1-σ)*(1+Real.log Y)^3≤ρ.im) :
    ‖6/(ρ-1)*(inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ)‖≤1/16 := by
  have hYp : 0<Y := by linarith
  have hL : 0<1+Real.log Y := by linarith [Real.log_nonneg hY]
  have hden : 96*Y^(1-σ)*(1+Real.log Y)^3≤‖ρ-1‖ :=
    hγ.trans (by simpa using Complex.im_le_norm (ρ-1))
  have hp : 0<‖ρ-1‖ := (show 0<96*Y^(1-σ)*(1+Real.log Y)^3 by positivity).trans_le hden
  have hpow := Real.rpow_le_rpow_of_exponent_le hY (by linarith : 1-ρ.re≤1-σ)
  rw [norm_mul,norm_div,show ‖(6:ℂ)‖=(6:ℝ) by norm_num]
  apply (mul_le_mul_of_nonneg_left (norm_inghamRieszSum_sub hY hβ') (by positivity : 0≤6/‖ρ-1‖)).trans
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith only [hden,mul_le_mul_of_nonneg_right hpow (pow_nonneg hL.le 3)]

private theorem montgomery_riesz_dichotomy {X : ℕ} {σ Y : ℝ} {ρ : ℂ} (hX : 1≤X) (hY : 16≤Y)
    (hσ : 3/4≤σ) (hβ : σ≤ρ.re) (hβ' : ρ.re≤1) (hγ₀ : 1≤ρ.im)
    (hγ : 96*Y^(1-σ)*(1+Real.log Y)^3≤ρ.im) :
    1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨ 1/4≤‖inghamDetectorRight X Y ρ‖ := by
  have hYp : 0<Y := by linarith
  have hne : ρ≠1 := by intro h;rw [h,one_im] at hγ₀;linarith
  let S := ∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)
  let E := 6/(ρ-1)*(inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ)
  let W : ℂ := (inghamRieszWeight 6 Y 1:ℂ)
  have heq : inghamDetectorRight X Y ρ=W+S+E := by
    rw [inghamDetectorRight_eq hYp (by linarith) hne]
    exact congrArg (fun z => z+E) (inghamRieszSum_six_split_independent hX (by linarith) ρ)
  have hW : 1/2≤‖W‖ := by
    have hrec : 1/Y≤1/16 := by gcongr
    have hbase : 15/16≤1-1/Y := by linarith
    have hpow : (15/16:ℝ)^6≤(1-1/Y)^6 := by gcongr
    change _≤‖((inghamRieszWeight 6 Y 1:ℝ):ℂ)‖
    rw [Complex.norm_real,Real.norm_eq_abs,inghamRieszWeight,Nat.cast_one,abs_of_nonneg (by positivity : 0≤(1-1/Y)^6)]
    norm_num at hpow ⊢;linarith
  have hE : ‖E‖≤1/16 := montgomery_zeta_pole_correction (by linarith) hβ hβ' hγ
  change 1/8≤‖S‖ ∨ _
  by_cases hS : 1/8≤‖S‖
  · exact Or.inl hS
  right
  have htri : ‖W‖≤‖inghamDetectorRight X Y ρ‖+‖E‖+‖S‖ := by
    calc _ = ‖(inghamDetectorRight X Y ρ-E)-S‖ := by rw [heq];abel_nf
         _ ≤ ‖inghamDetectorRight X Y ρ-E‖+‖S‖ := norm_sub_le ..
         _ ≤ _ := add_le_add (norm_sub_le ..) le_rfl
  linarith

/-- A zero above the explicit polar cutoff is detected either by a finite
polynomial of lengths `X,Y`, or by every sufficiently long symmetric
truncation of the sixth-power convolution on the critical line. -/
theorem montgomery_zeta_zero_detector :
    ∃ A : ℝ,0<A ∧ ∀ {X : ℕ} {σ Y : ℝ} {ρ : ℂ},1≤X → 16≤Y → 3/4≤σ → σ≤ρ.re → ρ.re<1 →
      96*Y^(1-σ)*(1+Real.log Y)^3≤ρ.im → riemannZeta ρ=0 →
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨
      ∀ᶠ R : ℝ in atTop,1/(A*Y^(1/2-σ))≤∫ t in -R..R,
        (1/(1+|t-ρ.im|)^6)*‖riemannZeta ((1/2:ℂ)+t*I)‖*
          ‖dirichletPoly (fun n => (μ n:ℂ)) X ((1/2:ℂ)+t*I)‖ := by
  let a : ℂ := 720/(2*π)
  refine ⟨8*(‖a‖+1)*3645,by positivity,?_⟩
  intro X σ Y ρ hX hY hσ hβ hβ' hγ hz
  have hy : 1≤Y := by linarith
  have hYp : 0<Y := by linarith
  have hlog : 1≤1+Real.log Y := by linarith [Real.log_nonneg hy]
  have hγ' : 1≤ρ.im := by
    have h := mul_le_mul (Real.one_le_rpow hy (by linarith : 0≤1-σ)) (one_le_pow₀ hlog (n:=3)) zero_le_one (by positivity)
    nlinarith only [h,hγ]
  rcases montgomery_riesz_dichotomy hX hY hσ hβ hβ'.le hγ' hγ with h | h
  · exact Or.inl h
  right
  rw [inghamDetectorRight_eq_critical X hy (by linarith) hβ' hγ' hz] at h
  let s (t : ℝ) := (1/2:ℂ)+t*I
  let g (t : ℝ) := 1/(1+|t-ρ.im|)^6*‖riemannZeta (s t)‖*‖rieszMobiusPolynomial X (s t)‖
  have hs : Continuous s := by dsimp [s];fun_prop
  have hζ : Continuous (fun t => riemannZeta (s t)) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_riemannZeta (by intro he;have := congrArg Complex.re he;norm_num [s] at this)).continuousAt.comp hs.continuousAt
  have hg : Continuous g := by
    apply Continuous.mul _ ((differentiable_rieszMobiusPolynomial X).continuous.comp hs).norm
    apply Continuous.mul _ hζ.norm
    exact continuous_const.div ((continuous_const.add ((continuous_id.sub (continuous_const (y:=ρ.im))).abs)).pow 6) (fun t => by change (1+|t-ρ.im|)^6≠0;positivity)
  have hker (v : ℝ) := norm_montgomery_zeta_integrand hγ' (hσ.trans hβ) hβ'.le X hYp v
  have H := eventually_convolution_large_of_integral (G:=g) (γ:=ρ.im) (a:=a) hg
    (fun v => by simpa [g,s,rieszMobiusPolynomial] using hker v) h
  filter_upwards [H,eventually_ge_atTop (0:ℝ)] with R hR hr
  have hG : 0≤∫ t in -R..R,g t := intervalIntegral.integral_nonneg (by linarith) (fun t _ => by dsimp [g];positivity)
  have hp := Real.rpow_le_rpow_of_exponent_le hy (by linarith : 1/2-ρ.re≤1/2-σ)
  apply (div_le_iff₀ (by positivity)).mpr
  change 1≤(∫ t in -R..R,g t)*(8*(‖a‖+1)*3645*Y^(1/2-σ))
  have hcoef := mul_le_mul (show ‖a‖≤‖a‖+1 by linarith) hp (Real.rpow_pos_of_pos hYp _).le (by positivity)
  nlinarith only [hR,mul_le_mul_of_nonneg_right hcoef hG]

end AnalyticNumberTheory.PrimeDistribution
