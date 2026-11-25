import AnalyticNumberTheory.RiemannZeta.HurwitzFirstCorrection
import AnalyticNumberTheory.RiemannZeta.HurwitzLogFreeApproximation

/-!
# The corrected Hurwitz Riemann–Siegel formula in the height variable

The error is uniform in the real shift and of order t^(-3/4) throughout
the balanced range t≥8π. Both polynomials have their original sharp
cutoffs, also at integral values of the saddle.
-/
noncomputable section
open Real Complex Set Filter
namespace AnalyticNumberTheory.RiemannZeta

/-- Uniform bound for the regularized first correction coefficient. -/
theorem riemannSiegelCorrection_bounded :
    ∃ B : ℝ,0<B ∧ ∀ c∈Icc (0:ℝ) 2, |riemannSiegelCorrection c|≤B := by
  obtain ⟨M,hM⟩ := (isCompact_Icc (a:=(0:ℝ)) (b:=2)).exists_bound_of_continuousOn continuous_riemannSiegelCorrection.continuousOn
  exact ⟨max 1 M,zero_lt_one.trans_le (le_max_left _ _),fun c hc => (hM c hc).trans (le_max_right _ _)⟩

theorem hurwitzSaddleFraction_mem {a x : ℝ} (h : a≤x) : hurwitzSaddleFraction a x∈Icc (0:ℝ) 1 :=
  ⟨sub_nonneg.mpr (Nat.floor_le (sub_nonneg.mpr h)),(by dsimp [hurwitzSaddleFraction];linarith [Nat.lt_floor_add_one (x-a)])⟩

theorem norm_hurwitzFirstCorrection {a x : ℝ} {s : ℂ} (hx : 0<x) :
    ‖hurwitzFirstCorrection a x s‖=x^(-s.re)*|riemannSiegelCorrection (x+hurwitzSaddleFraction a x-⌊x⌋₊)| := by
  unfold hurwitzFirstCorrection
  rw [norm_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_real,Real.norm_eq_abs,Complex.neg_re]

/-- The first corrected equation for every positive balanced cutoff x≥2. -/
theorem hurwitzZeta_first_correction_balanced : ∃ C : ℝ,0<C ∧ ∀ {a x : ℝ} {s : ℂ},
    a∈Ioc (0:ℝ) 1 → 2≤x → s.re=1/2 → s.im=2*Real.pi*x^2 →
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a x s-
      hurwitzFirstCorrection a x s‖≤C*x^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hh⟩ := hurwitzZeta_first_correction
  obtain ⟨B,hB,hbound⟩ := riemannSiegelCorrection_bounded
  refine ⟨max C (1024*(604+B)),hC.trans_le (le_max_left _ _),?_⟩
  intro a x s ha hx hσ ht
  have hx' : 0<x := by linarith
  have hM := Real.rpow_nonneg hx'.le (-(3/2:ℝ))
  by_cases hl : 1024≤x
  · exact (hh ha hl hσ ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
  have h₀ := hurwitzZeta_logFree_sharp_afe (s:=s) ha hx le_rfl (by rw [hσ];norm_num)
    (show |s.im|=2*Real.pi*x*x by rw [ht,abs_of_nonneg (by positivity)];ring)
  have hf := hurwitzSaddleFraction_mem (show a≤x by linarith [ha.2])
  have hd := hbound (x+hurwitzSaddleFraction a x-⌊x⌋₊) ⟨by linarith [Nat.floor_le hx'.le,hf.1],by linarith [Nat.lt_floor_add_one x,hf.2]⟩
  have he := norm_hurwitzFirstCorrection (s:=s) (a:=a) hx'
  rw [hσ] at h₀ he
  apply (norm_sub_le _ _).trans
  apply (add_le_add h₀ (he.le.trans (mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hx'.le _)))).trans
  have hp : x^(-(1/2:ℝ))=x^(-(3/2:ℝ))*x := by rw [←Real.rpow_add_one hx'.ne'];norm_num
  rw [hp]
  calc _ = (x*(604+B))*x^(-(3/2:ℝ)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (not_le.mp hl).le (by positivity)).trans (le_max_right _ _)) hM

/-- Uniform sharp Hurwitz expansion at height t, including the first
oscillatory correction and an absolute O(t^(-3/4)) error. -/
theorem hurwitzZeta_first_correction_height : ∃ C : ℝ,0<C ∧ ∀ {a t : ℝ},
    a∈Ioc (0:ℝ) 1 → 8*Real.pi≤t →
    let x := Real.sqrt (t/(2*Real.pi))
    let s := (1/2:ℂ)+(t:ℂ)*I
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a x s-
      hurwitzFirstCorrection a x s‖≤C*t^(-(3/4:ℝ)) := by
  obtain ⟨C,hC,h⟩ := hurwitzZeta_first_correction_balanced
  refine ⟨C*(2*Real.pi)^(3/4:ℝ),by positivity,?_⟩
  intro a t ha ht x s
  have hπ : 0<2*Real.pi := by positivity
  have ht' : 0<t := (by positivity : 0<8*Real.pi).trans_le ht
  have hx2 : x^2=t/(2*Real.pi) := Real.sq_sqrt (by positivity)
  have hx : 2≤x := by
    have h₄ : 4≤t/(2*Real.pi) := (le_div_iff₀ hπ).mpr (by linarith)
    nlinarith [Real.sqrt_nonneg (t/(2*Real.pi))]
  apply (h (s:=s) ha hx (by simp [s]) (by dsimp [s];simp only [add_im,div_ofNat_im,one_im,zero_div,mul_I_im,ofReal_re,zero_add];rw [hx2];field_simp)).trans_eq
  dsimp only [x]
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul (div_nonneg ht'.le hπ.le),show (1/2:ℝ)*(-(3/2))= -(3/4) by norm_num,
    Real.div_rpow ht'.le hπ.le,Real.rpow_neg hπ.le,div_inv_eq_mul];ring

end AnalyticNumberTheory.RiemannZeta
