import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Integrating a Gaussian error and two exponential tails

These estimates apply when the local approximation has polynomially
weighted Gaussian error and the outer parts have decay on scale 1/b.
-/
noncomputable section
open Real Complex Set MeasureTheory
namespace AnalyticNumberTheory.AnalyticTools

private def gaussianErrorWeight (v : ℝ) := (1+v^4)*Real.exp (-v^2/16)

private theorem gaussianErrorWeight_integrable : Integrable gaussianErrorWeight := by
  have h₀ := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/16)
  have h₄ := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/16) (by norm_num : (-1:ℝ)<4)
  apply (h₀.add h₄).congr
  filter_upwards with v
  dsimp only [gaussianErrorWeight];norm_num [show -(1/16:ℝ)*v^2= -v^2/16 by ring];ring

private theorem integral_abs_exponential {a : ℝ} (ha : 0<a) :
    (∫ v : ℝ, Real.exp (-a*|v|))=2/a := by
  rw [integral_comp_abs (f:=fun v : ℝ => Real.exp (-a*v)),integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
  simp;ring

/-- The integral of a pointwise approximation with a Gaussian core and two
exponential tails has error bounded by a constant times P/x. -/
theorem norm_integral_sub_le_of_gaussian_error {D : ℝ} (hD : 0<D) :
    ∃ C : ℝ,0<C ∧ ∀ {x b P : ℝ}, 0<x → x/2≤b → 0≤P →
      ∀ {F G : ℝ → ℂ}, AEStronglyMeasurable F → Integrable G →
      (∀ v : ℝ, ‖F v-G v‖≤D*(P/x)*((1+v^4)*Real.exp (-v^2/16))+
        D*P*Real.exp (-(b/64)*|v|)) →
      Integrable F ∧ ‖(∫ v : ℝ,F v)-(∫ v : ℝ,G v)‖≤C*(P/x) := by
  let K := ∫ v : ℝ,gaussianErrorWeight v
  have hK : 0≤K := integral_nonneg (fun v => by unfold gaussianErrorWeight;positivity)
  refine ⟨D*(K+256),by positivity,?_⟩
  intro x b P hx hb hP F G hF hG hdom
  have hb' : 0<b := by linarith
  let H (v : ℝ) := Real.exp (-(b/64)*|v|)
  have hi : (∫ v : ℝ,H v)=128/b := by rw [show (∫ v : ℝ,H v)=2/(b/64) from integral_abs_exponential (by positivity)];ring
  have hH : Integrable H := by
    by_contra hn
    rw [integral_undef hn] at hi
    exact (show 0<128/b by positivity).ne hi
  let g (v : ℝ) := D*(P/x)*gaussianErrorWeight v+D*P*H v
  have hig : Integrable g := (gaussianErrorWeight_integrable.const_mul _).add (hH.const_mul _)
  have hdiff : Integrable (fun v => F v-G v) := hig.mono' (hF.sub hG.aestronglyMeasurable) (Filter.Eventually.of_forall hdom)
  have hiF : Integrable F := by exact (hdiff.add hG).congr (Filter.Eventually.of_forall fun v => sub_add_cancel (F v) (G v))
  refine ⟨hiF,?_⟩
  rw [←integral_sub hiF hG]
  apply (norm_integral_le_integral_norm _).trans ((integral_mono_ae hdiff.norm hig (Filter.Eventually.of_forall hdom)).trans _)
  dsimp [g];rw [integral_add (gaussianErrorWeight_integrable.const_mul _) (hH.const_mul _),integral_const_mul,integral_const_mul,hi]
  change D*(P/x)*K+D*P*(128/b)≤D*(K+256)*(P/x)
  have htail : 128/b≤256/x := (div_le_div_iff₀ hb' hx).mpr (by linarith)
  calc _ ≤ D*(P/x)*K+D*P*(256/x) := by gcongr
       _ = _ := by ring

end AnalyticNumberTheory.AnalyticTools
