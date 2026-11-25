import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

/-! # Removing the full order of a finite set of zeros of an entire function -/
noncomputable section
open Complex Finset Filter Set
open scoped Topology Classical
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

private theorem finite_order_of_entire {f : ℂ→ℂ} (hf : Differentiable ℂ f) (hn : f≠0) (p : ℂ) :
    analyticOrderAt f p≠⊤ := by
  obtain ⟨w,hw⟩ := Function.ne_iff.mp hn
  apply hf.differentiableOn.analyticOnNhd isOpen_univ |>.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ w) (mem_univ p)
  rw [(hf.analyticAt w).analyticOrderAt_eq_zero.mpr hw];simp

set_option maxHeartbeats 500000 in
/-- Divide an entire function by the full linear power at p, filling in the
removable value. The resulting entire function is nonzero at p. -/
theorem exists_entire_remove_zero {f : ℂ→ℂ} (hf : Differentiable ℂ f) (hn : f≠0) (p : ℂ) :
    ∃ u : ℂ→ℂ,Differentiable ℂ u ∧ u p≠0 ∧
      ∀ z,f z=(z-p)^(analyticOrderNatAt f p)*u z := by
  let m := analyticOrderNatAt f p
  obtain ⟨v,hv,hvp,he⟩ := ((hf.analyticAt p).analyticOrderNatAt_eq_iff (finite_order_of_entire hf hn p)).mp rfl
  let u (z : ℂ) := if z=p then v z else f z/(z-p)^m
  have hu : u=ᶠ[𝓝 p]v := by
    filter_upwards [he] with z hz
    by_cases h : z=p
    · simp [u,h]
    · simp only [u,if_neg h]
      apply (div_eq_iff (pow_ne_zero _ (sub_ne_zero.mpr h))).mpr
      simpa only [smul_eq_mul,mul_comm] using hz
  refine ⟨u,?_,by simpa [u] using hvp,?_⟩
  · intro z
    by_cases h : z=p
    · subst z;exact hv.differentiableAt.congr_of_eventuallyEq hu
    · have hh : u=ᶠ[𝓝 z](fun w => f w/(w-p)^m) := by
        filter_upwards [eventually_ne_nhds h] with w hw;simp [u,hw]
      have hden : DifferentiableAt ℂ (fun w : ℂ => (w-p)^m) z := by fun_prop
      exact ((hf z).div hden (pow_ne_zero m (sub_ne_zero.mpr h))).congr_of_eventuallyEq hh
  · intro z;by_cases h : z=p
    · subst z;simpa [u,m,smul_eq_mul] using he.self_of_nhds
    · dsimp only [u];rw [if_neg h];field_simp [sub_ne_zero.mpr h];rfl

/-- Factor the exact multiplicities of finitely many zeros, leaving an entire
function which is nonvanishing on K when the finite set contains all its zeros. -/
theorem factor_entire_finite_zeros (K : Set ℂ) (Z : Finset ℂ) {f : ℂ→ℂ}
    (hf : Differentiable ℂ f) (hn : f≠0) (hZ : ∀ z∈K,f z=0 → z∈Z) :
    ∃ u : ℂ→ℂ,Differentiable ℂ u ∧ (∀ z∈K,u z≠0) ∧
      ∀ z,f z=(∏ p∈Z,(z-p)^(analyticOrderNatAt f p))*u z := by
  induction Z using Finset.induction_on generalizing f with
  | empty =>
    refine ⟨f,hf,(fun z hz h => Finset.notMem_empty z (hZ z hz h)),?_⟩
    simp
  | @insert p Z hp ih =>
    obtain ⟨v,hv,hvp,hf'⟩ := exists_entire_remove_zero hf hn p
    have hv₀ : v≠0 := fun h => hvp (by rw [h];rfl)
    have hZ' (z : ℂ) (hz : z∈K) (h : v z=0) := (mem_insert.mp (hZ z hz (by rw [hf' z,h,mul_zero]))).resolve_left
      (fun he => hvp (he ▸ h))
    obtain ⟨u,hu,hu₀,hv'⟩ := ih hv hv₀ hZ'
    have hord (t : ℂ) (ht : t∈Z) : analyticOrderNatAt f t=analyticOrderNatAt v t := by
      let P (z : ℂ) := (z-p)^(analyticOrderNatAt f p)
      have hP : AnalyticAt ℂ P t := by dsimp [P];fun_prop
      have hP₀ : P t≠0 := pow_ne_zero _ (sub_ne_zero.mpr (fun he => hp (he ▸ ht)))
      have horder := hP.analyticOrderAt_eq_zero.mpr hP₀
      have hfg : f=P*v := funext hf'
      have hm := analyticOrderAt_mul hP (hv.analyticAt t)
      rw [horder,zero_add,←hfg] at hm
      exact congrArg ENat.toNat hm
    refine ⟨u,hu,hu₀,?_⟩;intro z
    rw [prod_insert hp,hf' z,hv' z]
    rw [prod_congr rfl (fun t ht => congrArg (fun n : ℕ => (z-t)^n) (hord t ht))]
    ring

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
