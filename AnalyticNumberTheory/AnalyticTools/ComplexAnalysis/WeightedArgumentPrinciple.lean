import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.EntireZeroFactors
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleIntegrals

/-! # The argument principle with an entire weight on a rectangle -/
noncomputable section
open Complex Set Finset MeasureTheory
open scoped Classical
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Integrate an entire weight times the logarithmic derivative around the
positively oriented rectangle. Each interior zero contributes its analytic
multiplicity times the value of the weight. -/
theorem weighted_argument_principle_rect_entire {f g : ℂ→ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {a b c d : ℝ} (hab : a<b) (hcd : c<d)
    (Z : Finset ℂ) (hZ_int : ∀ p∈Z,p.re∈Ioo a b ∧ p.im∈Ioo c d)
    (hZ_all : ∀ z∈Icc a b ×ℂ Icc c d,f z=0 → z∈Z) :
    rectangleBoundary (fun z => g z*(deriv f z/f z)) ⟨a,c⟩ ⟨b,d⟩ =
      2*Real.pi*I*∑ p∈Z,(analyticOrderNatAt f p:ℂ)*g p := by
  let K := Icc a b ×ℂ Icc c d
  have hn : f≠0 := by
    intro he
    have hin := hZ_int ⟨a,c⟩ (hZ_all ⟨a,c⟩ ⟨⟨le_rfl,hab.le⟩,⟨le_rfl,hcd.le⟩⟩ (by rw [he];rfl))
    exact (lt_irrefl a) hin.1.1
  obtain ⟨u,hu,hun,hfactor⟩ := factor_entire_finite_zeros K Z hf hn hZ_all
  let m (p : ℂ) := analyticOrderNatAt f p
  let P (z : ℂ) := ∏ p∈Z,(z-p)^(m p)
  let F (z : ℂ) := g z*(deriv f z/f z)
  let G (z : ℂ) := g z*(deriv u z/u z)
  let L (p z : ℂ) := ((m p:ℂ)*g z)/(z-p)
  have hG (z : ℂ) (hz : z∈K) : DifferentiableAt ℂ G z :=
    (hg z).mul (((hu.analyticAt z).deriv.differentiableAt).div (hu z) (hun z hz))
  have hL (z : ℂ) (hz : z∉Z) (p) (hp : p∈Z) : ContinuousAt (L p) z :=
    (continuousAt_const.mul (hg z).continuousAt).div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr (fun he => hz (he ▸ hp)))
  have he (z : ℂ) (hz : z∈K) (hnot : z∉Z) : F z=G z+∑ p∈Z,L p z := by
    have hp (p) (hp : p∈Z) : z-p≠0 := sub_ne_zero.mpr (fun h => hnot (h ▸ hp))
    have hP : DifferentiableAt ℂ P z := by dsimp [P];fun_prop
    have hne : P z≠0 := prod_ne_zero_iff.mpr (fun p h => pow_ne_zero _ (hp p h))
    have hfg : f=P*u := funext hfactor
    have h1 : logDeriv f z=logDeriv P z+logDeriv u z := by
      rw [hfg];exact logDeriv_mul z hne (hun z hz) hP (hu z)
    have h2 : logDeriv P z=∑ p∈Z,(m p:ℂ)/(z-p) := by
      dsimp only [P]
      rw [logDeriv_fun_prod (f:=fun p s : ℂ => (s-p)^(m p)) (fun p h => pow_ne_zero _ (hp p h)) (fun p _ => by fun_prop)]
      apply sum_congr rfl;intro p _
      rw [logDeriv_fun_pow (f:=fun s : ℂ => s-p) (by fun_prop),logDeriv_apply,
        show deriv (fun s : ℂ => s-p) z=1 from ((hasDerivAt_id z).sub_const p).deriv];ring
    change g z*logDeriv f z=g z*logDeriv u z+∑ p∈Z,L p z
    rw [h1,h2,mul_add,mul_sum,add_comm]
    congr 1
    apply sum_congr rfl;intro p _;dsimp [L];ring
  have edge {s t : ℝ} (path : ℝ→ℂ) (hpath : Continuous path)
      (hm : ∀ v∈uIcc s t,path v∈K ∧ path v∉Z) :
      (∫ v in s..t,F (path v))=(∫ v in s..t,G (path v))+∑ p∈Z,∫ v in s..t,L p (path v) := by
    have hg' : ContinuousOn (fun v => G (path v)) (uIcc s t) :=
      fun v hv => ((hG _ (hm v hv).1).continuousAt.comp hpath.continuousAt).continuousWithinAt
    have hl' (p) (hp : p∈Z) : ContinuousOn (fun v => L p (path v)) (uIcc s t) :=
      fun v hv => ((hL _ (hm v hv).2 p hp).comp hpath.continuousAt).continuousWithinAt
    calc _ = ∫ v in s..t,G (path v)+∑ p∈Z,L p (path v) :=
               intervalIntegral.integral_congr (fun v hv => he _ (hm v hv).1 (hm v hv).2)
         _ = _ := by rw [intervalIntegral.integral_add hg'.intervalIntegrable
                            (continuousOn_finsetSum Z hl').intervalIntegrable,
                          intervalIntegral.integral_finsetSum (fun p hp => (hl' p hp).intervalIntegrable)]
  have no_boundary (z : ℂ) (h : z.re=a ∨ z.re=b ∨ z.im=c ∨ z.im=d) : z∉Z := by
    intro hz
    obtain ⟨⟨ha,hb⟩,hc,hd⟩ := hZ_int z hz
    rcases h with h|h|h|h <;> linarith
  have horizontal (v : ℝ) (hv : v=c ∨ v=d) := edge (s:=a) (t:=b)
    (fun x : ℝ => (x:ℂ)+v*I) (by fun_prop) (by
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      constructor
      · rcases hv with rfl|rfl <;> simpa [K,Complex.mem_reProdIm,hcd.le] using hx
      · apply no_boundary;simpa using Or.inr (Or.inr hv))
  have vertical (v : ℝ) (hv : v=a ∨ v=b) := edge (s:=c) (t:=d)
    (fun y : ℝ => (v:ℂ)+y*I) (by fun_prop) (by
      intro y hy
      rw [uIcc_of_le hcd.le] at hy
      constructor
      · rcases hv with rfl|rfl <;> simpa [K,Complex.mem_reProdIm,hab.le] using hy
      · apply no_boundary
        rcases hv with rfl|rfl
        · exact Or.inl (by simp)
        · exact Or.inr (Or.inl (by simp)))
  have hz : rectangleBoundary G ⟨a,c⟩ ⟨b,d⟩=0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G _ _ (fun z h => (hG z (by
      simpa only [uIcc_of_le hab.le,uIcc_of_le hcd.le,K] using h)).differentiableWithinAt)
  have hs (p) (hp : p∈Z) : rectangleBoundary (L p) ⟨a,c⟩ ⟨b,d⟩=2*Real.pi*I*((m p:ℂ)*g p) :=
    rectangleBoundary_cauchy (hg.const_mul (m p:ℂ)) (hZ_int p hp).1.1 (hZ_int p hp).1.2
      (hZ_int p hp).2.1 (hZ_int p hp).2.2
  change rectangleBoundary F ⟨a,c⟩ ⟨b,d⟩=_
  have hsum := sum_congr rfl hs
  dsimp only [rectangleBoundary] at hz hsum ⊢
  rw [horizontal c (Or.inl rfl),horizontal d (Or.inr rfl),vertical b (Or.inr rfl),vertical a (Or.inl rfl)]
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum] at hsum
  dsimp only [m] at hsum
  linear_combination hz+hsum

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
