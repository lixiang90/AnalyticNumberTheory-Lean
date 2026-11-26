import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleIntegrals

/-! # Residues of finitely many simple poles on a rectangular contour -/

noncomputable section

open Complex Set Finset Filter MeasureTheory
open scoped Topology Classical

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Near a puncture `p`, a function is a simple principal part `r/(z-p)` plus a function
analytic at `p`. A zero residue includes a removable singularity. -/
def HasSimplePrincipalPartAt (f : ℂ → ℂ) (p r : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ f =ᶠ[𝓝[≠] p] fun z => r/(z-p) + g z

/-- Dividing an analytic numerator by the displacement gives its value as the residue. -/
theorem hasSimplePrincipalPartAt_div_sub {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) :
    HasSimplePrincipalPartAt (fun z => g z/(z-p)) p (g p) := by
  refine ⟨dslope g p, hg.dslope p, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ p at hz
  rw [dslope_of_ne _ hz, slope_def_field]
  ring

/-- Multiplying a simple principal part by an analytic factor multiplies its residue by
the value of that factor. -/
theorem HasSimplePrincipalPartAt.mul_analytic {f g : ℂ → ℂ} {p r : ℂ}
    (hf : HasSimplePrincipalPartAt f p r) (hg : AnalyticAt ℂ g p) :
    HasSimplePrincipalPartAt (fun z => f z*g z) p (r*g p) := by
  obtain ⟨u, hu, he⟩ := hf
  refine ⟨fun z => u z*g z+r*dslope g p z, (hu.mul hg).add (analyticAt_const.mul (hg.dslope p)), ?_⟩
  filter_upwards [self_mem_nhdsWithin, he] with z hz hv
  change z ≠ p at hz
  rw [hv, dslope_of_ne _ hz, slope_def_field]
  ring

private theorem regularize_simplePoles (f : ℂ → ℂ) (K : Set ℂ) (Z : Finset ℂ) (r : ℂ → ℂ)
    (hreg : ∀ z ∈ K, z ∉ Z → DifferentiableAt ℂ f z)
    (hpole : ∀ p ∈ Z, HasSimplePrincipalPartAt f p (r p)) :
    ∃ G : ℂ → ℂ, (∀ z ∈ K, DifferentiableAt ℂ G z) ∧
      ∀ z ∉ Z, f z = G z + ∑ p ∈ Z, r p/(z-p) := by
  let B (p : ℂ) := if hp : p ∈ Z then (hpole p hp).choose else (fun _ : ℂ => 0)
  have hB (p : ℂ) (hp : p ∈ Z) : AnalyticAt ℂ (B p) p ∧
      f =ᶠ[𝓝[≠] p] fun z => r p/(z-p) + B p z := by simpa [B, hp] using (hpole p hp).choose_spec
  let P (S : Finset ℂ) (z : ℂ) := ∑ p ∈ S, r p/(z-p)
  let G (z : ℂ) := if z ∈ Z then B z z - P (Z.erase z) z else f z-P Z z
  have hP (S : Finset ℂ) (z : ℂ) (hz : z ∉ S) : DifferentiableAt ℂ (P S) z := by
    apply DifferentiableAt.fun_sum
    intro p hp
    exact (differentiableAt_const (r p)).div (differentiableAt_id.sub_const p) (sub_ne_zero.mpr (fun he => hz (he ▸ hp)))
  refine ⟨G, fun z hz => ?_, fun z hz => by simp [G, hz, P]⟩
  by_cases hp : z ∈ Z
  · have hnear : ∀ᶠ v in 𝓝 z, v ∉ Z.erase z :=
      (Z.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    apply ((hB z hp).1.differentiableAt.sub (hP _ z (notMem_erase z Z))).congr_of_eventuallyEq
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [self_mem_nhdsWithin, (hB z hp).2, hnear.filter_mono nhdsWithin_le_nhds] with v hv he hnot
      change v ≠ z at hv
      have hvZ : v ∉ Z := fun hm => hnot (mem_erase.mpr ⟨hv, hm⟩)
      have hsplit := sum_erase_add Z (fun p => r p/(v-p)) hp
      dsimp only [G, P, Pi.sub_apply]
      rw [ite_eq_right hvZ, he, ← hsplit]
      ring
    · simp [G, hp]
  · have he : G =ᶠ[𝓝 z] fun v => f v-P Z v := by
      filter_upwards [Z.finite_toSet.isClosed.isOpen_compl.mem_nhds hp] with v hv
      exact ite_eq_right hv
    exact ((hreg z hz hp).sub (hP Z z hp)).congr_of_eventuallyEq he

set_option maxHeartbeats 2000000 in
/-- If a function is regular on a closed rectangle except for finitely many simple
principal parts in the interior, its positively oriented boundary integral equals
`2πi` times the sum of their residues. -/
theorem rectangleBoundary_eq_sum_simpleResidues {f : ℂ → ℂ} {a b c d : ℝ} (hab : a<b) (hcd : c<d)
    (Z : Finset ℂ) (r : ℂ → ℂ) (hZ : ∀ p ∈ Z, p.re ∈ Ioo a b ∧ p.im ∈ Ioo c d)
    (hreg : ∀ z ∈ Icc a b ×ℂ Icc c d, z ∉ Z → DifferentiableAt ℂ f z)
    (hpole : ∀ p ∈ Z, HasSimplePrincipalPartAt f p (r p)) :
    rectangleBoundary f ⟨a,c⟩ ⟨b,d⟩ = 2*Real.pi*I*∑ p ∈ Z, r p := by
  let K := Icc a b ×ℂ Icc c d
  obtain ⟨G, hG, he⟩ := regularize_simplePoles f K Z r hreg hpole
  let L (p z : ℂ) := r p/(z-p)
  have hLcont (p z : ℂ) (hn : z ≠ p) : ContinuousAt (L p) z :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hn)
  have edge {s t : ℝ} (path : ℝ → ℂ) (hc : Continuous path)
      (hm : ∀ v ∈ uIcc s t, path v ∈ K ∧ path v ∉ Z) :
      (∫ v in s..t, f (path v)) = (∫ v in s..t, G (path v)) + ∑ p ∈ Z, ∫ v in s..t, L p (path v) := by
    have h₁ : ContinuousOn (fun v => G (path v)) (uIcc s t) :=
      fun v hv => ((hG _ (hm v hv).1).continuousAt.comp hc.continuousAt).continuousWithinAt
    have h₂ (p : ℂ) (hp : p ∈ Z) : ContinuousOn (fun v => L p (path v)) (uIcc s t) :=
      fun v hv => ((hLcont p (path v) (fun he => (hm v hv).2 (he ▸ hp))).comp hc.continuousAt).continuousWithinAt
    calc
      _ = ∫ v in s..t, G (path v) + ∑ p ∈ Z, L p (path v) :=
        intervalIntegral.integral_congr (fun v hv => he _ (hm v hv).2)
      _ = _ := by rw [intervalIntegral.integral_add h₁.intervalIntegrable
        (continuousOn_finsetSum Z h₂).intervalIntegrable,
        intervalIntegral.integral_finsetSum (fun p hp => (h₂ p hp).intervalIntegrable)]
  have no_boundary (z : ℂ) (h : z.re=a ∨ z.re=b ∨ z.im=c ∨ z.im=d) : z ∉ Z := by
    intro hz
    obtain ⟨⟨ha,hb⟩,hc,hd⟩ := hZ z hz
    rcases h with h|h|h|h <;> linarith
  have horizontal (v : ℝ) (hv : v=c ∨ v=d) := edge (s:=a) (t:=b)
    (fun x : ℝ => (x:ℂ)+v*I) (by fun_prop) (by
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      constructor
      · rcases hv with rfl|rfl <;> simpa [K,Complex.mem_reProdIm,hcd.le] using hx
      · apply no_boundary; simpa using Or.inr (Or.inr hv))
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
  have hG₀ : rectangleBoundary G ⟨a,c⟩ ⟨b,d⟩=0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G _ _ (fun z h => (hG z (by
      simpa only [uIcc_of_le hab.le,uIcc_of_le hcd.le,K] using h)).differentiableWithinAt)
  have hL (p : ℂ) (hp : p ∈ Z) : rectangleBoundary (L p) ⟨a,c⟩ ⟨b,d⟩ = 2*Real.pi*I*r p :=
    rectangleBoundary_cauchy (differentiable_const (r p)) (hZ p hp).1.1 (hZ p hp).1.2
      (hZ p hp).2.1 (hZ p hp).2.2
  have hsum := sum_congr rfl hL
  dsimp only [rectangleBoundary] at hG₀ hsum ⊢
  rw [horizontal c (Or.inl rfl), horizontal d (Or.inr rfl), vertical b (Or.inr rfl), vertical a (Or.inl rfl)]
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum] at hsum
  linear_combination hG₀ + hsum

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
