import AnalyticNumberTheory.AnalyticTools.BarnesKernel
import AnalyticNumberTheory.AnalyticTools.HankelMellin
import AnalyticNumberTheory.AnalyticTools.MellinTail

/-!
# Hankel's contour for the Barnes double zeta function

The circle and the outgoing and returning sides of the positive-axis
cut together give an entire function of the weight.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools

/-- A logarithmic radius inside the disk of the Barnes kernel's
double pole at zero. -/
def BarnesHankelRadius (a b : ℂ) (X : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℂ, 0<‖u‖ → ‖u‖≤Real.exp X →
    DifferentiableAt ℂ (barnesComplexKernel a b) u ∧ ‖u‖^2*‖barnesComplexKernel a b u‖≤C

theorem exists_barnesHankelRadius (a : ℂ) {b : ℂ} (hb : b≠0) : ∃ X, BarnesHankelRadius a b X := by
  obtain ⟨r,C,hr,H⟩ := exists_barnesKernel_disk a hb
  refine ⟨Real.log r,C,?_⟩; rwa [Real.exp_log hr]

theorem BarnesHankelRadius.mono {a b : ℂ} {x X : ℝ} (h : BarnesHankelRadius a b X)
    (hx : x≤X) : BarnesHankelRadius a b x := by
  obtain ⟨C,hC⟩ := h; exact ⟨C,fun u hu hur => hC u hu (hur.trans (Real.exp_le_exp.mpr hx))⟩

/-- The full Barnes Hankel contour, counterclockwise with continuously
lifted argument on the cut plane. -/
noncomputable def barnesHankel (a b : ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  hankelMellinArc (barnesComplexKernel a b) s X+
    (Complex.exp (s*(2*π*I))-1)*∫ t : ℝ in Ioi (Real.exp X),barnesKernel a b t*(t:ℂ)^(s-1)

/-- The complete contour integral is entire in its complex weight. -/
theorem differentiable_barnesHankel {a b : ℂ} {X : ℝ} (ha : 0<a.re) (hb : 0<b.re)
    (hX : BarnesHankelRadius a b X) : Differentiable ℂ (barnesHankel a b X) := by
  obtain ⟨C,H⟩ := hX
  apply Differentiable.add
  · exact differentiable_hankelMellinArc _ _ fun u hu =>
      (H u (hu.symm ▸ Real.exp_pos X) hu.le).1.continuousAt
  · apply Differentiable.mul
    · fun_prop
    · exact differentiable_mellinTail ha (Real.exp_pos _) ((continuousOn_barnesKernel a hb).mono
        (Ici_subset_Ioi.mpr (Real.exp_pos X))) (barnesKernel_isBigO_atTop hb)

/-- Evaluation by shrinking the circle in the half-plane where the
uncut Mellin integral converges absolutely. -/
theorem barnesHankel_eq {a b s : ℂ} {X : ℝ} (ha : 0<a.re) (hb : 0<b.re)
    (hX : BarnesHankelRadius a b X) (hs : 2<s.re) :
    barnesHankel a b X s=(Complex.exp (s*(2*π*I))-1)*(Complex.Gamma s*barnesDoubleZeta a b s) := by
  obtain ⟨C,H⟩ := hX
  have hi := integrableOn_barnesMellin ha hb hs
  have h₁ := hi.mono_set (show Ioc 0 (Real.exp X)⊆Ioi 0 from fun _ ht => ht.1)
  have h₂ := hi.mono_set (Ioi_subset_Ioi (Real.exp_pos X).le)
  have h := hankelMellinArc_eq (K:=barnesComplexKernel a b) hs (fun u hu hr => (H u hu hr).1)
    (fun u hu hr => (H u hu hr).2) h₁
  unfold barnesHankel
  rw [h,intervalIntegral.integral_of_le (Real.exp_pos X).le,←integral_barnesKernel ha hb hs,
    ←Ioc_union_Ioi_eq_Ioi (Real.exp_pos X).le,setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h₁ h₂,mul_add]
  rfl

end AnalyticNumberTheory.AnalyticTools
