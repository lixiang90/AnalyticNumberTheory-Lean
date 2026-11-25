import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! # Bounds on an interior horizontal segment and finite contour shifts -/
noncomputable section
open Complex Set Metric MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Polynomial growth on the two distant horizontal edges may be absorbed by
a holomorphic rational weight. Only the width of the rectangle enters the
bound on the central segment. -/
theorem norm_le_on_horizontal_segment {f : ℂ → ℂ} {a b l u y d M : ℝ} (k : ℕ)
    (hab : a<b) (hd : 0<d) (hly : l+d≤y) (hyu : y+d≤u) (hM : 0≤M)
    (hf : DifferentiableOn ℂ f (Icc a b ×ℂ Icc l u))
    (hV : ∀ z : ℂ, (z.re=a ∨ z.re=b) → z.im∈Icc l u → ‖f z‖≤M)
    (hH : ∀ z : ℂ, z.re∈Icc a b → (z.im=l ∨ z.im=u) → ‖f z‖≤M*d^k)
    {x : ℝ} (hx : x∈Icc a b) :
    ‖f ((x:ℂ)+(y:ℂ)*I)‖ ≤ M*(1+b-a)^k := by
  let U := Ioo a b ×ℂ Ioo l u
  let L (z : ℂ) := z-((a-1:ℝ):ℂ)-(y:ℂ)*I
  have hlu : l<u := by linarith
  have hcl : closure U=Icc a b ×ℂ Icc l u := by
    simp only [U,closure_reProdIm,closure_Ioo hab.ne,closure_Ioo hlu.ne]
  have hLre (z : ℂ) : (L z).re = z.re-a+1 := by simp [L];ring
  have hLim (z : ℂ) : (L z).im = z.im-y := by simp [L]
  have hLnorm {z : ℂ} (hz : a≤z.re) : 1≤‖L z‖ := by
    have h := (le_abs_self (L z).re).trans (Complex.abs_re_le_norm _)
    rw [hLre] at h
    linarith
  have hLdiff : Differentiable ℂ L := by dsimp [L];fun_prop
  let g (z : ℂ) := f z/(L z)^k
  have hg : DiffContOnCl ℂ g U := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]
    apply hf.div (hLdiff.pow k).differentiableOn
    intro z hz
    exact pow_ne_zero _ (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hLnorm hz.1.1)))
  have bound {z : ℂ} {v : ℝ} (hv : 0≤v) (hvL : v≤‖L z‖) (hr : a≤z.re)
      (hfz : ‖f z‖≤M*v^k) : ‖g z‖≤M := by
    change ‖f z/L z^k‖ ≤ M
    rw [norm_div,norm_pow]
    apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (hLnorm hr)) _)).2
    exact hfz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hvL k) hM)
  have hb : ∀ z∈frontier U, ‖g z‖≤M := by
    intro z hz
    rw [show U=Ioo a b ×ℂ Ioo l u by rfl,frontier_reProdIm,closure_Ioo hab.ne,
      closure_Ioo hlu.ne,frontier_Ioo hab,frontier_Ioo hlu] at hz
    rcases hz with hh|hv
    · have hr : z.re∈Icc a b := hh.1
      have him : z.im=l ∨ z.im=u := hh.2
      apply bound hd.le _ hr.1 (hH z hr him)
      have H := Complex.abs_im_le_norm (L z)
      rw [hLim] at H
      rcases him with h|h <;> rw [h] at H
      · linarith only [hly,(abs_le.mp H).1]
      · linarith only [hyu,(abs_le.mp H).2]
    · have hre : z.re=a ∨ z.re=b := hv.1
      have h : a≤z.re := hre.elim (fun e => e.ge) (fun e => e ▸ hab.le)
      exact bound zero_le_one (hLnorm h) h (by simpa using hV z hre hv.2)
  let z : ℂ := (x:ℂ)+(y:ℂ)*I
  have hz : z ∈ closure U := by rw [hcl];exact ⟨by simpa [z] using hx,by simp [z]; constructor <;> linarith⟩
  have H := Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo a b).reProdIm (isBounded_Ioo l u)) hg hb hz
  have hreal : L z = ((1+x-a:ℝ):ℂ) := by dsimp [L,z];push_cast;ring
  change ‖f z/L z^k‖ ≤ M at H
  rw [norm_div,hreal,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hx.1])] at H
  exact ((div_le_iff₀ (pow_pos (by linarith [hx.1]) k)).mp H).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) k) hM)

/-- Cost of moving the integral from the left to the right side of a finite
rectangle, with the same pointwise bound on both horizontal edges. -/
theorem norm_vertical_integral_sub_le_horizontal {f : ℂ → ℂ} {a b l u M : ℝ}
    (hab : a≤b) (hlu : l≤u) (hf : DifferentiableOn ℂ f (Icc a b ×ℂ Icc l u))
    (hh : ∀ x∈Icc a b, ∀ y∈({l,u}:Set ℝ), ‖f ((x:ℂ)+(y:ℂ)*I)‖≤M) :
    ‖(∫ t in l..u, f ((a:ℂ)+(t:ℂ)*I)) - (∫ t in l..u, f ((b:ℂ)+(t:ℂ)*I))‖ ≤
      2*M*(b-a) := by
  let V (x : ℝ) := ∫ t in l..u, f ((x:ℂ)+(t:ℂ)*I)
  let H (y : ℝ) := ∫ x in a..b, f ((x:ℂ)+(y:ℂ)*I)
  have he := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (⟨a,l⟩:ℂ) (⟨b,u⟩:ℂ)
    (by simpa only [uIcc_of_le hab,uIcc_of_le hlu] using hf)
  change H l-H u+I*V b-I*V a=0 at he
  have hEq : I*(V a-V b) = H l-H u := by linear_combination -he
  have hnorm (y : ℝ) (hy : y∈({l,u}:Set ℝ)) : ‖H y‖≤M*(b-a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b)
      (f:=fun x : ℝ => f ((x:ℂ)+(y:ℂ)*I)) (fun x hx =>
        hh x (uIcc_of_le hab ▸ uIoc_subset_uIcc hx) y hy)
    simpa [H,abs_of_nonneg (sub_nonneg.mpr hab)] using h
  change ‖V a-V b‖≤_
  calc
    _ = ‖I*(V a-V b)‖ := by rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ ‖H l‖+‖H u‖ := hEq ▸ norm_sub_le ..
    _ ≤ _ := by linarith only [hnorm l (by simp),hnorm u (by simp)]

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
