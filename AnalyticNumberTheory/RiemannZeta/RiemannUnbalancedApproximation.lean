import AnalyticNumberTheory.RiemannZeta.HurwitzLogFreeApproximation
import AnalyticNumberTheory.RiemannZeta.RiemannDualGamma

/-!
# Log-free Riemann zeta approximation for arbitrary reciprocal cutoffs

The functional equation exchanges the short and long sides. On the
reversed side the error acquires the modulus of the gamma multiplier.
-/
noncomputable section
open Real Complex Finset Set
namespace AnalyticNumberTheory.RiemannZeta

/-- Log-free error for either ordering of x and y, including both edges
of the critical strip. -/
theorem riemannZeta_unbalanced_sharp_afe :
    ∃ C : ℝ,0<C ∧ ∀ {x y : ℝ},2≤x → 2≤y → ∀ {s : ℂ},s.re∈Icc (0:ℝ) 1 → |s.im|=2*Real.pi*x*y →
      ‖riemannZeta s-(∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(-s))-
        riemannDualGamma s*(∑ m∈range ⌊y⌋₊,((m:ℂ)+1)^(s-1))‖ ≤
        C*(x^(-s.re)+|s.im|^(1/2-s.re)*y^(s.re-1)) := by
  obtain ⟨K,hK,HK⟩ := norm_riemannDualGamma_strip_bound
  refine ⟨604*(1+K),by positivity,?_⟩
  intro x y hx hy s hσ ht
  have hx' : 0<x := by linarith
  have hy' : 0<y := by linarith
  have hπ : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have Ht : 1≤|s.im| := by rw [ht];nlinarith [mul_nonneg (sub_nonneg.mpr hπ) (mul_nonneg hx'.le hy'.le),mul_nonneg (show 0≤x-1 by linarith) (show 0≤y-1 by linarith)]
  have hne : s.im≠0 := abs_pos.mp (by linarith)
  let P (x : ℝ) (s : ℂ) := ∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(-s)
  let A := x^(-s.re)
  let B := |s.im|^(1/2-s.re)*y^(s.re-1)
  have hA : 0≤A := by dsimp [A];positivity
  have hB : 0≤B := by dsimp [B];positivity
  rcases le_total x y with hxy|hyx
  · apply (riemannZeta_logFree_sharp_afe hx hxy hσ ht).trans
    change 604*A≤604*(1+K)*(A+B);nlinarith [mul_nonneg hK.le hA,mul_nonneg hK.le hB]
  · let v := 1-s
    have hv : v.re∈Icc (0:ℝ) 1 := by change 0≤1-s.re ∧ 1-s.re≤1;constructor <;>linarith [hσ.1,hσ.2]
    have hvt : |v.im|=2*Real.pi*y*x := by dsimp [v];simp [ht];ring
    have H := riemannZeta_logFree_sharp_afe (s:=v) hy hyx hv hvt
    change ‖riemannZeta v-P y v-riemannDualGamma v*(∑ m∈range ⌊x⌋₊,((m:ℂ)+1)^(v-1))‖≤_ at H
    rw [show v-1= -s by dsimp [v];ring,show -v.re=s.re-1 by change -(1-s.re)=s.re-1;ring] at H
    change ‖riemannZeta v-P y v-riemannDualGamma v*P x s‖≤604*y^(s.re-1) at H
    rw [show s-1= -v by dsimp [v];ring]
    change ‖riemannZeta s-P x s-riemannDualGamma s*P y v‖≤_
    have he : riemannZeta s-P x s-riemannDualGamma s*P y v=
        riemannDualGamma s*(riemannZeta v-P y v-riemannDualGamma v*P x s) := by
      rw [riemannZeta_dualGamma_functional_equation hne]
      linear_combination (P x s)*(riemannDualGamma_reciprocal hne)
    rw [he,norm_mul]
    apply (mul_le_mul (HK s hσ Ht) H (norm_nonneg _) (by positivity)).trans
    change K*|s.im|^(1/2-s.re)*(604*y^(s.re-1))≤604*(1+K)*(A+B)
    calc
      _ = 604*K*B := by dsimp [B];ring
      _ ≤ _ := by nlinarith [mul_nonneg hK.le hA]

end AnalyticNumberTheory.RiemannZeta
