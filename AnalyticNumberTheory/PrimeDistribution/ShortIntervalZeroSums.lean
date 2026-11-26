import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula

/-!
# The explicit formula on short intervals

Subtracting the two endpoint formulas cancels the constant term.
The contribution of each zero is bounded by the interval length times
x raised to its real part minus one.
-/
noncomputable section
open Complex Real Finset
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

/-- Moving the endpoint through [x,x+h] changes each zero term by at most
h times x raised to the real part of the zero minus one. -/
theorem short_interval_cpow_bound {x h : ℝ} {ρ : ℂ}
    (hx : 0<x) (hh : 0≤h) (h₀ : 0<ρ.re) (h₁ : ρ.re<1) :
    ‖((x+h:ℝ):ℂ)^ρ/ρ-(x:ℂ)^ρ/ρ‖ ≤ h*x^(ρ.re-1) := by
  have hr : ρ≠0 := fun he => by simp [he] at h₀
  have hd (t : ℝ) (ht : t∈Set.Icc x (x+h)) :
      HasDerivWithinAt (fun u : ℝ => (u:ℂ)^ρ/ρ) ((t:ℂ)^(ρ-1)) (Set.Icc x (x+h)) t := by
    exact (((hasDerivAt_ofReal_cpow_const (hx.trans_le ht.1).ne' hr).div_const ρ).congr_deriv
      (by field_simp [hr])).hasDerivWithinAt
  have hb (t : ℝ) (ht : t∈Set.Ico x (x+h)) : ‖(t:ℂ)^(ρ-1)‖ ≤ x^(ρ.re-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le ht.1),Complex.sub_re,Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  simpa [mul_comm] using norm_image_sub_le_of_norm_deriv_le_segment' hd hb (x+h) ⟨by linarith,le_rfl⟩

/-- Short-interval Chebyshev bound in terms of the weighted, multiplicity
counted zero sum up to height T. Both positive and negative ordinates
are included. -/
theorem psi_interval_zero_sum_bound :
    ∃ C : ℝ, 0<C ∧ ∀ {x h T : ℝ}, 2≤x → 0≤h → h≤x → 2≤T → T≤x →
      |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤
        C*(x*(Real.log x)^2/T+Real.log x)+
          h*∑ ρ∈nontrivialZerosUpTo T,(zeroMultiplicity ρ:ℝ)*x^(ρ.re-1) := by
  obtain ⟨C,hC,hF⟩ := explicit_formula_psi
  refine ⟨9*C,by positivity,fun {x h T} hx hh hhx hT hTx => ?_⟩
  have hxp : 0<x := by linarith
  have hlog := Real.log_nonneg (show 1≤x by linarith)
  have hlog' := Real.log_nonneg (show 1≤x+h by linarith)
  have hlu : Real.log (x+h)≤2*Real.log x := by
    have hl := Real.log_le_log (show 0<x+h by linarith) (show x+h≤2*x by linarith)
    rw [Real.log_mul (by norm_num) hxp.ne'] at hl
    linarith [Real.log_le_log (show (0:ℝ)<2 by norm_num) hx]
  let w (ρ : ℂ) : ℂ := zeroMultiplicity ρ
  let Z (u : ℝ) : ℂ := ∑ ρ∈nontrivialZerosUpTo T,w ρ*((u:ℂ)^ρ/ρ)
  let E (u : ℝ) : ℂ := (Chebyshev.psi u:ℂ)-((u:ℂ)+(-deriv riemannZeta 0/riemannZeta 0)-Z u)
  have he (u : ℝ) (hu : 2≤u) (htu : T≤u) : ‖E u‖ ≤ C*(u*(Real.log u)^2/T+Real.log u) := hF u T hu hT htu
  have hz : ‖Z (x+h)-Z x‖ ≤ h*∑ ρ∈nontrivialZerosUpTo T,(zeroMultiplicity ρ:ℝ)*x^(ρ.re-1) := by
    dsimp only [Z]; rw [←sum_sub_distrib,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro ρ hρ
    obtain ⟨_,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hρ
    rw [←mul_sub,norm_mul,show ‖w ρ‖=(zeroMultiplicity ρ:ℝ) by simp [w]]
    exact (mul_le_mul_of_nonneg_left (short_interval_cpow_bound hxp hh h₀ h₁)
      (Nat.cast_nonneg _)).trans_eq (by ring)
  have htri : |Chebyshev.psi (x+h)-Chebyshev.psi x-h| ≤ ‖E (x+h)‖+‖E x‖+‖Z (x+h)-Z x‖ := by
    have heq : ((Chebyshev.psi (x+h)-Chebyshev.psi x-h:ℝ):ℂ) = E (x+h)-E x-(Z (x+h)-Z x) := by
      dsimp only [E]; push_cast; ring
    change ‖(Chebyshev.psi (x+h)-Chebyshev.psi x-h:ℝ)‖≤_
    rw [←Complex.norm_real,heq]
    exact (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)
  have hlog2 := pow_le_pow_left₀ hlog' hlu 2
  have hb := div_le_div_of_nonneg_right (mul_le_mul (show x+h≤2*x by linarith) hlog2
    (sq_nonneg _) (by positivity)) (show 0≤T by linarith)
  have hsum : (x+h)*(Real.log (x+h))^2/T+Real.log (x+h)+(x*(Real.log x)^2/T+Real.log x)
      ≤ 9*(x*(Real.log x)^2/T+Real.log x) := by
    apply (add_le_add (add_le_add hb hlu) le_rfl).trans
    ring_nf; linarith
  have herr := mul_le_mul_of_nonneg_left hsum hC.le
  linarith only [htri,hz,he x hx hTx,he (x+h) (by linarith) (by linarith),herr]

end AnalyticNumberTheory.PrimeDistribution
