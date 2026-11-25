import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalCauchy
import AnalyticNumberTheory.RiemannZeta.FunctionalEquation

/-!
# A symmetric Gaussian integral for powers of the completed zeta function

The reflection law and a pair of vertical contours express `ξ(s)^k` as the
sum of two absolutely convergent Gaussian integrals on the right half-plane.
The polynomial factors in the definition of `ξ` absorb both zeta poles.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

private theorem linear_mul_log_le_sq_add {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → K*r*Real.log (r+2) ≤ r^2/8 + C := by
  let ε := 1/(16*(K+1))
  let L := 2*ε+|Real.log ε|
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hεK : K*ε ≤ 1/16 := by dsimp [ε]; rw [mul_one_div,div_le_iff₀ (by positivity)]; linarith
  refine ⟨4*(K*L)^2,?_⟩
  intro r hr
  have hlog := Real.log_le_sub_one_of_pos (mul_pos hε (by linarith : 0 < r+2))
  rw [Real.log_mul hε.ne' (by linarith)] at hlog
  have hh : Real.log (r+2) ≤ ε*r+L := by dsimp [L]; linarith [neg_abs_le (Real.log ε)]
  calc K*r*Real.log (r+2) ≤ K*r*(ε*r+L) := mul_le_mul_of_nonneg_left hh (by positivity)
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hεK (sq_nonneg r), sq_nonneg (r/4-2*(K*L))]

/-- Gaussian damping on a vertical strip for any function of growth
bounded by `A exp(B ‖z‖ log(‖z‖+2))`. -/
theorem gaussian_strip_bound_of_exp_norm_mul_log (f : ℂ→ℂ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : ∀ z : ℂ, ‖f z‖ ≤ A*Real.exp (B*‖z‖*Real.log (‖z‖+2)))
    (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0<c) :
    ∃ D : ℝ,0≤D ∧ ∀ x∈Icc (-c) c, ∀ t : ℝ,
      ‖f (s+((x:ℂ)+t*I))^k*Complex.exp (((x:ℂ)+t*I)^2)‖≤D/(1+t^2) := by
  let d := ‖s‖+c
  obtain ⟨C,hC⟩ := linear_mul_log_le_sq_add (K := k*B) (by positivity)
  refine ⟨2*A^k*Real.exp (C+d^2/4+c^2), by positivity,?_⟩
  intro x hx t
  let w := (x:ℂ)+t*I
  let r := ‖s+w‖
  have hx' := abs_le.mpr hx
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hr : 0 ≤ r := norm_nonneg _
  have hrd : r ≤ d+|t| := by
    have hw : ‖w‖ ≤ |x|+|t| := by
      simpa only [w,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] using norm_add_le (x:ℂ) ((t:ℂ)*I)
    exact (norm_add_le s w).trans (by dsimp [d]; linarith)
  have hr2 : r^2 ≤ 2*d^2 + 2*t^2 := by
    have h := sq_le_sq' (by linarith [abs_nonneg t]) hrd
    nlinarith [sq_nonneg (d-|t|),sq_abs t]
  have hwr : (w^2).re = x^2-t^2 := by simp [w,pow_two]
  have hxsq : x^2 ≤ c^2 := sq_le_sq' hx.1 hx.2
  have hexp : (k:ℝ)*(B*r*Real.log (r+2))+(w^2).re ≤ C+d^2/4+c^2-t^2/2 := by
    rw [hwr]
    nlinarith [hC r hr, sq_nonneg t]
  change ‖f (s+w)^k*Complex.exp (w^2)‖ ≤ _
  rw [norm_mul,norm_pow,Complex.norm_exp]
  have hpow := pow_le_pow_left₀ (norm_nonneg _) (hf (s+w)) k
  change ‖f (s+w)‖^k ≤ (A*Real.exp (B*r*Real.log (r+2)))^k at hpow
  rw [mul_pow,← Real.exp_nat_mul] at hpow
  calc _ ≤ (A^k*Real.exp (k*(B*r*Real.log (r+2))))*Real.exp (w^2).re :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
       _ ≤ A^k*Real.exp (C+d^2/4+c^2-t^2/2) := by
            rw [mul_assoc,← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
       _ ≤ _ := by
            rw [Real.exp_sub,le_div_iff₀ (by positivity),mul_div_assoc',div_mul_eq_mul_div,div_le_iff₀ (Real.exp_pos _)]
            nlinarith [mul_nonneg (by positivity : 0 ≤ A^k * Real.exp (C+d^2/4+c^2))
              (show 0 ≤ 2*Real.exp (t^2/2)-(1+t^2) by linarith [Real.add_one_le_exp (t^2/2)])]

/-- A horizontally uniform integrable majorant after Gaussian damping, for each fixed center. -/
theorem xi_pow_gaussian_strip_bound (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Icc (-c) c, ∀ t : ℝ,
      ‖xi (s+((x:ℂ)+t*I))^k * Complex.exp (((x:ℂ)+t*I)^2)‖ ≤ D/(1+t^2) := by
  obtain ⟨A,B,hA,hB,hxi⟩ := norm_xi_le_exp_norm_mul_log
  exact gaussian_strip_bound_of_exp_norm_mul_log xi hA.le hB.le hxi s k hc

/-- A right-line integral in the smoothed functional equation of a power of zeta. -/
noncomputable def xiGaussianIntegral (s : ℂ) (k : ℕ) (c : ℝ) : ℂ :=
  verticalCauchyIntegral (fun w => xi (s+w)^k*Complex.exp (w^2)) c

/-- Symmetric two-piece Gaussian integral identity for all powers of the completed zeta
function, at any complex center and every positive displacement. -/
theorem xi_pow_gaussian_functional_equation (s : ℂ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    xiGaussianIntegral s k c + xiGaussianIntegral (1-s) k c = 2*π*xi s^k := by
  let F (w : ℂ) := xi (s+w)^k * Complex.exp (w^2)
  have hf : Differentiable ℂ F :=
    ((differentiable_xi.comp ((differentiable_const s).add differentiable_id)).pow k).mul
      (Complex.differentiable_exp.comp (differentiable_id.pow 2))
  obtain ⟨D,hD,hb⟩ := xi_pow_gaussian_strip_bound s k hc
  have h := verticalCauchyIntegral_add_reflect (F := F) hf hc hD hb
  have href (z : ℂ) : F (-z) = xi ((1-s)+z)^k*Complex.exp (z^2) := by
    dsimp [F]
    rw [← xi_one_sub (s + -z),show 1-(s+ -z)=(1-s)+z by ring,neg_sq]
  simpa only [href, F, add_zero, zero_pow (by decide : 2 ≠ 0), Complex.exp_zero, mul_one,
    xiGaussianIntegral] using h

end AnalyticNumberTheory.RiemannZeta
