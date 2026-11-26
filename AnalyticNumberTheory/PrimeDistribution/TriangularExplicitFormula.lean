import AnalyticNumberTheory.AnalyticTools.SecondPoleDifference
import AnalyticNumberTheory.DirichletSeries.PositiveLogMean
import AnalyticNumberTheory.PrimeDistribution.IntegratedExplicitFormula
import AnalyticNumberTheory.PrimeDistribution.SmoothedZeroSums

/-!
# A triangular explicit formula for short intervals

The three logarithmic means at equally spaced logarithmic arguments give a
nonnegative triangular weight. Their second difference removes the linear
normalization, and both zero sums converge absolutely.
-/

noncomputable section

open Complex Finset
open scoped ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The von Mangoldt sum with a triangular weight on logarithms, supported
between exp(u) and exp(u+2h) and with maximum weight h at exp(u+h). -/
def triangularMangoldtSum (u h : ℝ) : ℂ :=
  logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp (u+2*h)) -
    2*logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp (u+h)) +
    logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp u)

/-- The triangular mean is nonnegative and bounded by its maximum weight times
the total von Mangoldt mass in the short interval. -/
theorem triangularMangoldtSum_re_bounds (u : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ (triangularMangoldtSum u h).re ∧
    (triangularMangoldtSum u h).re ≤ h*(Chebyshev.psi (Real.exp (u+2*h))-Chebyshev.psi (Real.exp u)) := by
  let F (v : ℝ) := logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp v)
  have H (v : ℝ) : Chebyshev.psi (Real.exp v)*h ≤ (F (v+h)-F v).re ∧
      (F (v+h)-F v).re ≤ Chebyshev.psi (Real.exp (v+h))*h := by
    have hs := logWeightedSum_increment_bounds (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
      (Real.exp_pos v) (Real.exp_le_exp.mpr (by linarith : v ≤ v+h))
    simpa only [←Real.exp_sub,add_sub_cancel_left,Real.log_exp,Chebyshev.psi,F] using hs
  have h₁ := H u
  have h₂ := H (u+h)
  rw [show u+h+h = u+2*h by ring] at h₂
  have he : triangularMangoldtSum u h = (F (u+2*h)-F (u+h))-(F (u+h)-F u) := by
    change F (u+2*h)-2*F (u+h)+F u = _
    ring
  rw [he,Complex.sub_re]
  constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2]

private theorem re_trivial_le (n : ℕ) : (trivialZetaZero n).re ≤ 0 := by
  simp [trivialZetaZero,Complex.mul_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The exact triangular explicit formula at every nonnegative logarithmic
argument and step. The pole at one and both zero families appear separately. -/
theorem exists_triangularMangoldtSum_explicit_formula :
    ∃ Z : ZetaZeroEnumeration, ∀ {u h : ℝ}, 0 ≤ u → 0 ≤ h →
      triangularMangoldtSum u h = secondPoleDifference 1 u h -
        (∑' n, secondPoleDifference (Z.zero n) u h) - ∑' n, secondPoleDifference (trivialZetaZero n) u h := by
  obtain ⟨Z,H⟩ := exists_logWeightedSum_vonMangoldt_eq_integratedZetaZeroSum
  refine ⟨Z,?_⟩
  intro u h hu hh
  have HF (v : ℝ) (hv : 0 ≤ v) : logWeightedSum (fun n => (Λ n : ℂ)) (Real.exp v) = integratedZetaZeroSum Z v := by
    simpa only [Real.log_exp] using H (Real.one_le_exp_iff.mpr hv)
  have hN := hasSum_secondPoleDifference (fun n => (mem_criticalStripZeros.mp (Z.mem_strip n)).2.2.le)
    Z.summable_inv_sq hu hh
  have hT := hasSum_secondPoleDifference re_trivial_le summable_trivialZetaZero_inv_sq hu hh
  rw [triangularMangoldtSum,HF _ (by linarith),HF _ (by linarith),HF _ hu,
    ←integratedPole_second_difference 1 hu hh,hN.tsum_eq,hT.tsum_eq]
  simp only [integratedZetaZeroSum,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

/-- Beyond logarithmic argument one, the entire trivial-zero contribution
to a triangular mean is bounded by four times the squared logarithmic step. -/
theorem norm_tsum_secondPoleDifference_trivial_le {u h : ℝ} (hu : 1 ≤ u) (hh : 0 ≤ h) :
    ‖∑' n, secondPoleDifference (trivialZetaZero n) u h‖ ≤ 4*h^2 := by
  let q := Real.exp (-2*u)
  have hq : q ≤ 1/2 := by
    rw [show q = (Real.exp (2*u))⁻¹ by dsimp [q]; rw [←Real.exp_neg]; congr 1; ring,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos (by linarith [Real.add_one_le_exp (2*u)])
  have hg := ((hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_right (1/2)).mul_left (4*h^2)
  apply (tsum_of_norm_bounded hg ?_).trans_eq (by ring)
  intro n
  have hpow : Real.exp ((trivialZetaZero n).re*u) = q^(n+1) := by
    rw [show q = Real.exp (-2*u) from rfl,←Real.exp_nat_mul]
    congr 1
    simp [trivialZetaZero,Complex.mul_re]
    ring
  have H := norm_secondPoleDifference_le_step (trivialZetaZero_ne_zero n) u hh
  rw [hpow,mul_pow] at H
  have hsmall : (Real.exp ((trivialZetaZero n).re*h)+1)^2 ≤ 4 := by
    have he := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (re_trivial_le n) hh)
    nlinarith [sq_nonneg (Real.exp ((trivialZetaZero n).re*h)), Real.exp_pos ((trivialZetaZero n).re*h),
      mul_nonneg (sub_nonneg.mpr he) (by positivity : 0 ≤ 3+Real.exp ((trivialZetaZero n).re*h))]
  calc
    _ ≤ q^(n+1)*(h^2*4) := H.trans (by gcongr)
    _ ≤ (1/2:ℝ)^(n+1)*(h^2*4) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hq _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- RH lower bound for the von Mangoldt mass in a multiplicative interval.
The second logarithmic difference saves a factor of log compared with
subtracting two global prime number theorem estimates. -/
theorem exists_lower_bound_triangular_psi_of_rh (hRH : RiemannHypothesisProp) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u h : ℝ}, 1 ≤ u → 0 < h → h ≤ 1/2 →
      Real.exp u*h^2 ≤ h*(Chebyshev.psi (Real.exp (u+2*h))-Chebyshev.psi (Real.exp u)) +
        C*Real.exp (u/2)*h*Real.log (1/h) + 4*h^2 := by
  obtain ⟨C,hC,HC⟩ := norm_tsum_secondPoleDifference_le_of_rh hRH
  obtain ⟨Z,HZ⟩ := exists_triangularMangoldtSum_explicit_formula
  refine ⟨C,hC,?_⟩
  intro u h hu hh hhalf
  let N := ∑' n, secondPoleDifference (Z.zero n) u h
  let T := ∑' n, secondPoleDifference (trivialZetaZero n) u h
  have hN := HC Z (by linarith : 0 ≤ u) hh hhalf
  have hT := norm_tsum_secondPoleDifference_trivial_le hu hh.le
  have hW := (triangularMangoldtSum_re_bounds u hh.le).2
  have hmain : (secondPoleDifference 1 u h).re = Real.exp u*(Real.exp h-1)^2 := by
    have he : secondPoleDifference 1 u h = ((Real.exp u*(Real.exp h-1)^2 : ℝ) : ℂ) := by
      simp [secondPoleDifference,Complex.ofReal_exp]
    rw [he,Complex.ofReal_re]
  have hid : (secondPoleDifference 1 u h).re = (triangularMangoldtSum u h).re + N.re + T.re := by
    rw [HZ (by linarith) hh.le]
    dsimp only [N,T]
    simp only [Complex.sub_re]
    ring
  have h₁ := pow_le_pow_left₀ hh.le (by linarith [Real.add_one_le_exp h] : h ≤ Real.exp h-1) 2
  have hreN : N.re ≤ C*Real.exp (u/2)*h*Real.log (1/h) := (Complex.re_le_norm _).trans hN
  have hreT : T.re ≤ 4*h^2 := (Complex.re_le_norm _).trans hT
  linarith [mul_le_mul_of_nonneg_left h₁ (Real.exp_pos u).le]

end AnalyticNumberTheory.PrimeDistribution
