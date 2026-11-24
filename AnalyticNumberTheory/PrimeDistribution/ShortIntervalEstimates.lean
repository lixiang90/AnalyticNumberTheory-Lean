import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDensity
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem

/-!
# Short intervals for primes

The Riemann–von Mangoldt formula and the density theorem supply two inputs
to the Hoheisel–Ingham argument for intervals of length `x^θ`.
Independently, the classical prime number theorem gives unconditional asymptotics
on intervals of length `x exp(-d sqrt(log x))`.
-/

noncomputable section

open Finset Filter Asymptotics
open scoped Classical Topology

namespace AnalyticNumberTheory.PrimeDistribution

/-- The zero sum in the truncated explicit formula may be expressed using the
symmetric density finset and analytic orders of the completed zeta function. -/
theorem truncatedExplicitFormula : TruncatedExplicitFormulaHypothesis := by
  obtain ⟨C,hC,hform⟩ := explicit_formula_psi
  let b := -deriv riemannZeta 0 / riemannZeta 0
  refine ⟨C+2*‖b‖,by positivity,?_⟩
  intro x T hT hTx
  have hx := hT.trans hTx
  have h := hform x T hx hT hTx
  have heq : zeroDensityFinsetSymmetric T = nontrivialZerosUpTo T := by
    ext z; rw [mem_zeroDensityFinsetSymmetric,mem_nontrivialZerosUpTo]
  rw [heq]
  have hsum : ∑ ρ ∈ nontrivialZerosUpTo T, (analyticOrderNatAt RiemannZeta.xi ρ:ℂ)*(x:ℂ)^ρ/ρ =
      ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ:ℂ)*((x:ℂ)^ρ/ρ) := by
    refine sum_congr rfl fun z hz => ?_
    obtain ⟨_,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hz
    rw [zeroMultiplicity_eq_xi h₀ h₁]; ring
  rw [hsum]
  let Z := ∑ ρ ∈ nontrivialZerosUpTo T, (zeroMultiplicity ρ:ℂ)*((x:ℂ)^ρ/ρ)
  let E := x*Real.log x^2/T+Real.log x
  change ‖(Chebyshev.psi x : ℂ) - ((x:ℂ)+b-Z)‖ ≤ C*E at h
  change ‖(Chebyshev.psi x : ℂ) - x + Z‖ ≤ (C+2*‖b‖)*E
  have hE : 1/2 ≤ E := by
    have hlog := Real.log_le_log zero_lt_two hx
    dsimp [E]; linarith [Real.log_two_gt_d9, div_nonneg (mul_nonneg (by linarith : 0≤x) (sq_nonneg (Real.log x))) (by linarith : 0≤T)]
  have htri := norm_add_le ((Chebyshev.psi x : ℂ) - ((x:ℂ)+b-Z)) b
  rw [show (Chebyshev.psi x : ℂ) - ((x:ℂ)+b-Z) + b = (Chebyshev.psi x : ℂ)-x+Z by ring] at htri
  apply htri.trans
  nlinarith only [h, mul_le_mul_of_nonneg_right hE (norm_nonneg b)]

/-- The Hoheisel–Ingham asymptotic on polynomial-length intervals, assuming a
super-logarithmic zero-free region. -/
theorem psi_shortInterval_of_superLogZeroFree (hZF : SuperLogZeroFreeHypothesis) {θ : ℝ}
    (hθ : 3/4 < θ) (hlt : θ < 1) :
    (fun x : ℝ => Chebyshev.psi (x+x^θ)-Chebyshev.psi x) ~[atTop] fun x => x^θ :=
  psi_shortInterval_isEquivalent_of_zeroDensity zeta_zeroDensity truncatedExplicitFormula hZF
    (by linarith) hlt (by linarith)

/-- Under the same zero-free input every sufficiently large `(x,x+x^θ]` contains a prime. -/
theorem eventually_exists_prime_of_superLogZeroFree (hZF : SuperLogZeroFreeHypothesis) {θ : ℝ}
    (hθ : 3/4 < θ) (hlt : θ < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+x^θ :=
  eventually_exists_prime_shortInterval zeta_zeroDensity truncatedExplicitFormula hZF
    (by linarith) hlt (by linarith)

/-- Classical subexponential short-interval length. -/
def expShortInterval (d x : ℝ) : ℝ := x*Real.exp (-d*Real.sqrt (Real.log x))

private theorem shortInterval_of_exp_error {f : ℝ → ℝ} {C c d : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hdc : d < c)
    (herr : ∀ t : ℝ, 2 ≤ t → |f t-t| ≤ C*t*Real.exp (-c*Real.sqrt (Real.log t))) :
    (fun x : ℝ => f (x+expShortInterval d x)-f x) ~[atTop] expShortInterval d := by
  have hz : ∀ᶠ x : ℝ in atTop, expShortInterval d x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; dsimp [expShortInterval]; positivity
  rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hcd : 0 < c-d := by linarith
  have hp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hs.const_mul_atTop hcd)
  have hlim : Tendsto (fun x : ℝ => 3*C*Real.exp (-((c-d)*Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    simpa using hp.const_mul (3*C)
  apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  let h := expShortInterval d x
  let R := Real.sqrt (Real.log x)
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := by dsimp [h,expShortInterval]; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hhx : h ≤ x := mul_le_of_le_one_right hx0.le (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hd.le hR] : -d*R ≤ 0))
  have ht : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x+h)) :=
    Real.sqrt_le_sqrt (Real.log_le_log hx0 (by linarith))
  have hdec : Real.exp (-c*Real.sqrt (Real.log (x+h))) ≤ Real.exp (-c*R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht (by linarith))
  have he₂ := (herr (x+h) (by linarith)).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (by linarith : x+h ≤ 2*x) hC.le) hdec (Real.exp_pos _).le (by positivity))
  have he₁ := herr x hx
  have hnum : |f (x+h)-f x-h| ≤ 3*C*x*Real.exp (-c*R) := by
    rw [show f (x+h)-f x-h = (f (x+h)-(x+h))-(f x-x) by ring]
    exact (abs_sub _ _).trans ((add_le_add he₂ he₁).trans_eq (by dsimp only [R]; ring))
  change ‖(f (x+h)-f x)/h-1‖ ≤ 3*C*Real.exp (-((c-d)*R))
  rw [Real.norm_eq_abs, ← div_self hh.ne', ← sub_div, abs_div, abs_of_pos hh]
  apply (div_le_div_of_nonneg_right hnum hh.le).trans_eq
  change 3*C*x*Real.exp (-c*R)/(x*Real.exp (-d*R)) = _
  rw [mul_div_mul_comm, ← Real.exp_sub]
  field_simp [hx0.ne']; congr 1; ring

/-- Unconditional short-interval asymptotics for both Chebyshev functions, with
one common constant in the interval length. -/
theorem chebyshev_expShortInterval :
    ∃ d > 0, ((fun x : ℝ => Chebyshev.psi (x+expShortInterval d x)-Chebyshev.psi x)
      ~[atTop] expShortInterval d) ∧
      ((fun x : ℝ => Chebyshev.theta (x+expShortInterval d x)-Chebyshev.theta x)
      ~[atTop] expShortInterval d) := by
  obtain ⟨C,hC,c,hc,hpsi⟩ := abs_psi_sub_id_le_exp
  obtain ⟨D,hD,e,he,htheta⟩ := abs_theta_sub_id_le_exp
  let d := min c e/2
  have hd : 0 < d := by dsimp [d]; positivity
  exact ⟨d,hd,shortInterval_of_exp_error hC hd (by dsimp [d]; linarith [min_le_left c e]) hpsi,
    shortInterval_of_exp_error hD hd (by dsimp [d]; linarith [min_le_right c e]) htheta⟩

/-- Every sufficiently large `(x, x + x exp(-d sqrt(log x))]` contains a prime
for an absolute `d > 0`. -/
theorem eventually_exists_prime_expShortInterval :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+expShortInterval d x := by
  obtain ⟨d,hd,_,hθ⟩ := chebyshev_expShortInterval
  refine ⟨d,hd,?_⟩
  have hn : ∀ᶠ x : ℝ in atTop, expShortInterval d x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp [expShortInterval]; positivity
  rw [isEquivalent_iff_tendsto_one hn] at hθ
  filter_upwards [hθ.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1)), eventually_gt_atTop (0:ℝ)] with x hx hx0
  let h := expShortInterval d x
  have hh : 0<h := by dsimp [h, expShortInterval]; positivity
  have hdiff : 0 < Chebyshev.theta (x+h)-Chebyshev.theta x := by
    change 0 < (Chebyshev.theta (x+h)-Chebyshev.theta x)/h at hx
    exact (div_pos_iff_of_pos_right hh).mp hx
  rw [theta_eq_sum_primesLE,theta_eq_sum_primesLE] at hdiff
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊x+h⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.floor_mono (by linarith)), (Nat.mem_primesLE.mp hp).2⟩
  rw [← sum_sdiff_eq_sub hsub] at hdiff
  have hne : (Nat.primesLE ⌊x+h⌋₊ \ Nat.primesLE ⌊x⌋₊).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    rw [hempty,sum_empty] at hdiff
    exact (lt_irrefl 0) hdiff
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hp₁,hp₂⟩ := mem_sdiff.mp hp
  obtain ⟨hp₃,hp₄⟩ := Nat.mem_primesLE.mp hp₁
  have hlow : ⌊x⌋₊ < p := by by_contra! ht; exact hp₂ (Nat.mem_primesLE.mpr ⟨ht,hp₄⟩)
  exact ⟨p,hp₄,(Nat.floor_lt hx0.le).mp hlow,(Nat.cast_le.mpr hp₃).trans (Nat.floor_le (by positivity))⟩

end AnalyticNumberTheory.PrimeDistribution
