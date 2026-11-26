import AnalyticNumberTheory.PrimeDistribution.Oscillation
import AnalyticNumberTheory.PrimeDistribution.ZeroReciprocalSum
import AnalyticNumberTheory.RiemannZeta.RiemannHypothesis

/-!
# The von Koch error bound and the real parts of the zeta zeros

The sharp truncation at T = x and the reciprocal first moment of the zeros give
the upper bound in terms of their supremal real part. The oscillation theorem
gives the converse for every admissible power of x.
-/

noncomputable section

open Complex Filter Finset Set
open scoped Asymptotics
open AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.PrimeDistribution

/-- The real part of any zero in the open critical strip is bounded by the
least upper bound of all such real parts. -/
theorem re_le_zetaSupRe_of_nontrivial_zero {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) : ρ.re ≤ zetaSupRe :=
  le_csSup (s := {σ : ℝ | ∃ z : ℂ, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ z.re = σ})
    ⟨1,by rintro _ ⟨z,_,_,h,rfl⟩; exact h.le⟩ ⟨ρ,hz,h₀,h₁,rfl⟩

/-- At x ≥ 2, the error in the prime number theorem is bounded by an absolute
constant times x^Θ log² x, where Θ is the supremum of the real parts of the nontrivial zeros. -/
theorem abs_psi_sub_id_le_zetaSupRe_log_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x-x| ≤ C*(x^zetaSupRe*(Real.log x)^2) := by
  obtain ⟨C,hC,H⟩ := explicit_formula_psi
  obtain ⟨K,hK,HK⟩ := sum_zeroMultiplicity_div_norm_le
  let d := -deriv riemannZeta 0 / riemannZeta 0
  refine ⟨3*C+4*‖d‖+K,by positivity,?_⟩
  intro x hx
  let Z := ∑ ρ ∈ nontrivialZerosUpTo x, (zeroMultiplicity ρ : ℂ)*((x:ℂ)^ρ/ρ)
  let A := x^zetaSupRe
  let L := Real.log x
  have hx₀ : 0 < x := by linarith
  have hA : 1 ≤ A := Real.one_le_rpow (by linarith) (by linarith [half_le_zetaSupRe])
  have hL : 1/2 ≤ L := (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
    (Real.log_le_log two_pos hx)
  have hZ : ‖Z‖ ≤ K*(A*L^2) := calc
    _ ≤ ∑ ρ ∈ nontrivialZerosUpTo x, ‖(zeroMultiplicity ρ : ℂ)*((x:ℂ)^ρ/ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ nontrivialZerosUpTo x, A*((zeroMultiplicity ρ : ℝ)/‖ρ‖) := by
      apply sum_le_sum
      intro ρ hρ
      obtain ⟨hz,h₀,h₁,_⟩ := mem_nontrivialZerosUpTo.mp hρ
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hx₀]
      calc
        _ = x^ρ.re*((zeroMultiplicity ρ : ℝ)/‖ρ‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith)
          (re_le_zetaSupRe_of_nontrivial_zero hz h₀ h₁)) (by positivity)
    _ = A*(∑ ρ ∈ nontrivialZerosUpTo x, (zeroMultiplicity ρ : ℝ)/‖ρ‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(K*L^2) := mul_le_mul_of_nonneg_left (HK x hx) (zero_le_one.trans hA)
    _ = _ := by ring
  have herr := H x x hx hx le_rfl
  change ‖(Chebyshev.psi x:ℂ)-((x:ℂ)+d-Z)‖ ≤ C*(x*L^2/x+L) at herr
  rw [mul_div_cancel_left₀ _ hx₀.ne'] at herr
  have hQ : L^2 ≤ A*L^2 := le_mul_of_one_le_left (sq_nonneg _) hA
  have hQ₁ : 1 ≤ 4*(A*L^2) := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) hL]
  have hQ₂ : L^2+L ≤ 3*(A*L^2) := by nlinarith [mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ 2*L-1)]
  calc
    _ = ‖(Chebyshev.psi x:ℂ)-(x:ℂ)‖ := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((Chebyshev.psi x:ℂ)-((x:ℂ)+d-Z))+(d-Z)‖ := by congr 1; ring
    _ ≤ ‖(Chebyshev.psi x:ℂ)-((x:ℂ)+d-Z)‖ + ‖d-Z‖ := norm_add_le _ _
    _ ≤ C*(L^2+L) + (‖d‖+‖Z‖) := add_le_add herr (norm_sub_le _ _)
    _ ≤ (3*C+4*‖d‖+K)*(A*L^2) := by
      nlinarith only [mul_le_mul_of_nonneg_left hQ₂ hC.le,
        mul_le_mul_of_nonneg_left hQ₁ (norm_nonneg d), hZ]

/-- The unconditional error estimate for ψ in terms of the zero supremum, in asymptotic notation. -/
theorem psi_error_isBigO_zetaSupRe_log_sq :
    (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^zetaSupRe*(Real.log x)^2 := by
  obtain ⟨C,_,H⟩ := abs_psi_sub_id_le_zetaSupRe_log_sq
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  have hpos : 0 ≤ x^zetaSupRe*(Real.log x)^2 := by positivity [show 0 ≤ x by linarith]
  simpa only [Real.norm_eq_abs,abs_of_nonneg hpos] using H x hx

private theorem absorb_log_sq {a b : ℝ} (hab : a < b) :
    (fun x : ℝ => x^a*(Real.log x)^2) =O[atTop] fun x : ℝ => x^b := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (2:ℝ) (sub_pos.mpr hab)).bound one_pos,
    eventually_gt_atTop (1:ℝ)] with x hx hx₁
  have hx₀ : 0 < x := by linarith
  have hlog : (Real.log x)^2 ≤ x^(b-a) := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)),
      abs_of_nonneg (Real.rpow_pos_of_pos hx₀ _).le, one_mul] using hx
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx₀ _).le (sq_nonneg _)),
    abs_of_nonneg (Real.rpow_pos_of_pos hx₀ _).le,one_mul]
  calc
    _ ≤ x^a*x^(b-a) := mul_le_mul_of_nonneg_left hlog (Real.rpow_pos_of_pos hx₀ _).le
    _ = _ := by rw [← Real.rpow_add hx₀,show a+(b-a) = b by ring]

/-- Every exponent a in a pure-power error bound ψ(x)−x = O(x^a) bounds the real
parts of all nontrivial zeros from above. -/
theorem zetaSupRe_le_of_psi_error_isBigO {a : ℝ}
    (H : (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^a) : zetaSupRe ≤ a := by
  by_contra! ha
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp H
  have homega := (psi_sub_id_omega_supRe (zetaSupRe-a) (sub_pos.mpr ha) (C+1)).1
  obtain ⟨x,hx,hbound,hx₁⟩ := (homega.and_eventually (hC.and (eventually_gt_atTop (1:ℝ)))).exists
  rw [show zetaSupRe-(zetaSupRe-a) = a by ring] at hx
  have hp := Real.rpow_pos_of_pos (show 0 < x by linarith) a
  simp only [Real.norm_eq_abs,abs_of_nonneg hp.le] at hbound
  nlinarith [le_abs_self (Chebyshev.psi x-x)]

/-- Θ ≤ a is equivalent to the family of prime number theorem error bounds with every
exponent strictly larger than a. -/
theorem zetaSupRe_le_iff_psi_error_isBigO {a : ℝ} :
    zetaSupRe ≤ a ↔ ∀ ε : ℝ, 0 < ε →
      (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^(a+ε) := by
  constructor
  · intro ha ε hε
    exact psi_error_isBigO_zetaSupRe_log_sq.trans (absorb_log_sq (by linarith))
  · intro H
    by_contra! ha
    have h := zetaSupRe_le_of_psi_error_isBigO (H ((zetaSupRe-a)/2) (by linarith))
    linarith

/-- The supremum of the real parts of the zeta zeros is the infimum of the admissible
pure powers in the prime number theorem error term. -/
theorem zetaSupRe_eq_sInf_psi_error_exponents :
    zetaSupRe = sInf {a : ℝ | (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^a} := by
  let E := {a : ℝ | (fun x : ℝ => Chebyshev.psi x-x) =O[atTop] fun x : ℝ => x^a}
  have hmem {a : ℝ} (ha : zetaSupRe < a) : a ∈ E :=
    psi_error_isBigO_zetaSupRe_log_sq.trans (absorb_log_sq ha)
  have hl : ∀ a ∈ E, zetaSupRe ≤ a := fun _ ha => zetaSupRe_le_of_psi_error_isBigO ha
  change zetaSupRe = sInf E
  refine le_antisymm (le_csInf ⟨_,hmem (lt_add_one zetaSupRe)⟩ hl) ?_
  by_contra! h
  have hmid := csInf_le (show BddBelow E from ⟨zetaSupRe,fun _ ha => hl _ ha⟩)
    (hmem (show zetaSupRe < (zetaSupRe+sInf E)/2 by linarith))
  linarith

/-- Von Koch's criterion: RH is equivalent to the prime number theorem with
error O(√x log² x) for the inclusive Chebyshev function ψ. -/
theorem riemannHypothesisProp_iff_psi_error_isBigO_sqrt_log_sq :
    RiemannHypothesisProp ↔ (fun x : ℝ => Chebyshev.psi x-x) =O[atTop]
      fun x : ℝ => Real.sqrt x*(Real.log x)^2 := by
  constructor
  · intro hRH
    have h := zetaSupRe_eq_half_iff_riemannHypothesis.mpr (riemannHypothesisProp_iff_mathlib.mp hRH)
    simpa only [h,Real.sqrt_eq_rpow] using psi_error_isBigO_zetaSupRe_log_sq
  · intro H
    have hs : zetaSupRe ≤ 1/2 := zetaSupRe_le_iff_psi_error_isBigO.mpr (fun ε hε =>
      H.trans (by simpa only [Real.sqrt_eq_rpow] using (absorb_log_sq (a := 1/2) (b := 1/2+ε) (by linarith))))
    exact riemannHypothesisProp_iff_mathlib.mpr (zetaSupRe_eq_half_iff_riemannHypothesis.mp
      (le_antisymm hs half_le_zetaSupRe))

end AnalyticNumberTheory.PrimeDistribution
