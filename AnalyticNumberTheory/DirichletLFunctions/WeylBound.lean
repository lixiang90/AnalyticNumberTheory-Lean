import AnalyticNumberTheory.RiemannZeta.HurwitzWeyl
import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximation
import AnalyticNumberTheory.DirichletLFunctions.Characters

/-!
# Weyl bounds for periodic L-functions

The Hurwitz subconvex estimate applies on each residue class.
Summing the first terms separately keeps the dependence on the modulus
to a square root.
-/

open Complex Real Finset
open AnalyticNumberTheory.RiemannZeta AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem sum_shift_inv_sqrt (q : ℕ) :
    ∑ r ∈ range q, (√((r+1:ℕ):ℝ))⁻¹ ≤ 2*√q := by
  have he : (∑ r ∈ range q, (√((r+1:ℕ):ℝ))⁻¹) =
      ∑ n ∈ Icc 1 q, (√(n:ℝ))⁻¹ := by
    induction q with
    | zero => simp
    | succ q ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]
  rw [he]
  exact sum_Icc_inv_sqrt_le q

/-- Height-aspect Weyl subconvexity for every bounded periodic sequence.
The same absolute constant works for every modulus. -/
theorem periodicLFunction_weyl_bound :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ), (∀ j, ‖Φ j‖≤1) →
    ∀ {t : ℝ}, 2*π≤|t| → ‖ZMod.LFunction Φ ((1/2:ℂ)+t*I)‖ ≤
      C*√q*|t|^(1/6:ℝ)*(1+Real.log |t|) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_weyl_bound
  refine ⟨C+2,by positivity,?_⟩
  intro q _ Φ hΦ t ht
  let s := (1/2:ℂ)+t*I
  let V := |t|^(1/6:ℝ)*(1+Real.log |t|)
  have hh : 1≤|t| := by linarith [Real.two_le_pi]
  have hV : 1≤V := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hh (by norm_num))
    (by linarith [Real.log_nonneg hh])
  have hq : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hs : (-s).re = -(1/2:ℝ) := by simp [s]
  change ‖ZMod.LFunction Φ s‖ ≤ _
  rw [ZMod.LFunction,norm_mul,Complex.norm_natCast_cpow_of_pos (NeZero.pos q),hs,
    Real.rpow_neg hq.le,← Real.sqrt_eq_rpow,sum_residues_succ]
  have he (r : ℕ) : (√(((r+1:ℕ):ℝ)/q))⁻¹ = √(q:ℝ)*(√((r+1:ℕ):ℝ))⁻¹ := by
    rw [Real.sqrt_div (by positivity),inv_div,div_eq_mul_inv]
  have hsum : ‖∑ r ∈ range q, Φ ((r+1:ℕ):ZMod q)*
    HurwitzZeta.hurwitzZeta (ZMod.toAddCircle ((r+1:ℕ):ZMod q)) s‖ ≤ 2*(q:ℝ)+q*(C*V) := by
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑ r ∈ range q, (√q*(√((r+1:ℕ):ℝ))⁻¹+C*V) := by
              apply sum_le_sum
              intro r hr
              rw [norm_mul,ZMod.toAddCircle_natCast]
              have ha : ((r+1:ℕ):ℝ)/q ∈ Set.Ioc (0:ℝ) 1 :=
                ⟨by positivity,(div_le_one hq).mpr (by exact_mod_cast mem_range.mp hr)⟩
              apply (mul_le_of_le_one_left (norm_nonneg _) (hΦ _)).trans
              simpa only [he,V,s,mul_assoc] using H ha ht
         _ ≤ _ := by
              rw [sum_add_distrib,← Finset.mul_sum,sum_const,card_range,nsmul_eq_mul]
              have hmul := mul_le_mul_of_nonneg_left (sum_shift_inv_sqrt q) (Real.sqrt_nonneg (q:ℝ))
              nlinarith only [hmul,Real.sq_sqrt hq.le]
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
  have hs' := Real.sq_sqrt hq.le
  have hp := Real.sqrt_pos.mpr hq
  change (√(q:ℝ))⁻¹*(2*q+q*(C*V)) ≤ (C+2)*√q*|t|^(1/6:ℝ)*(1+Real.log |t|)
  rw [mul_assoc ((C+2)*√q)]
  change _ ≤ (C+2)*√q*V
  rw [← div_eq_inv_mul,div_le_iff₀ hp]
  nlinarith only [mul_le_mul_of_nonneg_left hV hq.le,
    congrArg (fun z : ℝ => (C+2)*z*V) hs']

/-- Uniform Weyl bound for Dirichlet characters, including imprimitive
characters and the principal character. -/
theorem LFunction_weyl_bound :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ}, 2*π≤|t| →
      ‖χ.LFunction ((1/2:ℂ)+t*I)‖ ≤ C*√q*|t|^(1/6:ℝ)*(1+Real.log |t|) := by
  obtain ⟨C,hC,H⟩ := periodicLFunction_weyl_bound
  exact ⟨C,hC,fun χ _ ht => H χ (norm_char_le_one χ) ht⟩

end AnalyticNumberTheory.DirichletLFunctions
