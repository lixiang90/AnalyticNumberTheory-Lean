import AnalyticNumberTheory.DirichletLFunctions.ReducedHarmonicSum
import AnalyticNumberTheory.DirichletLFunctions.CharacterHarmonics

/-!
# The constant term in a periodic harmonic diagonal

Each residue class contributes its digamma value to the constant term.
No bound on the periodic coefficient function is needed.
-/
noncomputable section
open Real Complex Finset Set
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Constant after subtracting the average squared coefficient times
logarithm of the number of full periods. -/
def periodicHarmonicConstant {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) : ℝ :=
  -(∑r∈range q,‖Φ ((r+1:ℕ):ZMod q)‖^2*realDigamma (((r+1:ℕ):ℝ)/q))/q

theorem periodic_harmonic_constant_error {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) {x : ℝ} (hx : 2≤x) :
    |(∑n∈Finset.Icc 1 ⌊(q:ℝ)*x⌋₊,‖Φ n‖^2/(n:ℝ))-
      (periodicNormMean Φ*Real.log x+periodicHarmonicConstant Φ)|≤4*periodicNormMean Φ/x := by
  let a := fun r : ℕ => ((r+1:ℕ):ℝ)/q
  let W := fun r : ℕ => ‖Φ ((r+1:ℕ):ZMod q)‖^2
  let F := fun r : ℕ => ∑m∈range (⌊x-a r⌋₊+1),1/((m:ℝ)+a r)
  let L := ∑n∈Finset.Icc 1 ⌊(q:ℝ)*x⌋₊,‖Φ n‖^2/(n:ℝ)
  let Ψ := fun j : ZMod q => ((‖Φ j‖^2:ℝ):ℂ)
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hs (r : ℕ) : hurwitzDirectSum (a r) x 1=(F r:ℂ) := by
    unfold F hurwitzDirectSum;rw [Nat.range_succ_eq_Icc_zero,Complex.ofReal_sum];apply sum_congr rfl
    intro n _;push_cast;simp [Complex.cpow_neg_one]
  have hd : dirichletPoly (fun n : ℕ => Ψ n) ⌊(q:ℝ)*x⌋₊ 1=(L:ℂ) := by
    unfold dirichletPoly L;rw [Complex.ofReal_sum];apply sum_congr rfl;intro n _
    dsimp [Ψ];push_cast;simp [div_eq_mul_inv,Complex.cpow_neg_one]
  have H := periodic_directSum Ψ (by linarith : 1≤x) (1:ℂ)
  rw [hd] at H
  have he : L=(q:ℝ)⁻¹*∑r∈range q,W r*F r := by
    have hh (r : ℕ) : Ψ ((r+1:ℕ):ZMod q)*hurwitzDirectSum (((r+1:ℕ):ℝ)/q) x 1=
        ((W r*F r:ℝ):ℂ) := by rw [hs,Complex.ofReal_mul]
    simp_rw [hh] at H
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_sum,Complex.cpow_neg_one] using H
  let c := fun r => realDigamma (a r)
  have hc (r : ℕ) (hr : r∈range q) : |F r-Real.log x+c r|≤4/x := by
    exact shifted_harmonic_floor_remainder ⟨div_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) hq,
      (div_le_one hq).mpr (by exact_mod_cast Finset.mem_range.mp hr)⟩ hx
  have hW : (∑r∈range q,W r)/q=periodicNormMean Φ := by rw [periodicNormMean,sum_residues_succ]
  have hsum : |∑r∈range q,W r*(F r-Real.log x+c r)|≤(∑r∈range q,W r)*(4/x) := by
    apply (abs_sum_le_sum_abs ..).trans
    rw [sum_mul];apply sum_le_sum;intro r hr
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hc r hr) (sq_nonneg _)
  have hmain : (q:ℝ)⁻¹*∑r∈range q,W r*(F r-Real.log x+c r)=
      L-(periodicNormMean Φ*Real.log x+periodicHarmonicConstant Φ) := by
    rw [he,←hW,periodicHarmonicConstant]
    simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,←sum_mul]
    dsimp only [W,c,a];ring
  change |L-_|≤_
  rw [←hmain,abs_mul,abs_of_nonneg (inv_nonneg.mpr hq.le),←hW]
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)).trans_eq;ring

end AnalyticNumberTheory.DirichletLFunctions
