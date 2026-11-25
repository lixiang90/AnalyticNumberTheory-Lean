import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximation

/-!
# Parseval's identity for Dirichlet character values

At each height the full second moment over the characters of one modulus
is a diagonal sum over unit residue classes.
-/
noncomputable section
open Real Complex Finset
open scoped ComplexConjugate
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Parseval for the unnormalized Fourier transform over all characters.
Residues outside the unit group make no contribution. -/
theorem dirichlet_character_parseval {q : ℕ} [NeZero q] (f : ZMod q→ℂ) :
    (∑χ : DirichletCharacter ℂ q,‖∑r : ZMod q,χ r*f r‖^2)=
      q.totient*∑r : ZMod q,if IsUnit r then ‖f r‖^2 else 0 := by
  classical
  have hdiag (r : ZMod q) : (∑j : ZMod q,if IsUnit r ∧ j=r then (q.totient:ℂ)*(f j*conj (f r)) else 0)=
      if IsUnit r then (q.totient:ℂ)*(f r*conj (f r)) else 0 := by
    by_cases hr : IsUnit r <;>simp [hr]
  have h (χ : DirichletCharacter ℂ q) : (∑r,χ r*f r)*conj (∑r,χ r*f r)=
      ∑r : ZMod q,∑j : ZMod q,(χ j*star (χ r))*(f j*conj (f r)) := by
    rw [map_sum,mul_sum];apply sum_congr rfl;intro r _
    rw [sum_mul,map_mul];apply sum_congr rfl;intro j _;change _=(χ j*conj (χ r))*_;ring
  have H : (∑χ : DirichletCharacter ℂ q,(∑r,χ r*f r)*conj (∑r,χ r*f r))=
      ∑r : ZMod q,if IsUnit r then (q.totient:ℂ)*(f r*conj (f r)) else 0 := by
    simp_rw [h];rw [sum_comm];apply sum_congr rfl;intro r _
    rw [sum_comm,←hdiag];apply sum_congr rfl;intro j _
    rw [←sum_mul,sum_chars_mul_conj_eq_general];split_ifs <;>simp_all
  have he (z : ℂ) : (z*conj z).re=‖z‖^2 := by rw [Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
  have H' := congrArg Complex.re H
  simp only [Complex.re_sum,he] at H'
  rw [H',mul_sum];apply sum_congr rfl;intro r _
  split_ifs <;>simp [Complex.mul_re,he]

/-- Pointwise full-family second moment on the critical line, including
both primitive and imprimitive characters. -/
theorem character_family_critical_energy {q : ℕ} [NeZero q] (t : ℝ) :
    (∑χ : DirichletCharacter ℂ q,‖χ.LFunction ((1/2:ℂ)+t*I)‖^2)=
      (q.totient/q:ℝ)*∑r∈range q,if IsUnit ((r+1:ℕ):ZMod q) then
        ‖HurwitzZeta.hurwitzZeta ((((r+1:ℕ):ℝ)/q:ℝ):UnitAddCircle) ((1/2:ℂ)+t*I)‖^2 else 0 := by
  let s := (1/2:ℂ)+t*I
  let g := fun r : ZMod q => HurwitzZeta.hurwitzZeta (ZMod.toAddCircle r) s
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hs : s.re=1/2 := by simp [s]
  have hpow : ‖(q:ℂ)^(-s)‖^2=(q:ℝ)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q),neg_re,hs,←Real.rpow_natCast _ 2,
      ←Real.rpow_mul hq.le,show -(1/2:ℝ)*(2:ℕ)= -1 by norm_num,Real.rpow_neg hq.le,Real.rpow_one]
  have h (χ : DirichletCharacter ℂ q) : ‖χ.LFunction s‖^2=(q:ℝ)⁻¹*‖∑r,χ r*g r‖^2 := by
    change ‖(q:ℂ)^(-s)*(∑r,χ r*g r)‖^2=_
    rw [norm_mul,mul_pow,hpow]
  change (∑χ : DirichletCharacter ℂ q,‖χ.LFunction s‖^2)=_
  simp_rw [h];rw [←mul_sum,dirichlet_character_parseval,sum_residues_succ]
  simp only [g,ZMod.toAddCircle_natCast];ring

end AnalyticNumberTheory.DirichletLFunctions
