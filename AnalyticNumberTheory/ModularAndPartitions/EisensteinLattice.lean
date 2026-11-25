import AnalyticNumberTheory.AnalyticTools.LipschitzSummation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The Eisenstein lattice at complex weight

The branch of the logarithm has argument in `[-π,π)`. In particular a
negative real lattice vector carries the factor `exp(π i s)`. Pairing
opposite vectors leaves one row of the zeta series and the upper rows
to which Lipschitz summation applies.
-/

open Complex Real Finset
open scoped UpperHalfPlane
namespace AnalyticNumberTheory.ModularAndPartitions

/-- The factor relating opposite vectors when the first vector lies
in the upper half-plane or on the positive real axis. -/
noncomputable def eisensteinReflection (s : ℂ) : ℂ := Complex.exp (π*I*s)

/-- The lattice summand with the argument in `[-π,π)`. Positive rows
use the principal power directly, with the real row split at the origin. -/
noncomputable def eisensteinLatticeTerm (z : ℍ) (s : ℂ) (m n : ℤ) : ℂ :=
  if m=0 ∧ n=0 then 0 else
  if 0<m ∨ m=0 ∧ 0<n then ((m:ℂ)*(z:ℂ)+n)^(-s)
  else eisensteinReflection s * (-((m:ℂ)*(z:ℂ)+n))^(-s)

/-- The absolutely convergent lattice representation of the complex-weight
Eisenstein function on `2 < re s`. -/
noncomputable def eisensteinLatticeSum (z : ℍ) (s : ℂ) : ℂ :=
  ∑' v : ℤ×ℤ,eisensteinLatticeTerm z s v.1 v.2

theorem summable_eisensteinLatticeTerm (z : ℍ) {s : ℂ} (hs : 2<s.re) :
    Summable fun v : ℤ×ℤ => eisensteinLatticeTerm z s v.1 v.2 := by
  apply (finTwoArrowEquiv ℤ).summable_iff.mp
  apply summable_norm_iff.mp
  let C := (1+‖eisensteinReflection s‖)*Real.exp (π*|s.im|)
  have hC : 0≤C := by dsimp [C]; positivity
  have hE := (EisensteinSeries.summable_one_div_norm_rpow hs).mul_left
    (C*(EisensteinSeries.r z)^(-s.re))
  apply hE.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  let w : ℂ := (v 0:ℂ)*(z:ℂ)+(v 1:ℤ)
  have ha (w : ℂ) : ‖w^(-s)‖≤‖w‖^(-s.re)*Real.exp (π*|s.im|) := by
    simpa only [Complex.neg_re,Complex.neg_im,abs_neg] using AnalyticTools.norm_cpow_le_arg_bound w (-s)
  have hW : ‖w‖^(-s.re)≤(EisensteinSeries.r z)^(-s.re)*‖v‖^(-s.re) :=
    EisensteinSeries.summand_bound z (by linarith) v
  change ‖eisensteinLatticeTerm z s (v 0) (v 1)‖≤_
  calc
    _ ≤ C*‖w‖^(-s.re) := by
      unfold eisensteinLatticeTerm
      split_ifs
      · rw [norm_zero]; positivity
      · change ‖w^(-s)‖≤_
        apply (ha w).trans
        dsimp [C]; nlinarith only [mul_nonneg (norm_nonneg (eisensteinReflection s))
          (mul_nonneg (Real.rpow_nonneg (norm_nonneg w) (-s.re)) (Real.exp_pos (π*|s.im|)).le)]
      · change ‖eisensteinReflection s*(-w)^(-s)‖≤_
        rw [norm_mul]
        have h := ha (-w)
        rw [norm_neg] at h
        apply (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans
        dsimp [C]; nlinarith only [mul_nonneg (Real.rpow_nonneg (norm_nonneg w) (-s.re)) (Real.exp_pos (π*|s.im|)).le]
    _ ≤ C*((EisensteinSeries.r z)^(-s.re)*‖v‖^(-s.re)) := mul_le_mul_of_nonneg_left hW hC
    _ = _ := by ring

private theorem eisenstein_real_row (z : ℍ) {s : ℂ} (hs : 2<s.re) :
    (∑' n : ℤ,eisensteinLatticeTerm z s 0 n)=(1+eisensteinReflection s)*riemannZeta s := by
  have hsum := (summable_eisensteinLatticeTerm z hs).prod_factor 0
  rw [tsum_int_eq_zero_add_tsum_pnat hsum]
  have hp (n : ℕ+) : eisensteinLatticeTerm z s 0 (n:ℤ)=(n:ℂ)^(-s) := by
    have h : 0<(n:ℤ) := by exact_mod_cast n.2
    simp [eisensteinLatticeTerm,h,h.ne']
  have hm (n : ℕ+) : eisensteinLatticeTerm z s 0 (-(n:ℤ))=eisensteinReflection s*(n:ℂ)^(-s) := by
    have h : 0<(n:ℤ) := by exact_mod_cast n.2
    simp [eisensteinLatticeTerm,h,h.ne',not_lt_of_ge h.le]
  simp only [hp,hm,tsum_mul_left,show eisensteinLatticeTerm z s 0 0=0 by simp [eisensteinLatticeTerm],zero_add]
  rw [tsum_pnat_eq_tsum_succ (f:=fun n : ℕ => (n:ℂ)^(-s))]
  have he := zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith : 1<s.re)
  simp only [Complex.cpow_neg,one_div,Nat.cast_add_one] at *
  rw [he]; ring

/-- Pairing opposite lattice vectors gives the upper-row expansion. -/
theorem eisensteinLatticeSum_eq_upper_rows (z : ℍ) {s : ℂ} (hs : 2<s.re) :
    eisensteinLatticeSum z s=(1+eisensteinReflection s)*
      (riemannZeta s+∑' m : ℕ+,∑' n : ℤ,((m:ℂ)*(z:ℂ)+n)^(-s)) := by
  have h := summable_eisensteinLatticeTerm z hs
  rw [eisensteinLatticeSum,h.tsum_prod,tsum_int_eq_zero_add_tsum_pnat h.prod]
  rw [eisenstein_real_row z hs]
  have hp (m : ℕ+) (n : ℤ) : eisensteinLatticeTerm z s m n=((m:ℂ)*(z:ℂ)+n)^(-s) := by
    have hm : 0<(m:ℤ) := by exact_mod_cast m.2
    simp [eisensteinLatticeTerm,hm,hm.ne']
  have hm (m : ℕ+) : (∑' n : ℤ,eisensteinLatticeTerm z s (-(m:ℤ)) n)=
      eisensteinReflection s*∑' n : ℤ,((m:ℂ)*(z:ℂ)+n)^(-s) := by
    rw [←tsum_comp_neg (f:=fun n:ℤ => eisensteinLatticeTerm z s (-(m:ℤ)) n),←tsum_mul_left]
    apply tsum_congr
    intro n
    have hpos : 0<(m:ℤ) := by exact_mod_cast m.2
    simp [eisensteinLatticeTerm,hpos,hpos.ne',not_lt_of_ge hpos.le,neg_add_rev,add_comm]
  simp only [hp,hm,tsum_mul_left]; ring

end AnalyticNumberTheory.ModularAndPartitions
