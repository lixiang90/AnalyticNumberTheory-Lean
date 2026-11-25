import AnalyticNumberTheory.DirichletLFunctions.CriticalPolynomialEnergy

/-! # Harmonic mass of a tail in one residue class -/

open Finset Real

namespace AnalyticNumberTheory.DirichletLFunctions

/-- In the first block a single residue costs at most 1/A. The terms in
subsequent blocks of length q cost the harmonic sum divided by q. -/
theorem sum_residue_tail_inv_le {q A : ℕ} [NeZero q] (hA : 1≤A) (X : ℕ) (r : ZMod q) :
    (∑ n ∈ (Ioc A X).filter (fun n : ℕ => (n : ZMod q)=r), (n : ℝ)⁻¹) ≤
      (A : ℝ)⁻¹ + (q : ℝ)⁻¹*(1+Real.log X) := by
  classical
  let S := (Ioc A X).filter (fun n : ℕ => (n : ZMod q)=r)
  let w (j : ℕ) : ℝ := if j=0 then (A : ℝ)⁻¹ else (q : ℝ)⁻¹*(j : ℝ)⁻¹
  have hw (j : ℕ) : 0≤w j := by dsimp [w]; split <;> positivity
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have inj : Set.InjOn (fun n : ℕ => n/q) (S : Set ℕ) := by
    intro i hi j hj he
    have hsame : (i : ZMod q)=(j : ZMod q) := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
    have hrem := (ZMod.natCast_eq_natCast_iff ..).mp hsame
    change i%q=j%q at hrem
    change i/q=j/q at he
    calc i = q*(i/q)+i%q := (Nat.div_add_mod ..).symm
         _ = q*(j/q)+j%q := by rw [he,hrem]
         _ = j := Nat.div_add_mod ..
  have sub : S.image (fun n : ℕ => n/q) ⊆ Icc 0 X := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr ⟨Nat.zero_le _, (Nat.div_le_self n q).trans (mem_Ioc.mp (mem_filter.mp hn).1).2⟩
  have bound (n : ℕ) (hn : n ∈ S) : (n : ℝ)⁻¹ ≤ w (n/q) := by
    by_cases h : n/q=0
    · simp only [w, ite_eq_left h]
      exact inv_anti₀ (by exact_mod_cast hA) (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).1.le)
    · simp only [w, ite_eq_right h]
      have hp : (0 : ℝ) < ((n/q : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      have he : ((n/q : ℕ) : ℝ)*(q : ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n q
      exact (inv_anti₀ (mul_pos hp hq) he).trans_eq (by rw [mul_inv_rev])
  have hh : (∑ j ∈ Icc 1 X, (j : ℝ)⁻¹) ≤ 1+Real.log X := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log X
  calc
    _ ≤ ∑ n ∈ S, w (n/q) := sum_le_sum bound
    _ = ∑ j ∈ S.image (fun n : ℕ => n/q), w j := (sum_image inj).symm
    _ ≤ ∑ j ∈ Icc 0 X, w j := sum_le_sum_of_subset_of_nonneg sub fun j _ _ => hw j
    _ = (A : ℝ)⁻¹ + (q : ℝ)⁻¹*∑ j ∈ Icc 1 X, (j : ℝ)⁻¹ := by
      have split : Icc 0 X = insert 0 (Icc 1 X) := by ext j; simp; omega
      rw [split, sum_insert (by simp), mul_sum]
      congr 1
      apply sum_congr rfl
      intro j hj
      exact ite_eq_right (Nat.ne_of_gt (mem_Icc.mp hj).1)
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hh (by positivity)) _

end AnalyticNumberTheory.DirichletLFunctions
