import AnalyticNumberTheory.AdditiveNumberTheory.Waring
import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Local representation counts for Waring's problem

The discrete Fourier formula counts all solutions of the power-sum congruence, including
imprimitive solutions. A vanishing local count rules out an integral representation.
-/

open Finset
open AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.AdditiveNumberTheory

variable {q : ℕ} [NeZero q]

/-- Number of ordered solutions in residues modulo `q`. -/
def waringLocalCount (k s : ℕ) (n : ZMod q) : ℕ :=
  (univ.filter (fun x : Fin s → ZMod q => ∑ i, x i ^ k = n)).card

/-- Local counts multiply over coprime moduli by the Chinese remainder theorem. -/
theorem waringLocalCount_mul {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (k s n : ℕ) : waringLocalCount k s (n : ZMod (u * v)) =
      waringLocalCount k s (n : ZMod u) * waringLocalCount k s (n : ZMod v) := by
  let crt := ZMod.chineseRemainder huv
  let sol (R : Type) [CommSemiring R] := {x : Fin s → R // ∑ i, x i ^ k = n}
  have mapSol {R T : Type} [CommSemiring R] [CommSemiring T] (f : R →+* T) (x : sol R) :
      ∑ i, f (x.val i) ^ k = n := by
    simpa only [map_sum, map_pow, map_natCast] using congrArg f x.property
  let e : sol (ZMod (u * v)) ≃ sol (ZMod u) × sol (ZMod v) := {
    toFun := fun x =>
      (⟨fun i => (crt (x.val i)).1, mapSol ((RingHom.fst _ _).comp crt.toRingHom) x⟩,
       ⟨fun i => (crt (x.val i)).2, mapSol ((RingHom.snd _ _).comp crt.toRingHom) x⟩)
    invFun := fun (x, y) => ⟨fun i => crt.symm (x.val i, y.val i), by
      apply crt.injective
      simp only [map_sum, map_pow, RingEquiv.apply_symm_apply, map_natCast]
      apply Prod.ext
      · simpa [Prod.fst_sum] using x.property
      · simpa [Prod.snd_sum] using y.property⟩
    left_inv := fun x => by ext i; simp
    right_inv := fun (x, y) => by ext <;> simp }
  simpa only [sol, Fintype.card_prod, Fintype.card_subtype, waringLocalCount]
    using Fintype.card_congr e

/-- Integral solutions reduce to solutions at each modulus. -/
theorem waringLocalCount_pos_of_waringCount_pos {k s n : ℕ} (hk : 0 < k)
    (hn : 0 < waringCount k s n) : 0 < waringLocalCount k s (n : ZMod q) := by
  obtain ⟨x, hx⟩ := (waringCount_pos_iff hk).mp hn
  refine card_pos.mpr ⟨fun i => (x i : ZMod q), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  simpa only [Nat.cast_sum, Nat.cast_pow] using congrArg (Nat.cast : ℕ → ZMod q) hx

/-- Complete Weyl sums as character sums over the residue ring. -/
theorem completeExpSum_eq_sum_stdAddChar (a : ZMod q) (k : ℕ) :
    completeExpSum q a.val k = ∑ x : ZMod q, ZMod.stdAddChar (a * x ^ k) := by
  symm
  unfold completeExpSum
  refine sum_bij (fun x _ => x.val) (fun x _ => mem_range.mpr x.val_lt)
    (fun _ _ _ _ h => ZMod.val_injective q h) ?_ ?_
  · exact fun b hb => ⟨(b : ZMod q), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hb)⟩
  · intro x _
    rw [show a * x ^ k = (((a.val : ℤ) * (x.val : ℤ) ^ k : ℤ) : ZMod q) by simp,
      ZMod.stdAddChar_coe]
    push_cast
    congr 1
    ring

/-- Fourier inversion modulo `q`. The frequency zero is included, and the unnormalized
complete sums give a factor of `q` on the counting side. -/
theorem waringLocalCount_fourier (k s : ℕ) (n : ZMod q) :
    ∑ a : ZMod q, completeExpSum q a.val k ^ s * ZMod.stdAddChar (-(a * n)) =
      (q : ℂ) * waringLocalCount k s n := by
  classical
  have hprod (a : ZMod q) (t : Finset (Fin s)) (x : Fin s → ZMod q) :
      ∏ i ∈ t, ZMod.stdAddChar (a * x i ^ k) = ZMod.stdAddChar (a * ∑ i ∈ t, x i ^ k) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      rw [prod_insert hi, sum_insert hi, mul_add, AddChar.map_add_eq_mul, ih]
  simp_rw [completeExpSum_eq_sum_stdAddChar, Fintype.sum_pow, sum_mul, hprod,
    ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
  rw [sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card, sub_eq_zero]
  rw [waringLocalCount, ← nsmul_eq_mul', ← sum_const, sum_filter]
  simp [apply_ite]

/-- Squares modulo eight give a local obstruction to representing `8m + 7` by three squares. -/
theorem waringCount_three_squares_eq_zero {n : ℕ} (hn : n % 8 = 7) :
    waringCount 2 3 n = 0 := by
  by_contra! h
  have hlocal := waringLocalCount_pos_of_waringCount_pos (q := 8) (k := 2)
    (by decide) (Nat.pos_of_ne_zero h)
  obtain ⟨x, hx⟩ := card_pos.mp hlocal
  have hsum := (mem_filter.mp hx).2
  have hn8 : (n : ZMod 8) = 7 := by
    change (n : ZMod 8) = ((7 : ℕ) : ZMod 8)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hn
  rw [hn8, Fin.sum_univ_three] at hsum
  have h8 : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  exact h8 _ _ _ hsum

end AnalyticNumberTheory.AdditiveNumberTheory
