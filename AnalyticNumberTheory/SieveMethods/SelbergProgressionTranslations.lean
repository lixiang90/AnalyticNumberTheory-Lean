import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Selberg's translation argument for a progression

Averaging translated reduced residue systems retains the fraction φ(q)/q of a
finite set. The Chinese remainder theorem prescribes the same translation at
all primes not dividing q.
-/

open Finset
namespace AnalyticNumberTheory.SieveMethods

private noncomputable def translatedUnits {q : ℕ} (a : ZMod q) :
    {j : ZMod q // IsUnit (a+j)} ≃ (ZMod q)ˣ where
  toFun j := j.prop.unit
  invFun u := ⟨(u:ZMod q)-a,by simpa using u.isUnit⟩
  left_inv j := by apply Subtype.ext; simp
  right_inv u := by apply Units.ext; simp

/-- In each complete period, precisely φ(q) translates send a fixed residue to a unit. -/
theorem card_unit_translates {q : ℕ} [NeZero q] (a : ZMod q) :
    (Finset.univ.filter (fun j : ZMod q => IsUnit (a+j))).card=q.totient := by
  classical
  rw [← Fintype.card_subtype,← ZMod.card_units_eq_totient]
  exact Fintype.card_congr (translatedUnits a)

/-- A single translate retains at least the mean number of elements coprime to q. -/
theorem exists_selberg_unit_translate {q : ℕ} [NeZero q] (A : Finset ℕ) :
    ∃ j : ZMod q, A.card*q.totient ≤ q*(A.filter (fun n : ℕ => IsUnit ((n:ZMod q)+j))).card := by
  classical
  let C (j : ZMod q) := (A.filter fun n : ℕ => IsUnit ((n:ZMod q)+j)).card
  have he : ∑j : ZMod q,C j=A.card*q.totient := by
    simp only [C,Finset.card_filter]
    rw [sum_comm]
    have hh (n : ℕ) : (∑ j : ZMod q, if IsUnit ((n:ZMod q)+j) then 1 else 0)=q.totient := by
      rw [← Finset.card_filter,card_unit_translates]
    simp [hh]
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ C Finset.univ_nonempty
  refine ⟨j,?_⟩
  calc
    A.card*q.totient = ∑i : ZMod q,C i := he.symm
    _ ≤ ∑_i : ZMod q,C j := Finset.sum_le_sum (fun i hi => hmax i hi)
    _ = q*C j := by simp [ZMod.card]

/-- A simultaneous translate. Modulo the sifted modulus it converts qn+a into
q(n+r); modulo q it realizes the independently selected translation j. -/
theorem exists_selberg_crt_translate {q M : ℕ} (hq : 0<q) (hM : 0<M)
    (h : M.Coprime q) (a : ℕ) (j : ZMod q) :
    ∃ r : ℕ, 1≤r ∧ q*r ≡ a [MOD M] ∧ (r:ZMod q)=j := by
  letI : NeZero M := ⟨hM.ne'⟩
  letI : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime q h.symm
  let c := ((↑u⁻¹ : ZMod M)*(a:ZMod M)).val
  have hqc : q*c ≡ a [MOD M] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    rw [Nat.cast_mul,show (q:ZMod M)=(u:ZMod M) from rfl]
    dsimp only [c]; rw [ZMod.natCast_zmod_val]
    simp [←mul_assoc]
  let t := Nat.chineseRemainder h c j.val
  let r := t.val+M*q
  have hrM : r ≡ t.val [MOD M] := Nat.add_modEq_left_iff.mpr (dvd_mul_right M q)
  have hrq : r ≡ t.val [MOD q] := Nat.add_modEq_left_iff.mpr (dvd_mul_left q M)
  refine ⟨r,by dsimp [r]; have := Nat.mul_pos hM hq; omega,((hrM.trans t.prop.1).mul_left q).trans hqc,?_⟩
  rw [← ZMod.natCast_zmod_val j]
  exact (ZMod.natCast_eq_natCast_iff ..).mpr (hrq.trans t.prop.2)

end AnalyticNumberTheory.SieveMethods
