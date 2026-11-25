import AnalyticNumberTheory.AdditiveNumberTheory.WaringUnitClasses
import AnalyticNumberTheory.AdditiveNumberTheory.WaringLocalPositivity
import Mathlib.RingTheory.ZMod.LocalRing

/-!
# Local Waring representations with a unit coordinate

Multiplication by a unit power preserves representability. Among the
positive representatives of unit classes, a missing class is at distance
at most two from a smaller represented unit. Each pair of new summands
therefore reaches an additional power class.
-/

open Finset
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Representation modulo `q` having at least one unit coordinate. -/
def WaringUnitRepresentation {q : ℕ} (k s : ℕ) (a : ZMod q) : Prop :=
  ∃ x : Fin s → ZMod q, ∑ i, x i^k=a ∧ ∃ i, IsUnit (x i)

private theorem one_rep {q k : ℕ} : WaringUnitRepresentation k 1 (1:ZMod q) :=
  ⟨fun _ => 1,by simp,0,isUnit_one⟩

private theorem rep_cons {q k s : ℕ} {a : ZMod q} (h : WaringUnitRepresentation k s a) (x : ZMod q) :
    WaringUnitRepresentation k (s+1) (x^k+a) := by
  obtain ⟨v,he,i,hi⟩ := h
  exact ⟨Fin.cons x v,by simp [Fin.sum_univ_succ,he],i.succ,by simpa using hi⟩

theorem WaringUnitRepresentation.mono {q k s t : ℕ} (hk : 0<k) (hst : s≤t) {a : ZMod q}
    (h : WaringUnitRepresentation k s a) : WaringUnitRepresentation k t a := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => simpa [hk.ne'] using rep_cons ih 0

private theorem rep_add_one {q k s : ℕ} {a : ZMod q} (h : WaringUnitRepresentation k s a) :
    WaringUnitRepresentation k (s+1) (a+1) := by simpa [add_comm] using rep_cons h 1

private theorem rep_scale {q k s : ℕ} {a : ZMod q} (h : WaringUnitRepresentation k s a) (v : (ZMod q)ˣ) :
    WaringUnitRepresentation k s (a*(v:ZMod q)^k) := by
  obtain ⟨x,hx,i,hi⟩ := h
  exact ⟨fun j => x j*v,by simp [mul_pow,←sum_mul,hx],i,hi.mul v.isUnit⟩

private theorem rep_power_class {q k s : ℕ} (u b v : (ZMod q)ˣ) (e : u=b*v^k) :
    WaringUnitRepresentation k s (u:ZMod q) ↔ WaringUnitRepresentation k s (b:ZMod q) := by
  subst u
  refine ⟨fun h => ?_,fun h => by simpa using rep_scale h v⟩
  simpa [mul_assoc,←mul_pow] using rep_scale h v⁻¹

private theorem coprime_predecessor {p n : ℕ} (hp : p.Prime) (hn : 2≤n) :
    (n-1).Coprime p ∨ (n-2).Coprime p := by
  by_contra! h
  have ha := hp.coprime_iff_not_dvd.not.mp (fun hh => h.1 hh.symm)
  have hb := hp.coprime_iff_not_dvd.not.mp (fun hh => h.2 hh.symm)
  have he : n-1=(n-2)+1 := by omega
  have h₁ : p∣1 := (Nat.dvd_add_iff_right (not_not.mp hb)).mpr (he ▸ not_not.mp ha)
  exact hp.not_dvd_one h₁

private theorem exists_new_unit {p h k s : ℕ} (hp : p.Prime) (hh : 0<h) (hk : 0<k) (hs : 1≤s)
    (hmiss : ∃ u : (ZMod (p^h))ˣ, ¬WaringUnitRepresentation k s (u:ZMod (p^h))) :
    ∃ u : (ZMod (p^h))ˣ, ¬WaringUnitRepresentation k s (u:ZMod (p^h)) ∧
      WaringUnitRepresentation k (s+2) (u:ZMod (p^h)) := by
  classical
  let q := p^h
  haveI : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hq : 1<q := one_lt_pow₀ hp.one_lt hh.ne'
  have hex : ∃ n : ℕ, IsUnit (n:ZMod q) ∧ ¬WaringUnitRepresentation k s (n:ZMod q) := by
    obtain ⟨u,hu⟩ := hmiss
    change ¬WaringUnitRepresentation k s (u:ZMod q) at hu
    exact ⟨(u:ZMod q).val,by simpa using u.isUnit,by simpa using hu⟩
  let n := Nat.find hex
  obtain ⟨hn,hm⟩ := Nat.find_spec hex
  change IsUnit (n:ZMod q) at hn
  change ¬WaringUnitRepresentation k s (n:ZMod q) at hm
  have hpos : 2≤n := by
    by_contra! h
    interval_cases n
    · haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
      simpa using hn
    · exact hm (by simpa using (WaringUnitRepresentation.mono hk hs (one_rep (q:=q))))
  have hprev (m : ℕ) (hmn : m<n) (hc : m.Coprime p) : WaringUnitRepresentation k s (m:ZMod q) := by
    have hu : IsUnit (m:ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr (hc.pow_right h)
    by_contra he
    exact (Nat.find_min hex hmn) ⟨hu,he⟩
  refine ⟨hn.unit,by simpa using hm,?_⟩
  rw [IsUnit.unit_spec]
  rcases coprime_predecessor hp hpos with ha|hb
  · have H := (rep_add_one (hprev (n-1) (by omega) ha)).mono hk (show s+1≤s+2 by omega)
    simpa only [←Nat.cast_one (R:=ZMod q),←Nat.cast_add,show n-1+1=n by omega] using H
  · have H := rep_add_one (rep_add_one (hprev (n-2) (by omega) hb))
    simpa only [←Nat.cast_one (R:=ZMod q),←Nat.cast_add,show n-2+1+1=n by omega] using H

/-- Every unit modulo a prime power can be represented by at most
`4k-1` powers, with one coordinate a unit. -/
theorem waring_units_prime_power {p h k : ℕ} (hp : p.Prime) (hh : 0<h) (hk : 0<k)
    (u : (ZMod (p^h))ˣ) : WaringUnitRepresentation k (4*k-1) (u:ZMod (p^h)) := by
  classical
  let G := (ZMod (p^h))ˣ
  obtain ⟨B,hB,H⟩ := waring_unit_power_classes (a:=h) hp hk
  let V (s : ℕ) := B.filter (fun b : (ZMod (p^h))ˣ => WaringUnitRepresentation k s (b:ZMod (p^h)))
  have mono (s t : ℕ) (hst : s≤t) : V s⊆V t := by
    intro b hb; exact mem_filter.mpr ⟨(mem_filter.mp hb).1, WaringUnitRepresentation.mono hk hst (mem_filter.mp hb).2⟩
  have hfull (s : ℕ) (he : V s=B) (u : G) : WaringUnitRepresentation k s (u:ZMod (p^h)) := by
    obtain ⟨b,hb,v,hv⟩ := H u
    apply (rep_power_class u b v hv).mpr
    exact (mem_filter.mp (he ▸ hb : b∈V s)).2
  have hnon : (V 1).Nonempty := by
    obtain ⟨b,hb,v,hv⟩ := H 1
    exact ⟨b,mem_filter.mpr ⟨hb,(rep_power_class 1 b v hv).mp (by simpa using (one_rep (q:=p^h) (k:=k)))⟩⟩
  have hinc (s : ℕ) (hs : 1≤s) (hne : V s≠B) : (V s).card < (V (s+2)).card := by
    have hmiss : ∃ u : G, ¬WaringUnitRepresentation k s (u:ZMod (p^h)) := by
      by_contra! ha
      exact hne (filter_eq_self.mpr (fun b _ => ha b))
    obtain ⟨v,hv,hv'⟩ := exists_new_unit hp hh hk hs hmiss
    obtain ⟨b,hb,w,hw⟩ := H v
    have hnew : b∈V (s+2) := mem_filter.mpr ⟨hb,(rep_power_class v b w hw).mp hv'⟩
    have hold : b∉V s := fun h => hv ((rep_power_class v b w hw).mpr (mem_filter.mp h).2)
    exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨mono _ _ (by omega),fun he => hold (he ▸ hnew)⟩)
  have hstep (j : ℕ) : V (2*j+1)=B ∨ j+1≤(V (2*j+1)).card := by
    induction j with
    | zero => exact Or.inr (by simpa using hnon.card_pos)
    | succ j ih =>
      rw [show 2*(j+1)+1=(2*j+1)+2 by omega]
      rcases ih with ih|ih
      · exact Or.inl (le_antisymm (filter_subset ..) (ih ▸ mono _ _ (Nat.le_add_right _ _)))
      · by_cases he : V (2*j+1)=B
        · exact Or.inl (le_antisymm (filter_subset ..) (he ▸ mono _ _ (Nat.le_add_right _ _)))
        · exact Or.inr ((Nat.succ_le_succ ih).trans (hinc _ (by omega) he))
  have hBpos : 0<B.card := hnon.card_pos.trans_le (card_le_card (filter_subset ..))
  have hfull' : V (2*(B.card-1)+1)=B := by
    rcases hstep (B.card-1) with he|hc
    · exact he
    · apply eq_of_subset_of_card_le (filter_subset ..)
      change B.card≤(V (2*(B.card-1)+1)).card
      omega
  exact (hfull _ hfull' u).mono hk (by omega)

/-- Every residue modulo a prime power is a sum of `4k` powers with at
least one unit among the coordinates. -/
theorem waring_prime_power_unit_representation {p h k s : ℕ} (hp : p.Prime) (hh : 0<h)
    (hk : 0<k) (hs : 4*k≤s) (n : ZMod (p^h)) : WaringUnitRepresentation k s n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero h := ⟨hh.ne'⟩
  by_cases hu : IsUnit n
  · apply WaringUnitRepresentation.mono hk (by omega : 4*k-1≤s)
    simpa using waring_units_prime_power hp hh hk hu.unit
  · have hu' : IsUnit (n-1) := by
      have h := IsLocalRing.isUnit_or_isUnit_one_sub_self n
      simpa only [neg_sub] using (h.resolve_left hu).neg
    have hrep := rep_add_one (waring_units_prime_power hp hh hk hu'.unit)
    rw [IsUnit.unit_spec,sub_add_cancel] at hrep
    exact hrep.mono hk (by omega)

end AnalyticNumberTheory.AdditiveNumberTheory
