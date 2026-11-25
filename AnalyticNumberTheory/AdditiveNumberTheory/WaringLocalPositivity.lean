import AnalyticNumberTheory.AdditiveNumberTheory.WaringLocalDensities
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Positive local densities for Waring congruences

Hensel lifting at the unit coordinate `1` uses the starting precision
`2 vₚ(k) + 1`. The argument applies also at primes dividing the degree.
-/

open Finset Filter Polynomial
open scoped Topology

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Precision sufficient for Hensel lifting the equation `X^k = b` at one. -/
def waringHenselLevel (p k : ℕ) : ℕ := 2 * k.factorization p + 1

variable {p : ℕ} [Fact p.Prime]

/-- Every residue congruent to one modulo `p^(2 vₚ(k)+1)` has a `k`-th
root at every higher power of `p`, including primes dividing `k`. -/
theorem exists_pow_eq_of_henselLevel {k r : ℕ} (hk : 0 < k) (hr : waringHenselLevel p k ≤ r)
    (b : ZMod (p^r)) (hb : ZMod.castHom (pow_dvd_pow p hr) (ZMod (p^(waringHenselLevel p k))) b = 1) :
    ∃ a : ZMod (p^r), a ^ k = b := by
  have hp : p.Prime := Fact.out
  let B := waringHenselLevel p k
  let c : ℤ_[p] := b.val
  have hred : PadicInt.toZModPow B (1-c) = 0 := by
    have he := congrArg (ZMod.castHom (pow_dvd_pow p hr) (ZMod (p^B))) (ZMod.natCast_zmod_val b)
    simp only [map_natCast] at he
    have h1 := he.trans hb
    simp only [c, map_sub, map_one, map_natCast, h1, sub_self]
  have hbound : ‖1-c‖ ≤ (p:ℝ) ^ (-(B:ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    exact hred
  have hval : (k : ℤ_[p]).valuation = k.factorization p := by
    apply Nat.cast_injective (R := ℤ)
    rw [← PadicInt.valuation_coe, PadicInt.coe_natCast, Padic.valuation_natCast, Nat.multiplicity_eq_factorization hp]
  have hsmall : ‖1-c‖ < ‖(k : ℤ_[p])‖^2 := by
    rw [PadicInt.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr hk.ne'), hval, ← zpow_natCast, ← zpow_mul]
    apply hbound.trans_lt
    apply (zpow_lt_zpow_iff_right₀ (show (1:ℝ) < p by exact_mod_cast hp.one_lt)).mpr
    dsimp [B, waringHenselLevel]
    omega
  let F : Polynomial ℤ_[p] := X^k - C c
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    simpa [F, derivative_X_pow] using hsmall
  obtain ⟨z,hz,_⟩ := hensels_lemma hnorm
  have hpow : z^k = c := sub_eq_zero.mp (by simpa [F] using hz)
  refine ⟨PadicInt.toZModPow r z, ?_⟩
  simpa [c] using congrArg (PadicInt.toZModPow r) hpow

/-- If each residue above the prescribed class admits a root, each lift of the other coordinates
gives a distinct representation. -/
theorem waringLocalCount_ge_of_liftable_residue {q Q : ℕ} [NeZero q] [NeZero Q]
    (hqQ : q ∣ Q) (k s : ℕ) (n : ZMod Q) (a : ZMod q)
    (hx : 0 < waringLocalCount k s (ZMod.castHom hqQ (ZMod q) n - a))
    (hlift : ∀ b : ZMod Q, ZMod.castHom hqQ (ZMod q) b = a → ∃ z : ZMod Q, z^k = b) :
    (Q/q)^s ≤ waringLocalCount k (s+1) n := by
  classical
  let red := ZMod.castHom hqQ (ZMod q)
  obtain ⟨x,hx⟩ := card_pos.mp hx
  have hsum : ∑ i, x i ^ k = red n - a := (mem_filter.mp hx).2
  let enc (i : Fin s) (a : Fin (Q/q)) : ℕ := (x i).val + q*a.val
  have hlt (i : Fin s) (a : Fin (Q/q)) : enc i a < Q := calc
    _ < q*(a.val+1) := by dsimp [enc]; rw [Nat.mul_succ]; have := (x i).val_lt; omega
    _ ≤ q*(Q/q) := Nat.mul_le_mul_left q a.isLt
    _ = Q := Nat.mul_div_cancel' hqQ
  let y (v : Fin s → Fin (Q/q)) (i : Fin s) : ZMod Q := enc i (v i)
  have hred (v : Fin s → Fin (Q/q)) (i : Fin s) : red (y v i) = x i := by
    change red (↑(enc i (v i)) : ZMod Q) = _
    rw [map_natCast]
    simp [enc]
  have hroot (v : Fin s → Fin (Q/q)) : ∃ z : ZMod Q, z^k = n - ∑ i, y v i ^ k := by
    apply hlift
    change red _ = _
    rw [map_sub, map_sum]
    simp only [map_pow, hred, hsum]
    ring
  choose z hz using hroot
  let rep (v : Fin s → Fin (Q/q)) : Fin (s+1) → ZMod Q := Fin.cons (z v) (y v)
  have hm (v : Fin s → Fin (Q/q)) : rep v ∈ univ.filter (fun t : Fin (s+1) → ZMod Q => ∑ i, t i ^ k = n) := by
    simp [rep, Fin.sum_univ_succ, hz]
  have hi : Function.Injective rep := by
    intro v w he
    funext i
    have h := congrArg (fun t : Fin (s+1) → ZMod Q => (t i.succ).val) he
    change (↑(enc i (v i)) : ZMod Q).val = (↑(enc i (w i)) : ZMod Q).val at h
    rw [ZMod.val_natCast_of_lt (hlt i (v i)), ZMod.val_natCast_of_lt (hlt i (w i))] at h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos q) (Nat.add_left_cancel h)
  simpa [waringLocalCount] using card_le_card_of_injOn (s := univ) rep (fun v _ => hm v) hi.injOn

/-- A class congruent to one can be filled by a single power at every lifting precision. -/
theorem waringLocalCount_ge_of_unit_lifting {q Q : ℕ} [NeZero q] [NeZero Q]
    (hqQ : q ∣ Q) (k s : ℕ) (n : ZMod Q)
    (hx : 0 < waringLocalCount k s (ZMod.castHom hqQ (ZMod q) n - 1))
    (hlift : ∀ b : ZMod Q, ZMod.castHom hqQ (ZMod q) b = 1 → ∃ z : ZMod Q, z^k = b) :
    (Q/q)^s ≤ waringLocalCount k (s+1) n :=
  waringLocalCount_ge_of_liftable_residue hqQ k s n 1 hx hlift

/-- Taking a suitable number of coordinates equal to one represents every
residue modulo `q` with at least `q-1` summands. -/
theorem waringLocalCount_pos_of_modulus_le {q : ℕ} [NeZero q] {k s : ℕ}
    (hk : 0 < k) (hs : q ≤ s+1) (n : ZMod q) : 0 < waringLocalCount k s n := by
  have hn : n.val ≤ s := by have := n.val_lt; omega
  let x (i : Fin s) : ZMod q := if i.val < n.val then 1 else 0
  refine card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  have hsum (i : Fin s) : x i ^ k = if i.val < n.val then 1 else 0 := by by_cases h : i.val < n.val <;> simp [x,h,hk.ne']
  simp_rw [hsum]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < n.val then (1 : ZMod q) else 0)]
  rw [show (∑ i ∈ range s, if i < n.val then (1 : ZMod q) else 0) =
    ∑ i ∈ (range s).filter (fun i => i < n.val), (1 : ZMod q) from (sum_filter _ _).symm]
  have he : (range s).filter (fun i => i < n.val) = range n.val := by ext i; simp; omega
  simp [he]

/-- A lower bound for the normalized counts at all sufficiently high powers gives a lower bound for the local factor. -/
theorem waringLocalFactor_re_ge_of_count {k s : ℕ} (hk : 0 < k) (hs : 2*k < s+1)
    (n B : ℕ) (h : ∀ r, B ≤ r → (p^r / p^B)^s ≤ waringLocalCount k (s+1) (n : ZMod (p^r))) :
    1 / ((p^B : ℕ) : ℝ)^s ≤ (waringLocalFactor k (s+1) n p).re := by
  let q := p^B
  have hlim := (Complex.continuous_re.tendsto (waringLocalFactor k (s+1) n p)).comp
    (tendsto_waringLocalCount_localFactor hk hs n p)
  have hreal : Tendsto (fun r : ℕ => ((p^r : ℕ) : ℝ) *
      (waringLocalCount k (s+1) (n : ZMod (p^r)) : ℝ) / ((p^r : ℕ) : ℝ)^(s+1))
      atTop (𝓝 (waringLocalFactor k (s+1) n p).re) := by
    convert hlim using 1
    funext r
    dsimp only [Function.comp_apply]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  apply ge_of_tendsto hreal
  filter_upwards [eventually_ge_atTop B] with r hr
  let Q := p^r
  let hd : q ∣ Q := pow_dvd_pow p hr
  have hcount := h r hr
  have hq : 0 < (q:ℝ) := by have : 0 < q := pow_pos (NeZero.pos p) _; exact_mod_cast this
  have hQ : 0 < (Q:ℝ) := by have : 0 < Q := pow_pos (NeZero.pos p) _; exact_mod_cast this
  have he : (q:ℝ) * ((Q/q : ℕ) : ℝ) = Q := by exact_mod_cast Nat.mul_div_cancel' hd
  change 1/(q:ℝ)^s ≤ (Q:ℝ) * _ / (Q:ℝ)^(s+1)
  calc
    _ = (Q:ℝ) * (((Q/q : ℕ) : ℝ)^s) / (Q:ℝ)^(s+1) := by
      rw [pow_succ]
      field_simp
      rw [← mul_pow]
      rw [he]
    _ ≤ _ := by gcongr; exact_mod_cast hcount

/-- A representation with a coordinate one at Hensel precision supplies a
uniform lower bound for the limiting density. -/
theorem waringLocalFactor_re_ge_of_henselLevel {k s : ℕ} (hk : 0 < k) (hs : 2*k < s+1)
    (n : ℕ) (hbase : 0 < waringLocalCount k s ((n : ZMod (p^waringHenselLevel p k)) - 1)) :
    1 / ((p^waringHenselLevel p k : ℕ) : ℝ)^s ≤ (waringLocalFactor k (s+1) n p).re := by
  apply waringLocalFactor_re_ge_of_count hk hs n
  intro r hr
  let hd := pow_dvd_pow p hr
  apply waringLocalCount_ge_of_unit_lifting hd
  · simpa only [map_natCast] using hbase
  · exact exists_pow_eq_of_henselLevel hk hr

/-- At primes dividing the degree, a sufficient supply of zero and one
coordinates at the starting precision gives a positive local density. -/
theorem waringLocalFactor_re_pos_of_modulus_le {k s : ℕ} (hk : 0 < k) (hs : 2*k < s+1)
    (hsum : p^waringHenselLevel p k ≤ s+1) (n : ℕ) : 0 < (waringLocalFactor k (s+1) n p).re :=
  (one_div_pos.mpr (pow_pos (by exact_mod_cast pow_pos (NeZero.pos p) (waringHenselLevel p k)) s)).trans_le
    (waringLocalFactor_re_ge_of_henselLevel hk hs n (waringLocalCount_pos_of_modulus_le hk hsum _))

/-- For a prime coprime to the degree, the prime-field Waring theorem and
Hensel lifting give a density lower bound even when `p` is large. -/
theorem waringLocalFactor_re_ge_of_coprime {k s : ℕ} (hk : 0 < k) (hs : 2*k < s+1)
    (hpk : p.Coprime k) (n : ℕ) : 1/(p : ℝ)^s ≤ (waringLocalFactor k (s+1) n p).re := by
  have hp : p.Prime := Fact.out
  have hq : p ^ waringHenselLevel p k = p := by
    simp [waringHenselLevel, Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hpk)]
  have hb : 0 < waringLocalCount k s ((n : ZMod (p^waringHenselLevel p k)) - 1) := by
    let _ : Fact (p ^ waringHenselLevel p k).Prime := ⟨hq.symm ▸ hp⟩
    exact waringLocalCount_pos_prime hk (by omega) _
  simpa only [hq] using waringLocalFactor_re_ge_of_henselLevel hk hs n hb

end AnalyticNumberTheory.AdditiveNumberTheory
