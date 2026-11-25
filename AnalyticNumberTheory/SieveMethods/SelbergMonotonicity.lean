import AnalyticNumberTheory.SieveMethods.SelbergProgressionTranslations
import AnalyticNumberTheory.SieveMethods.LargeSieve

/-!
# Selberg monotonicity for a prime progression

Each sufficiently large prime qk+a avoids one residue class of k at every
prime not dividing q. Averaging translations at primes dividing q embeds at
least φ(q)/q of the candidates into a translated interval free of all small
prime divisors.
-/

open Finset
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

/-- Translate the indices of a finite set of prime values in a progression
into a set without small divisors, retaining the totient density. -/
theorem selberg_progression_to_rough {q a : ℕ} [NeZero q] (A : Finset ℕ) (z : ℝ)
    (hprime : ∀k∈A, (q*k+a).Prime ∧ z<(q*k+a:ℕ)) :
    ∃ r : ℕ, ∃ T : Finset ℕ, 1≤r ∧ T⊆A.image (·+r) ∧
      A.card*q.totient≤q*T.card ∧ ∀ n∈T, ∀ d : ℕ, 1<d → (d:ℝ)≤z → ¬d∣n := by
  classical
  let P := ((⌊z⌋₊+1).primesBelow).filter (fun p => p.Coprime q)
  let M := ∏p∈P,p
  have hM : 0<M := Finset.prod_pos fun p hp => (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2.pos
  have hcop : M.Coprime q := Nat.coprime_prod_left_iff.mpr (fun _ hp => (mem_filter.mp hp).2)
  obtain ⟨j,hj⟩ := exists_selberg_unit_translate A (q:=q)
  obtain ⟨r,hr,hMr,hqr⟩ := exists_selberg_crt_translate (NeZero.pos q) hM hcop a j
  let S := A.filter (fun k : ℕ => IsUnit ((k:ZMod q)+j))
  let T := S.image (·+r)
  have hc : T.card=S.card := card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
  refine ⟨r,T,hr,image_subset_image (filter_subset _ _),by simpa only [hc] using hj,?_⟩
  intro n hn d hd hz hdn
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
  have hk' := mem_filter.mp hk
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (by omega : d≠1)
  have hpk := hpd.trans hdn
  have hpz : (p:ℝ)≤z := (show (p:ℝ)≤d by exact_mod_cast Nat.le_of_dvd (by omega : 0<d) hpd).trans hz
  by_cases hpq : p∣q
  · have hu : IsUnit ((k+r:ℕ):ZMod q) := by push_cast; rw [hqr]; exact hk'.2
    exact (Nat.not_coprime_of_dvd_of_dvd (by exact hp.one_lt) hpk hpq) ((ZMod.isUnit_iff_coprime ..).mp hu)
  · have hpP : p∈P := mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by have := Nat.le_floor hpz; omega,hp⟩,
      hp.coprime_iff_not_dvd.mpr hpq⟩
    have hpm : p∣M := Finset.dvd_prod_of_mem _ hpP
    have hh : q*(k+r) ≡ q*k+a [MOD p] := by
      rw [Nat.mul_add]; exact (hMr.of_dvd hpm).add_left _
    have hpd' : p∣q*k+a := Nat.modEq_zero_iff_dvd.mp
      (hh.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hpk q)))
    have hp' := hprime k hk'.1
    rcases (Nat.dvd_prime hp'.1).mp hpd' with h|h
    · exact hp.ne_one h
    · rw [h] at hpz; linarith [hp'.2]

/-- Upper bound after averaging over translates. All weights in this formula are
unrestricted by q, and the dependence on q is the totient density. -/
theorem selberg_progression_interval_bound {q a : ℕ} [NeZero q] (A : Finset ℕ) {x y z : ℝ}
    (hx : -1≤x) (hy : 0<y) (hz : 1≤z)
    (hI : ∀k∈A, x<k ∧ (k:ℝ)≤x+y)
    (hprime : ∀k∈A, (q*k+a).Prime ∧ z<(q*k+a:ℕ)) :
    let S := (Finset.Icc 1 ⌊z⌋₊).filter Squarefree
    let G := ∑d∈S,(d.totient:ℝ)⁻¹
    (A.card:ℝ)*(q.totient:ℝ) ≤ q*(y/G+(selbergWeightMass S/G)^2) := by
  intro S G
  obtain ⟨r,T,hr,hsub,hc,hrough⟩ := selberg_progression_to_rough A z hprime
  have hx' : 0≤x+r := by
    have h : (1:ℝ)≤r := by exact_mod_cast hr
    linarith
  have hT : T⊆(Ioc ⌊x+r⌋₊ ⌊x+r+y⌋₊).filter (fun n => n ≡ 0 [MOD 1]) := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := mem_image.mp (hsub hn)
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt hx').mpr ?_,Nat.le_floor ?_⟩,Nat.modEq_one ..⟩
    · push_cast; linarith [(hI k hk).1]
    · push_cast; linarith [(hI k hk).2]
  have HB := selberg_sieve_rough_ap_bound (q:=1) (a:=0) hx' hy (by decide) (by decide) hz T hT hrough
  have hf : (Icc 1 ⌊z⌋₊).filter (fun s => Squarefree s ∧ s.Coprime 1)=S := by simp [S]
  rw [hf] at HB
  simp only [Nat.cast_one,div_one] at HB
  have hT' : (T.card:ℝ)≤y/G+(selbergWeightMass S/G)^2 := HB.trans (add_le_add le_rfl (min_le_right ..))
  exact (show (A.card:ℝ)*(q.totient:ℝ)≤(q:ℝ)*T.card by exact_mod_cast hc).trans
    (mul_le_mul_of_nonneg_left hT' (Nat.cast_nonneg _))

end AnalyticNumberTheory.SieveMethods
