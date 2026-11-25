import AnalyticNumberTheory.SieveMethods.ShiftedPrimeDensity

/-!
# Distribution of a shifted prime sequence

Restrict to primes larger than the absolute shift, so the difference has a
positive absolute value and the map to the sifted integers is injective.
Divisibility of the difference recovers a reduced residue class.
-/
noncomputable section
open Finset Real Set Filter MeasureTheory
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution Classical

/-- Prime inputs with a positive shifted value. -/
def shiftedPrimeInputs (h : ℤ) (x : ℝ) := (primeFinset x).filter (fun p => h.natAbs<p)

/-- Absolute value of the difference between a prime input and an integral shift. -/
def primeShift (h : ℤ) (p : ℕ) := ((p:ℤ)-h).natAbs

/-- Sequence to which the linear sieve is applied. -/
def shiftedPrimeSequence (h : ℤ) (x : ℝ) := (shiftedPrimeInputs h x).image (primeShift h)

private theorem shift_positive {h : ℤ} {p : ℕ} (hp : h.natAbs<p) : 0<(p:ℤ)-h := by
  have hh : h≤(h.natAbs:ℤ) := Int.le_natAbs
  omega

theorem primeShift_cast {h : ℤ} {p : ℕ} (hp : h.natAbs<p) :
    (primeShift h p:ℤ)=(p:ℤ)-h := Int.natAbs_of_nonneg (shift_positive hp).le

theorem primeShift_injOn (h : ℤ) (x : ℝ) : Set.InjOn (primeShift h) (shiftedPrimeInputs h x) := by
  intro p hp q hq he
  have he' := congrArg (fun n : ℕ => (n:ℤ)) he
  rw [primeShift_cast (mem_filter.mp hp).2,primeShift_cast (mem_filter.mp hq).2] at he'
  omega

private theorem natMod_cast (h : ℤ) {d : ℕ} (hd : d≠0) : (h.natMod d:ℤ)=h%(d:ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd))

theorem primeShift_dvd_iff {h : ℤ} {p d : ℕ} (hp : h.natAbs<p) (hd : d≠0) :
    d∣primeShift h p ↔ p≡h.natMod d [MOD d] := by
  rw [←Int.natCast_dvd_natCast,primeShift_cast hp,←Int.modEq_iff_dvd,←Int.natCast_modEq_iff,natMod_cast h hd]
  exact ⟨fun he => he.symm.trans (Int.mod_modEq ..).symm,fun he => (he.trans (Int.mod_modEq ..)).symm⟩

private theorem natMod_coprime {h : ℤ} {d : ℕ} (hd : d≠0) (hc : d.Coprime h.natAbs) :
    (h.natMod d).Coprime d := by
  have hh := Int.gcd_emod h (d:ℤ)
  rw [←natMod_cast h hd] at hh
  change ((h.natMod d:ℤ).natAbs).gcd ((d:ℤ).natAbs)=h.natAbs.gcd ((d:ℤ).natAbs) at hh
  simpa [Nat.Coprime,hc.symm.gcd_eq_one] using hh

private theorem class_count (x : ℝ) (d a : ℕ) :
    piAP x d a=(((primeFinset x).filter (fun p => p≡a [MOD d])).card:ℝ) := by
  unfold piAP primeCountingAP primeFinset
  rw [Nat.primesLE_eq_filter_Icc_one,Finset.filter_filter]

private theorem multiple_count {h : ℤ} {x : ℝ} {d : ℕ} (hd : d≠0) :
    (sieveMultiple (shiftedPrimeSequence h x) d).card=
      ((shiftedPrimeInputs h x).filter (fun p => p≡h.natMod d [MOD d])).card := by
  let S := shiftedPrimeInputs h x
  have he : sieveMultiple (shiftedPrimeSequence h x) d=
      (S.filter (fun p => p≡h.natMod d [MOD d])).image (primeShift h) := by
    ext n; simp only [sieveMultiple,mem_filter,shiftedPrimeSequence,Finset.mem_image]
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hd'⟩
      exact ⟨p,⟨hp,(primeShift_dvd_iff (mem_filter.mp hp).2 hd).mp hd'⟩,rfl⟩
    · rintro ⟨p,⟨hp,hp'⟩,rfl⟩
      exact ⟨⟨p,hp,rfl⟩,(primeShift_dvd_iff (mem_filter.mp hp).2 hd).mpr hp'⟩
  rw [he,Finset.card_image_of_injOn]
  exact (primeShift_injOn h x).mono (Finset.filter_subset ..)

private theorem abs_multiple_count_sub_piAP {h : ℤ} {x : ℝ} {d : ℕ} (hd : d≠0) :
    |((sieveMultiple (shiftedPrimeSequence h x) d).card:ℝ)-piAP x d (h.natMod d)|≤h.natAbs+1 := by
  rw [multiple_count hd,class_count]
  let A := (shiftedPrimeInputs h x).filter (fun p => p≡h.natMod d [MOD d])
  let B := (primeFinset x).filter (fun p => p≡h.natMod d [MOD d])
  have hsub : A⊆B := fun p hp => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
  have hset : B\A⊆range (h.natAbs+1) := by
    intro p hp; obtain ⟨hB,hn⟩ := mem_sdiff.mp hp
    obtain ⟨hp,hco⟩ := mem_filter.mp hB
    by_contra hn'; have hlarge : h.natAbs<p := by have := not_lt.mp (fun hl => hn' (mem_range.mpr hl)); omega
    exact hn (mem_filter.mpr ⟨mem_filter.mpr ⟨hp,hlarge⟩,hco⟩)
  have hcount := Finset.card_le_card hset
  rw [card_range,card_sdiff_of_subset hsub] at hcount
  have hab : A.card≤B.card := Finset.card_le_card hsub
  change |(A.card:ℝ)-(B.card:ℝ)|≤_
  rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
  have hnat : B.card≤h.natAbs+1+A.card := by omega
  exact_mod_cast (by linarith [show (B.card:ℝ)≤(h.natAbs:ℝ)+1+A.card by exact_mod_cast hnat] : -((A.card:ℝ)-B.card)≤(h.natAbs:ℝ)+1)

/-- The logarithmic integral is increasing and is comparable to x/log x
from below on the large positive half-line. -/
theorem shifted_logIntegral_bounds {x : ℝ} (hx : 2≤x) :
    (x-2)/log x≤logIntegral x ∧ logIntegral x≤(x-2)/log 2 := by
  have hl := log_pos (show 1<x by linarith)
  have hc : ContinuousOn (fun t : ℝ => (log t)⁻¹) (Set.Icc 2 x) := by
    apply ContinuousOn.inv₀ (Real.continuousOn_log.mono (fun t ht => by change t≠0; linarith [ht.1]))
    intro t ht; exact (log_pos (by linarith [ht.1])).ne'
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) hx
  have h₁ := intervalIntegral.integral_mono_on (μ:=volume) hx (intervalIntegrable_const (a:=2) (b:=x)) hi
    (f:=fun _ : ℝ => (log x)⁻¹) (fun t ht => inv_anti₀ (log_pos (by linarith [ht.1])) (log_le_log (by linarith [ht.1]) ht.2))
  have h₂ := intervalIntegral.integral_mono_on (μ:=volume) hx hi (intervalIntegrable_const (a:=2) (b:=x))
    (g:=fun _ : ℝ => (log 2)⁻¹) (fun t ht => inv_anti₀ (log_pos (by norm_num)) (log_le_log (by norm_num) ht.1))
  simpa only [logIntegral,intervalIntegral.integral_const,smul_eq_mul,div_eq_mul_inv] using And.intro h₁ h₂

theorem piAPError_le_maximal {x : ℝ} (hx : 2≤x) {d a : ℕ} (hd : d≠0) (ha : a.Coprime d) :
    |piAP x d a-logIntegral x/d.totient|≤maximalPiAPError x d := by
  unfold maximalPiAPError
  apply le_csSup (s:={v : ℝ | ∃ y ∈ Set.Icc 2 x, ∃ a : ℕ, a.Coprime d ∧ v=|piAP y d a-logIntegral y/d.totient|}) _ ⟨x,⟨hx,le_rfl⟩,a,ha,rfl⟩
  refine ⟨(Nat.primeCounting ⌊x⌋₊:ℝ)+x/log 2,?_⟩
  rintro v ⟨y,hy,c,hc,rfl⟩
  have hπ := (piAP_le_primeCounting y d c).trans (show (Nat.primeCounting ⌊y⌋₊:ℝ)≤(Nat.primeCounting ⌊x⌋₊:ℝ) by
    exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hy.2))
  have hli := shifted_logIntegral_bounds hy.1
  have hl : 0≤logIntegral y := (div_nonneg (sub_nonneg.mpr hy.1) (log_pos (by linarith [hy.1])).le).trans hli.1
  have hupper := (div_le_self hl (show 1≤(d.totient:ℝ) by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd))).trans hli.2
  have hπ₀ : 0≤piAP y d c := Nat.cast_nonneg _
  rw [abs_le]; constructor
  · have hh : (y-2)/log 2≤x/log 2 := by gcongr <;> linarith [hy.2]
    linarith only [hπ₀,hupper,hh,Nat.cast_nonneg (α:=ℝ) (Nat.primeCounting ⌊x⌋₊)]
  · linarith only [hπ,div_nonneg hl (Nat.cast_nonneg d.totient),div_nonneg (show 0≤x by linarith) (log_pos (by norm_num : (1:ℝ)<2)).le]

/-- Pointwise remainder for the shifted sequence, controlled by the maximal
prime-counting discrepancy and the deleted initial primes. -/
theorem shiftedPrime_rem_le {h : ℤ} (hh : Even h.natAbs) {x : ℝ} (hx : 2≤x) {d : ℕ}
    (hd : d≠0) (hc : d.Coprime h.natAbs) :
    |(shiftedPrimeSieveData (shiftedPrimeSequence h x) (logIntegral x) h.natAbs hh).rem d|≤
      maximalPiAPError x d+(h.natAbs+1) := by
  let s := shiftedPrimeSieveData (shiftedPrimeSequence h x) (logIntegral x) h.natAbs hh
  have h₁ := abs_multiple_count_sub_piAP (h:=h) (x:=x) hd
  have h₂ := piAPError_le_maximal hx hd (natMod_coprime hd hc)
  change |((sieveMultiple (shiftedPrimeSequence h x) d).card:ℝ)-s.density d*logIntegral x|≤_
  rw [show s.density d=1/(d.totient:ℝ) from shiftedPrime_density _ _ hh hd hc,one_div,inv_mul_eq_div]
  exact (abs_sub_le _ (piAP x d (h.natMod d)) _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end AnalyticNumberTheory.SieveMethods
