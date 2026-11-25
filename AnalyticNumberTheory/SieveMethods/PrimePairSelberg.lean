import AnalyticNumberTheory.SieveMethods.PrimePairDenominator
import AnalyticNumberTheory.SieveMethods.ShiftedPrimeProgressions
import AnalyticNumberTheory.SieveMethods.SelbergSieve

/-!
# Selberg's sieve on the prime inputs for a pair of primes

An integral translation of all primes up to x keeps both sides of the
shift while preserving each divisibility condition. The remainders are
therefore exactly discrepancies in reduced residue classes.
-/

noncomputable section
open Finset Real BoundingSieve
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution Classical

/-- Number of prime inputs p ≤ x for which |p − h| is also prime. -/
def primePairCount (x : ℝ) (h : ℤ) :=
  ((primeFinset x).filter (fun p => (primeShift h p).Prime)).card

private def modulus (h : ℕ) (z : ℝ) :=
  selbergPrimeProd z / (selbergPrimeProd z).gcd h

private theorem mod_dvd (h : ℕ) (z : ℝ) : modulus h z ∣ selbergPrimeProd z :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..)

private theorem mod_sf (h : ℕ) (z : ℝ) : Squarefree (modulus h z) :=
  (selbergPrimeProd_squarefree z).squarefree_of_dvd (mod_dvd h z)

private theorem mod_coprime (h : ℕ) (z : ℝ) : (modulus h z).Coprime h :=
  Nat.coprime_div_gcd_of_squarefree (selbergPrimeProd_squarefree z)

private theorem mod_dvd_of_small {z : ℝ} {h d : ℕ} (hh : h≠0) (hd : Squarefree d)
    (hz : (d:ℝ)≤z) (hc : d.Coprime h) : d∣modulus h z := by
  rw [← Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_dvd_iff (mod_sf h z).ne_zero]
  rw [modulus,Nat.primeFactors_div_gcd (selbergPrimeProd_squarefree z) hh,primeFactors_selbergPrimeProd]
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  refine mem_sdiff.mpr ⟨mem_selbergPrimeFinset_iff.mpr ⟨hp',?_⟩,?_⟩
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) hpd) hz
  · exact fun hph => (hp'.coprime_iff_not_dvd.mp (hc.coprime_dvd_left hpd)) (Nat.dvd_of_mem_primeFactors hph)

private def offset (h : ℤ) (P : ℕ) := ((P:ℤ)*h.natAbs-h).toNat

private theorem offset_cast (h : ℤ) {P : ℕ} (hP : 0<P) : (offset h P:ℤ)=(P:ℤ)*h.natAbs-h := by
  apply Int.toNat_of_nonneg
  have hh : h≤(h.natAbs:ℤ) := Int.le_natAbs
  have hp : (1:ℤ)≤P := by exact_mod_cast hP
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Int.natCast_nonneg h.natAbs)]

private theorem offset_dvd {h : ℤ} {p P d : ℕ} (hP : 0<P) (hd : d∣P) :
    d∣p+offset h P ↔ (d:ℤ)∣(p:ℤ)-h := by
  rw [← Int.natCast_dvd_natCast,Nat.cast_add,offset_cast _ hP,show (p:ℤ)+((P:ℤ)*h.natAbs-h)=((p:ℤ)-h)+(P:ℤ)*h.natAbs by ring]
  exact dvd_add_left (dvd_mul_of_dvd_left (by exact_mod_cast hd) _)

private theorem offset_modEq {h : ℤ} {p P d : ℕ} (hP : 0<P) (hd : d∣P) :
    d∣p+offset h P ↔ p≡h.natMod d [MOD d] := by
  have hd0 : d≠0 := ne_zero_of_dvd_ne_zero hP.ne' hd
  have hcast : (h.natMod d:ℤ)=h%(d:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd0))
  rw [offset_dvd hP hd,←Int.modEq_iff_dvd,←Int.natCast_modEq_iff,hcast]
  exact ⟨fun he => he.symm.trans (Int.mod_modEq ..).symm,fun he => (he.trans (Int.mod_modEq ..)).symm⟩

private def sieve (h : ℤ) (hh : Even h.natAbs) (x z : ℝ) : BoundingSieve where
  support := (primeFinset x).image (fun p => p+offset h (modulus h.natAbs z))
  prodPrimes := modulus h.natAbs z
  prodPrimes_squarefree := mod_sf _ _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := logIntegral x
  nu := ⟨fun n => (n.totient:ℝ)⁻¹,by simp⟩
  nu_mult := ⟨by simp,fun {a b} hab => by simp [Nat.totient_mul hab,mul_comm]⟩
  nu_pos_of_prime p hp _ := inv_pos.mpr (Nat.cast_pos.mpr (Nat.totient_pos.mpr hp.pos))
  nu_lt_one_of_prime p hp hpP := by
    have hc := (mod_coprime h.natAbs z).coprime_dvd_left hpP
    have hp2 : p≠2 := fun he => (hp.coprime_iff_not_dvd.mp hc) (he ▸ hh.two_dvd)
    have hp3 : 3≤p := by have := hp.two_le; omega
    change ((p.totient:ℝ)⁻¹)<1
    rw [Nat.totient_prime hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (show 1<p-1 by omega))

private theorem sieve_den (h : ℤ) (hh : Even h.natAbs) (h0 : h.natAbs≠0) (x : ℝ) {z : ℝ} (hz : 1≤z) :
    selbergG (sieve h hh x z) z=primePairDenominator h.natAbs z := by
  let s := sieve h hh x z
  have he : s.prodPrimes.divisors.filter (fun d : ℕ => (d:ℝ)≤z)=
      (Icc 1 ⌊z⌋₊).filter (fun d => Squarefree d ∧ d.Coprime h.natAbs) := by
    ext d
    simp only [mem_filter,Nat.mem_divisors,mem_Icc]
    constructor
    · rintro ⟨⟨hd,_⟩,hdz⟩
      have hs := s.squarefree_of_dvd_prodPrimes hd
      exact ⟨⟨Nat.pos_of_ne_zero hs.ne_zero,Nat.le_floor hdz⟩,hs,(mod_coprime _ _).coprime_dvd_left hd⟩
    · rintro ⟨⟨_,hdz⟩,hs,hc⟩
      have hz' := (Nat.le_floor_iff (by linarith : 0≤z)).mp hdz
      exact ⟨⟨mod_dvd_of_small h0 hs hz' hc,s.prodPrimes_ne_zero⟩,hz'⟩
  change selbergG s z=_
  rw [selbergG,he,primePairDenominator]
  apply sum_congr rfl
  intro d hd
  have hs := (mem_filter.mp hd).2.1
  have hc := (mem_filter.mp hd).2.2
  rw [←s.selbergTerms_isMultiplicative.prod_primeFactors hs]
  apply prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpc := hc.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)
  have hp2 : p≠2 := fun he => (hp'.coprime_iff_not_dvd.mp hpc) (he ▸ hh.two_dvd)
  have h3 : (3:ℝ)≤p := by exact_mod_cast (show 3≤p by have := hp'.two_le;omega)
  rw [s.selbergTerms_apply,hp'.primeFactors,prod_singleton]
  change (p.totient:ℝ)⁻¹*(1-(p.totient:ℝ)⁻¹)⁻¹=_
  rw [Nat.totient_prime hp',Nat.cast_sub hp'.one_le,Nat.cast_one]
  have h1 : (p:ℝ)-1≠0 := by linarith
  rw [show 1-((p:ℝ)-1)⁻¹=((p:ℝ)-2)/(p-1) by field_simp [h1];ring,inv_div]
  field_simp [h1]

private theorem sieve_rem {h : ℤ} (hh : Even h.natAbs) {x z : ℝ} (hx : 2≤x) {d : ℕ}
    (hd : d∣modulus h.natAbs z) : |(sieve h hh x z).rem d|≤maximalPiAPError x d := by
  let s := sieve h hh x z
  let P := modulus h.natAbs z
  have hp := Nat.pos_of_ne_zero (mod_sf h.natAbs z).ne_zero
  have he : s.support.filter (fun n => d∣n)=
      ((primeFinset x).filter (fun p => p≡h.natMod d [MOD d])).image (fun p => p+offset h P) := by
    ext m
    change m∈((primeFinset x).image _).filter _ ↔ _
    simp only [mem_image,mem_filter]
    constructor
    · rintro ⟨⟨p,hp',rfl⟩,hpd⟩
      exact ⟨p,⟨hp',(offset_modEq hp hd).mp hpd⟩,rfl⟩
    · rintro ⟨p,⟨hp',hpd⟩,rfl⟩
      exact ⟨⟨p,hp',rfl⟩,(offset_modEq hp hd).mpr hpd⟩
  have hmult : s.multSum d=piAP x d (h.natMod d) := by
    rw [multSum_eq_card_of_weights_one (fun _ => rfl),he,card_image_of_injective _ (add_left_injective _),piAP_eq_primeFinset_card]
  have hd0 := ne_zero_of_dvd_ne_zero hp.ne' hd
  change |s.multSum d-(d.totient:ℝ)⁻¹*logIntegral x|≤_
  rw [hmult,inv_mul_eq_div]
  exact piAPError_le_maximal hx hd0 (shiftedPrime_residue_coprime hd0 ((mod_coprime _ _).coprime_dvd_left hd))

private theorem count_le_sifted {h : ℤ} (hh : Even h.natAbs) (x : ℝ) {z : ℝ} (hz : 1≤z) :
    (primePairCount x h:ℝ)≤2*z+1+(sieve h hh x z).siftedSum := by
  let s := sieve h hh x z
  let T := (primeFinset x).filter (fun p => (primeShift h p).Prime)
  let small (p : ℕ) := (primeShift h p:ℝ)≤z
  let Z := ⌊z⌋₊
  let P := modulus h.natAbs z
  have hp := Nat.pos_of_ne_zero (mod_sf h.natAbs z).ne_zero
  have hsmall : (T.filter small).card≤2*Z+1 := by
    have h := Finset.card_le_card_of_injOn (s:=T.filter small) (t:=Icc (-(Z:ℤ)) Z) (fun p : ℕ => (p:ℤ)-h)
      (by
        intro p hmem
        have hlim : primeShift h p≤Z := Nat.le_floor (mem_filter.mp hmem).2
        have hi : |(p:ℤ)-h|≤(Z:ℤ) := by rw [←Int.natCast_natAbs];exact_mod_cast hlim
        exact mem_Icc.mpr (abs_le.mp hi))
      (fun p _ q _ he => by dsimp at he; omega)
    rw [Int.card_Icc] at h;omega
  have hlarge : (T.filter (fun p => ¬small p)).card≤(s.support.filter (fun n => P.Coprime n)).card := by
    apply Finset.card_le_card_of_injOn (fun p => p+offset h P) _ (add_left_injective _).injOn
    intro p hpT
    obtain ⟨hpT,hl⟩ := mem_filter.mp hpT
    obtain ⟨hpX,hpr⟩ := mem_filter.mp hpT
    refine mem_filter.mpr ⟨mem_image.mpr ⟨p,hpX,rfl⟩,Nat.coprime_of_dvd fun r hr hrP hrd => ?_⟩
    have hrq : r∣primeShift h p := Int.natCast_dvd.mp ((offset_dvd hp hrP).mp hrd)
    have he := ((Nat.dvd_prime hpr).mp hrq).resolve_left hr.ne_one
    have hrz := (prime_dvd_selbergPrimeProd_iff hr).mp (hrP.trans (mod_dvd _ _))
    apply hl; change (primeShift h p:ℝ)≤z; rwa [←he]
  have hpart := T.card_filter_add_card_filter_not small
  change (T.card:ℝ)≤2*z+1+s.siftedSum
  rw [siftedSum_eq_card_of_weights_one (fun _ => rfl)]
  have hZ : (Z:ℝ)≤z := Nat.floor_le (by linarith)
  have he : T.card≤2*Z+1+(s.support.filter (fun n => P.Coprime n)).card := by omega
  change (T.card:ℝ)≤2*z+1+((s.support.filter (fun n => P.Coprime n)).card:ℝ)
  exact (show (T.card:ℝ)≤2*(Z:ℝ)+1+((s.support.filter (fun n => P.Coprime n)).card:ℝ) by exact_mod_cast he).trans (by gcongr)

/-- The divisor-square majorant for a Selberg coefficient with weights bounded by one. -/
theorem abs_lambdaSquared_le_divisors_sq {w : ℕ → ℝ} (hw : ∀ n, |w n|≤1) (d : ℕ) :
    |lambdaSquared w d|≤(d.divisors.card:ℝ)^2 := by
  unfold lambdaSquared
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _a∈d.divisors, ∑ _b∈d.divisors, (1:ℝ) := by
          apply sum_le_sum
          intro a _
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
          split_ifs
          · rw [abs_mul];exact (mul_le_mul (hw a) (hw b) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
          · norm_num
       _ = _ := by simp; ring

/-- Finite Selberg upper bound for prime pairs, uniform in the integral shift.
The small complementary primes cost at most 2z+1, and every remaining
discrepancy occurs at a squarefree modulus of size at most z². -/
theorem primePairCount_selberg {h : ℤ} (hh : Even h.natAbs) (h0 : h.natAbs≠0)
    {x z : ℝ} (hx : 2≤x) (hz : 1≤z) :
    (primePairCount x h:ℝ) ≤ 2*z+1 + logIntegral x/primePairDenominator h.natAbs z +
      ∑d∈(Icc 1 ⌊z^2⌋₊).filter Squarefree, (d.divisors.card:ℝ)^2*maximalPiAPError x d := by
  let s := sieve h hh x z
  let S : SelbergSieve := { s with level := z^2, one_le_level := one_le_pow₀ hz }
  have H := selberg_upper_bound_level S
  change s.siftedSum≤s.totalMass/selbergG s (√(z^2))+
    ∑d∈s.prodPrimes.divisors.filter (fun d : ℕ => (d:ℝ)≤z^2),
      |lambdaSquared (selbergOptW s (√(z^2))) d| * |s.rem d| at H
  rw [Real.sqrt_sq (by linarith : 0≤z),sieve_den h hh h0 x hz] at H
  let D := s.prodPrimes.divisors.filter (fun d : ℕ => (d:ℝ)≤z^2)
  let E := (Icc 1 ⌊z^2⌋₊).filter Squarefree
  have hsub : D⊆E := by
    intro d hd;obtain ⟨hd,hle⟩ := mem_filter.mp hd
    have hs := s.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero,Nat.le_floor hle⟩,hs⟩
  have herr :
      (∑d∈D,|lambdaSquared (selbergOptW s z) d| * |s.rem d|)≤
        ∑d∈E,(d.divisors.card:ℝ)^2*maximalPiAPError x d := by
    refine (Finset.sum_le_sum (g:=fun d : ℕ => (d.divisors.card:ℝ)^2*maximalPiAPError x d) ?_).trans
      (sum_le_sum_of_subset_of_nonneg hsub ?_)
    · intro d hd
      exact mul_le_mul (abs_lambdaSquared_le_divisors_sq (selbergOptW_abs_le_one hz) d)
        (sieve_rem hh hx (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)) (abs_nonneg _) (sq_nonneg _)
    · intro d hd _
      exact mul_nonneg (sq_nonneg _) ((abs_nonneg _).trans (piAPError_le_maximal hx (mem_filter.mp hd).2.ne_zero (Nat.coprime_one_left _)))
  change s.siftedSum≤logIntegral x/primePairDenominator h.natAbs z+_ at H
  linarith only [H,herr,count_le_sifted hh x hz]

end AnalyticNumberTheory.SieveMethods
