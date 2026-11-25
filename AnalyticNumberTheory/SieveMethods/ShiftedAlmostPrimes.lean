import AnalyticNumberTheory.SieveMethods.KuhnSieve
import AnalyticNumberTheory.SieveMethods.KuhnAlmostPrimes
import AnalyticNumberTheory.SieveMethods.ShiftedPrimeEstimates

/-!
# Primes at a fixed even distance from an almost prime

For each nonzero even integer h, there are ≫ₕ x/(log x)² primes p ≤ x
such that |p-h| is a product of at most three primes counted with
multiplicity. Kuhn's weighted sieve removes the possible fourth factor.
-/
noncomputable section
open Finset Set Real Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods
open AnalyticNumberTheory.PrimeDistribution Classical

/-- The primes up to x whose distance to h has at most three prime factors,
counted with multiplicity. -/
def shiftedAlmostPrimes (h : ℤ) (x : ℝ) : Finset ℕ :=
  (primeFinset x).filter (fun p => (primeShift h p).primeFactorsList.length≤3)

private theorem good_image_le (h : ℤ) (x : ℝ) :
    (atMostThreeFactors (shiftedPrimeSequence h x)).card≤(shiftedAlmostPrimes h x).card := by
  have hsub : atMostThreeFactors (shiftedPrimeSequence h x)⊆(shiftedAlmostPrimes h x).image (primeShift h) := by
    intro n hn; obtain ⟨hn,hlen⟩ := mem_filter.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨p,mem_filter.mpr ⟨(mem_filter.mp hp).1,hlen⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans card_image_le

private theorem shift_excludes_divisors {h : ℤ} (hh : h≠0) {p q : ℕ} (hp : p.Prime)
    (hl : h.natAbs<p) (hq : q.Prime) (hd : q∣primeShift h p) : q.Coprime h.natAbs := by
  apply hq.coprime_iff_not_dvd.mpr; intro hqh
  have h₁ : (q:ℤ)∣(p:ℤ)-h := Int.natCast_dvd.mpr hd
  have h₂ : (q:ℤ)∣h := Int.natCast_dvd.mpr hqh
  have hqp : q∣p := Int.natCast_dvd_natCast.mp (by simpa using dvd_add h₁ h₂)
  have he := (hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.ne_one
  have hpos : 0<h.natAbs := Int.natAbs_pos.mpr hh
  have := Nat.le_of_dvd hpos hqh; omega

private theorem shifted_main_at_eighth_root (h : ℤ) (hh₀ : h≠0) (hh : Even h) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ z : ℝ in atTop,
      c*z^8/(log z)^2≤((shiftedAlmostPrimes h (z^8)).card:ℝ) := by
  have hEven := Int.natAbs_even.mpr hh
  obtain ⟨K,hK,HK⟩ := shiftedPrime_log_mass hEven (Int.natAbs_ne_zero.mpr hh₀)
  obtain ⟨c,hc,hMain⟩ := shiftedPrime_main_lower hK
  obtain ⟨Q,hQ,hSq⟩ := kuhn_square_bound
  let a := kuhnScale/200*c
  let e := a/10
  have ha : 0<a := mul_pos (div_pos kuhnScale_pos (by norm_num)) hc
  have he : 0<e := div_pos ha (by norm_num)
  have hqpow : Tendsto (fun z : ℝ => z^(1/10:ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  refine ⟨a/2,by positivity,?_⟩
  filter_upwards [kuhn_weighted_sieve hK (by norm_num : (0:ℝ)<2),shiftedPrime_error_sum h he,
    shifted_log_power_small (d:=1/2) (by norm_num) 2 (c:=e/(2*Q)) (by positivity),
    hqpow.eventually_gt_atTop 2,eventually_ge_atTop (max 2 (h.natAbs:ℝ))] with z hKuhn hBV hsqSmall hlarge hz
  let x := z^8
  let t := z^kuhnPrimeExponent
  let y := z^kuhnLevel
  let A := shiftedPrimeSequence h x
  let X := logIntegral x
  let P := shiftedSievePrimes h.natAbs t
  let s := shiftedPrimeSieveData A X h.natAbs hEven
  let M := sievePrimeWindow P z t
  let D := sieveProductBelow P z
  let W := sieveEulerBelow P s.density z
  let F := shiftedPrimeError h x
  let J := x/(log z)^2
  have hz₂ := (le_max_left (2:ℝ) (h.natAbs:ℝ)).trans hz
  have hz₁ : 1≤z := by linarith
  have hz₀ : 0<z := by linarith
  have hlz := log_pos (by linarith : 1<z)
  have hsize : 2*x<t^3 := by
    change 2*z^8<(z^kuhnPrimeExponent)^3
    rw [←Real.rpow_natCast z 8,←Real.rpow_natCast (z^kuhnPrimeExponent) 3,←Real.rpow_mul hz₀.le,
      show kuhnPrimeExponent*(3:ℕ)=(1/10:ℝ)+8 by norm_num [kuhnPrimeExponent],Real.rpow_add hz₀]
    exact mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hz₀ _)
  have hzx : z≤x := by change z≤z^8; simpa only [pow_one] using pow_le_pow_right₀ hz₁ (by norm_num : 1≤8)
  have hx := hz₂.trans hzx
  have hx₀ := zero_lt_two.trans_le hx
  have hxH := (le_max_right (2:ℝ) (h.natAbs:ℝ)).trans (hz.trans hzx)
  have hzt : z≤t := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz₁ (by norm_num [kuhnPrimeExponent] : 1≤kuhnPrimeExponent)
  have hpos : 0≤X := (div_nonneg (sub_nonneg.mpr hx) (log_pos (by linarith : 1<x)).le).trans (shifted_logIntegral_bounds hx).1
  have hW (p : ℕ) (hp : p∈P) := (mem_shiftedSievePrimes.mp hp).1
  have H := HK A X t
  have hdist (d : ℕ) (hd : d∣sieveProductBelow P t) : |s.rem d|≤F d := by
    have hd' : d≠0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero (sieveProductBelow_squarefree hW t).ne_zero))
    have hcop : (sieveProductBelow P t).Coprime h.natAbs := by
      apply Nat.coprime_prod_left_iff.mpr; intro p hp; exact (mem_shiftedSievePrimes.mp (mem_filter.mp hp).1).2.2
    exact shiftedPrime_rem_le hEven hx hd' (hcop.of_dvd_left hd)
  have hweighted := hKuhn P s hW hpos (shiftedPrime_separation A X hEven) H F
    (fun d hd => shiftedPrimeError_nonneg hx (mem_Icc.mp hd).1) hdist
  have hmain := hMain hEven A hz₂ (H.mono_interval le_rfl hzt)
  have hAn (n : ℕ) (hn : n∈A) : 0<n ∧ (n:ℝ)≤2*x := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hpi := (mem_primeFinset_iff.mp (mem_filter.mp hp).1).2
    have hl := (mem_filter.mp hp).2
    have hc := primeShift_cast hl
    have hab : -(h.natAbs:ℤ)≤h := by have hh' : -h≤((-h).natAbs:ℤ) := Int.le_natAbs; simpa using neg_le_neg hh'
    have hp' : primeShift h p≤p+h.natAbs := by omega
    constructor
    · have hh' : h≤(h.natAbs:ℤ) := Int.le_natAbs; omega
    · exact (show ((primeShift h p:ℕ):ℝ)≤(p:ℝ)+h.natAbs by exact_mod_cast hp').trans (by linarith)
  have htags (n : ℕ) (hn : n∈A) (hnD : n.Coprime D) (q : ℕ) (hq : q∈n.primeFactorsList) (hqt : (q:ℝ)<t) : q∈M := by
    have ⟨hQp,hqd⟩ := (Nat.mem_primeFactorsList (hAn n hn).1.ne').mp hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hcop := shift_excludes_divisors hh₀ (mem_primeFinset_iff.mp (mem_filter.mp hp).1).1
      (mem_filter.mp hp).2 hQp hqd
    have hqm : q∈P := mem_shiftedSievePrimes.mpr ⟨hQp,hqt,hcop⟩
    refine mem_filter.mpr ⟨hqm,?_,hqt⟩
    by_contra hlt
    have hv : q∣D := dvd_prod_of_mem _ (mem_filter.mpr ⟨hqm,not_le.mp hlt⟩)
    exact hQp.not_dvd_one (by simpa [hnD.gcd_eq_one] using Nat.dvd_gcd hqd hv)
  have hcomb := kuhn_combinatorial_lower A M D (hz₁.trans hzt) (fun n hn => ⟨(hAn n hn).1.ne',(hAn n hn).2.trans_lt hsize⟩) htags
  have hsq := hSq A M (x:=2*x) (by positivity) hz₁ hAn (fun q hq => (mem_filter.mp hq).2.1)
  have hSqMain : ((kuhnSquareExceptions A M).card:ℝ)≤e*J := by
    apply hsq.trans
    rw [Real.rpow_ofNat,←Real.sqrt_eq_rpow] at hsqSmall
    change Q*(2*x)/sqrt z≤e*(x/(log z)^2)
    have Hsq : (log z)^2*(2*Q)≤e*sqrt z := by
      apply (le_div_iff₀ (by positivity : 0<2*Q)).mp
      convert hsqSmall using 1 <;> ring
    have hbound : 2*Q≤e*sqrt z/(log z)^2 := (le_div_iff₀ (sq_pos_of_pos hlz)).mpr (by linarith)
    calc Q*(2*x)/sqrt z=(2*Q)*x/sqrt z := by ring
         _ ≤ (e*sqrt z/(log z)^2)*x/sqrt z :=
           div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound hx₀.le) (sqrt_nonneg _)
         _ = _ := by field_simp [hlz.ne',(Real.sqrt_pos.mpr hz₀).ne'] <;> ring
  have hcard := good_image_le h x
  have hgood : ((atMostThreeFactors A).card:ℝ)≤(shiftedAlmostPrimes h x).card := by exact_mod_cast hcard
  have hBV' : (∑d∈Finset.Icc 1 ⌊y⌋₊,F d)≤e*J := by convert hBV using 1 <;> ring
  change kuhnScale/200*(X*W)-5/2*(∑d∈Finset.Icc 1 ⌊y⌋₊,F d)≤(siftedCountOf A D:ℝ)-1/2*∑q∈M,(siftedCountOf (sieveMultiple A q) D:ℝ) at hweighted
  have hm : c*J≤X*W := by convert hmain using 1 <;> ring
  have hbest := mul_le_mul_of_nonneg_left hm (div_nonneg kuhnScale_pos.le (by norm_num : (0:ℝ)≤200))
  have hJ : 0≤J := div_nonneg hx₀.le (sq_nonneg _)
  change a/2*x/(log z)^2≤((shiftedAlmostPrimes h x).card:ℝ)
  rw [show a/2*x/(log z)^2=a/2*J by dsimp [J]; ring]
  dsimp only [e,a] at hBV' hSqMain ⊢
  nlinarith only [hweighted,hcomb,hgood,hbest,hBV',hSqMain,mul_nonneg ha.le hJ]

/-- A positive-proportion lower bound on the two-prime scale for the
shifted almost primes. The constant can depend on the fixed even shift. -/
theorem shiftedAlmostPrimes_lower (h : ℤ) (hh₀ : h≠0) (hh : Even h) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      c*x/(log x)^2≤((shiftedAlmostPrimes h x).card:ℝ) := by
  obtain ⟨c,hc,H⟩ := shifted_main_at_eighth_root h hh₀ hh
  refine ⟨64*c,by positivity,?_⟩
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).eventually H,eventually_ge_atTop (2:ℝ)] with x hx hx₂
  have hx₀ : 0<x := by linarith
  have hxpow : (x^(1/8:ℝ))^8=x := by rw [←Real.rpow_natCast,←Real.rpow_mul hx₀.le]; norm_num
  rw [hxpow,Real.log_rpow hx₀] at hx
  convert hx using 1 <;> ring

/-- Infinitely many primes p have |p-h| a product of at most three primes,
with repetitions counted, for every fixed nonzero even integer h. -/
theorem infinite_primes_shift_threeFactors (h : ℤ) (hh₀ : h≠0) (hh : Even h) :
    Set.Infinite {p : ℕ | p.Prime ∧ (primeShift h p).primeFactorsList.length≤3} := by
  obtain ⟨c,hc,H⟩ := shiftedAlmostPrimes_lower h hh₀ hh
  intro hfin
  let N := hfin.toFinset.card
  obtain ⟨x,hx,hl,hbig,hx₂⟩ := (H.and ((shifted_log_power_small (d:=1/2) (by norm_num) 2 (c:=1) zero_lt_one).and
    (((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_gt_atTop ((N:ℝ)/c)).and (eventually_ge_atTop (2:ℝ))))).exists
  have hcard : (shiftedAlmostPrimes h x).card≤N := by
    apply Finset.card_le_card; intro p hp; obtain ⟨hp,hh⟩ := mem_filter.mp hp
    exact hfin.mem_toFinset.mpr ⟨(mem_primeFinset_iff.mp hp).1,hh⟩
  have hx₀ : 0<x := by linarith
  rw [Real.rpow_ofNat,one_mul,←Real.sqrt_eq_rpow] at hl
  rw [←Real.sqrt_eq_rpow] at hbig
  have hs := Real.sqrt_pos.mpr hx₀
  have hh' : (N:ℝ)<c*sqrt x := by linarith [(div_lt_iff₀ hc).mp hbig]
  have hl' := div_le_div_of_nonneg_left (mul_nonneg hc.le hx₀.le) (sq_pos_of_pos (log_pos (by linarith : 1<x))) hl
  have he : c*x/sqrt x=c*sqrt x := by apply (div_eq_iff hs.ne').mpr; rw [mul_assoc,←pow_two,Real.sq_sqrt hx₀.le]
  rw [he] at hl'; linarith only [hh',hl',hx,show ((shiftedAlmostPrimes h x).card:ℝ)≤N by exact_mod_cast hcard]

end AnalyticNumberTheory.SieveMethods
