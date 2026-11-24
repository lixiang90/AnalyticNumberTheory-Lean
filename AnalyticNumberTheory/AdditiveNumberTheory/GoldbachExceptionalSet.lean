import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachBinaryMean
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachBinaryPrimePowers

/-!
# Almost all even integers are sums of two primes

A positive binary singular series and the logarithmic mean saving imply that
the set of even exceptions has size O(N/(log N)^A) for every natural A.
-/

noncomputable section
open Finset Filter
open scoped Classical Topology
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Positive even integers up to N having no representation as a sum of two primes. -/
def goldbachExceptionalSet (N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter (fun n => Even n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)

private theorem card_goldbachExceptionalSet_le {N : ℕ} {c X : ℝ} (hc : 0<c) (hX : 2≤X)
    (hpos : ∀ n : ℕ, Even n → 2 ≤ n → c ≤ goldbachBinarySingularSeries n)
    (hpowers : 42*Real.sqrt N*Real.log N ≤ c*X/4) :
    ((goldbachExceptionalSet N).card:ℝ) ≤ X +
      (∑ n ∈ Ioc 0 N, |goldbachBinaryWeighted n-goldbachBinarySingularSeries n*(n-1:ℕ)|)/(c*X/4) := by
  let E := goldbachExceptionalSet N
  let small := E.filter (fun n : ℕ => (n:ℝ) ≤ X)
  let large := E.filter (fun n : ℕ => ¬(n:ℝ) ≤ X)
  have hcut : 0<c*X/4 := by positivity
  have hs : small ⊆ Ioc 0 ⌊X⌋₊ := by
    intro n hn
    obtain ⟨he,hx⟩ := mem_filter.mp hn
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp he).1).1,(Nat.le_floor_iff (by linarith)).mpr hx⟩
  have hs' : (small.card:ℝ) ≤ X := by
    have h := card_le_card hs
    simp only [Nat.card_Ioc,Nat.sub_zero] at h
    exact (show (small.card:ℝ) ≤ ⌊X⌋₊ by exact_mod_cast h).trans (Nat.floor_le (by linarith))
  let err := fun n : ℕ => |goldbachBinaryWeighted n-goldbachBinarySingularSeries n*(n-1:ℕ)|
  have hb (n : ℕ) (hn : n∈large) : c*X/4 ≤ err n := by
    obtain ⟨hen,hgt⟩ := mem_filter.mp hn
    obtain ⟨hnN,hpar,hno⟩ := mem_filter.mp hen
    obtain ⟨hn1,hnN⟩ := mem_Ioc.mp hnN
    have hnx : X<(n:ℝ) := not_le.mp hgt
    have hn2 : 2 ≤ n := by exact_mod_cast hX.trans hnx.le
    have hbound := goldbachBinaryWeighted_le_of_no_prime_pair hn1 hno
    have hp' : goldbachBinaryWeighted n ≤ c*X/4 := by
      refine hbound.trans (le_trans ?_ hpowers)
      gcongr <;> exact_mod_cast hnN
    have hn' : (n:ℝ)-1 = (n-1:ℕ) := by rw [Nat.cast_sub hn1,Nat.cast_one]
    have hprod := mul_le_mul_of_nonneg_right (hpos n hpar hn2)
      (Nat.cast_nonneg (α := ℝ) (n-1))
    change c*X/4 ≤ |goldbachBinaryWeighted n-goldbachBinarySingularSeries n*(n-1:ℕ)|
    have hh := neg_le_abs (goldbachBinaryWeighted n-goldbachBinarySingularSeries n*(n-1:ℕ))
    rw [← hn'] at hprod hh ⊢
    nlinarith [mul_le_mul_of_nonneg_left hnx.le hc.le, mul_le_mul_of_nonneg_left hX hc.le]
  have he : large ⊆ Ioc 0 N := fun n hn => (mem_filter.mp (mem_filter.mp hn).1).1
  have hl : (large.card:ℝ) ≤ (∑ n ∈ Ioc 0 N, err n)/(c*X/4) := by
    apply (le_div_iff₀ hcut).mpr
    calc
      _ = ∑ _n ∈ large, c*X/4 := by simp [nsmul_eq_mul]
      _ ≤ ∑ n ∈ large, err n := sum_le_sum hb
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg he (fun _ _ _ => abs_nonneg _)
  have hcard : small.card + large.card = E.card := card_filter_add_card_filter_not _
  change (E.card:ℝ) ≤ X + _
  rw [← hcard,Nat.cast_add]
  exact add_le_add hs' hl

/-- The number of exceptional even integers is O(N/(log N)^A), for every A.
Representations allow repeated primes. -/
theorem goldbachExceptionalSet_card_isBigO (A : ℕ) :
    (fun N : ℕ => ((goldbachExceptionalSet N).card:ℝ)) =O[atTop]
      (fun N : ℕ => (N:ℝ)/(Real.log N)^A) := by
  obtain ⟨c,hc,hpos⟩ := goldbachBinarySingularSeries_pos_of_even
  obtain ⟨D,hD,hmean⟩ := (goldbachBinaryWeighted_mean_isBigO (2*A)).exists_pos
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hslow (j : ℕ) (K : ℝ) : ∀ᶠ N : ℕ in atTop, K*(Real.log N)^j ≤ Real.sqrt N := by
    have ho := (isLittleO_log_rpow_rpow_atTop (j:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
    have ht := ((tendsto_const_nhds (x := K)).mul ho).eventually (gt_mem_nhds (by simp : K*0<1))
    filter_upwards [hcast.eventually ht,eventually_ge_atTop (1:ℕ)] with N h hN
    change K*((Real.log N)^(j:ℝ)/(N:ℝ)^(1/2:ℝ))<1 at h
    rw [Real.rpow_natCast,← Real.sqrt_eq_rpow,← mul_div_assoc,div_lt_one (Real.sqrt_pos.mpr (by exact_mod_cast hN))] at h
    exact h.le
  apply Asymptotics.IsBigO.of_bound (1+4*D/c)
  filter_upwards [hslow A 2,hslow (A+1) (168/c),hmean,(Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1,
    eventually_ge_atTop (2:ℕ)] with N hs hs' hm hL hN
  let L := Real.log N
  change 1 ≤ L at hL
  have hL0 : 0<L := by linarith
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hsq := Real.sq_sqrt hN0.le
  have hr := Real.sqrt_pos.mpr hN0
  have hcut : 2 ≤ (N:ℝ)/L^A := (le_div_iff₀ (by positivity)).mpr
    (hs.trans (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (by omega : 1≤N)))))
  have hpow : 42*Real.sqrt N*Real.log N ≤ c*((N:ℝ)/L^A)/4 := by
    change (168/c)*L^(A+1) ≤ Real.sqrt N at hs'
    have hb := mul_le_mul_of_nonneg_right hs' (mul_nonneg hc.le hr.le)
    have he : (168/c)*L^(A+1)*(c*Real.sqrt N) = 168*Real.sqrt N*L*L^A := by rw [pow_succ]; field_simp <;> ring
    rw [he] at hb
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
    change 42*Real.sqrt N*L*4*L^A ≤ _
    nlinarith
  have h := card_goldbachExceptionalSet_le hc hcut hpos hpow
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)] at hm
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  refine h.trans ?_
  calc
    _ ≤ (N:ℝ)/L^A + (D*((N:ℝ)^2/L^(2*A)))/(c*(N/L^A)/4) := by gcongr
    _ = _ := by change _ = (1+4*D/c)*((N:ℝ)/L^A); rw [mul_comm 2 A,pow_mul]; field_simp <;> ring

/-- The exceptional even integers have natural density zero. -/
theorem almost_all_even_sum_two_primes :
    Tendsto (fun N : ℕ => ((goldbachExceptionalSet N).card:ℝ)/N) atTop (𝓝 0) := by
  obtain ⟨D,hD,hm⟩ := (goldbachExceptionalSet_card_isBigO 1).exists_pos
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Tendsto (fun N : ℕ => D/Real.log N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ ht
  filter_upwards [hm,hlog.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with N h hL hN
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),pow_one] at h
  apply (div_le_iff₀ hn).mpr
  exact h.trans_eq (by ring)

/-- Among the first M positive even numbers, the proportion admitting a
representation as a sum of two primes tends to one. -/
theorem even_sum_two_primes_proportion_tendsto_one :
    Tendsto (fun M : ℕ =>
      (((Ioc 0 M).filter (fun m => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=2*m)).card:ℝ)/M)
      atTop (𝓝 1) := by
  let repr := fun m : ℕ => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=2*m
  have hc (M : ℕ) : ((Ioc 0 M).filter (fun m => ¬repr m)).card =
      (goldbachExceptionalSet (2*M)).card := by
    refine card_bij (fun m _ => 2*m) ?_ ?_ ?_
    · intro m hm
      obtain ⟨hm,hr⟩ := mem_filter.mp hm
      obtain ⟨hm0,hmM⟩ := mem_Ioc.mp hm
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,even_two_mul m,hr⟩
    · intro i _ j _ he; omega
    · intro n hn
      obtain ⟨hn,⟨j,hj⟩,hr⟩ := mem_filter.mp hn
      obtain ⟨hn0,hnM⟩ := mem_Ioc.mp hn
      have he : 2*j=n := by omega
      refine ⟨j,mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,?_⟩,he⟩
      simpa [repr,he] using hr
  have hc' (M : ℕ) : ((Ioc 0 M).filter repr).card + (goldbachExceptionalSet (2*M)).card = M := by
    rw [← hc,card_filter_add_card_filter_not]; simp
  have ht : Tendsto (fun m : ℕ => 2*m) atTop atTop :=
    tendsto_atTop_mono (fun m => show m ≤ 2*m by omega) tendsto_id
  have he := (tendsto_const_nhds (x := (2:ℝ))).mul (almost_all_even_sum_two_primes.comp ht)
  have hl := (tendsto_const_nhds (x := (1:ℝ))).sub he
  simp only [mul_zero,sub_zero] at hl
  refine hl.congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  change 1-2*((goldbachExceptionalSet (2*m)).card/(2*m:ℕ)) = (((Ioc 0 m).filter repr).card:ℝ)/m
  have hcast : ((((Ioc 0 m).filter repr).card:ℝ) + (goldbachExceptionalSet (2*m)).card) = m := by exact_mod_cast hc' m
  push_cast
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  field_simp
  linarith

end AnalyticNumberTheory.AdditiveNumberTheory
