import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSieveAverage
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachUniformBinaryUpper
import AnalyticNumberTheory.AnalyticTools.Summation.LogarithmicWeights

/-!
# The mean loss of one Goldbach logarithm

The large-prime contribution is controlled by Abel summation of the binary
sieve factor along shifted primes. For primes below the square root it is
enough to count all possible choices of the second summand.
-/

noncomputable section
open Finset Real Filter
open AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.AdditiveNumberTheory

private def largePrimeSet (N : ℕ) := ((Icc 2 N).filter Nat.Prime).filter (fun p : ℕ => sqrt N≤p)

private theorem largePrime_log_deficit :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 4≤N →
      (∑p∈largePrimeSet N,goldbachSieveFactor (N-p)*(log N-log p))≤C*N/log N := by
  obtain ⟨C,hC,H⟩ := goldbachPrimeSieveFactor_average
  refine ⟨2*C,by positivity,?_⟩
  intro N hN
  have hn : (4:ℝ)≤N := by exact_mod_cast hN
  have hL : 0<log N := Real.log_pos (by linarith)
  have hroot : 2≤sqrt N := (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  let P := (largePrimeSet N).filter (fun p => p<N)
  let a (p:ℕ) := if p∈P then goldbachSieveFactor (N-p) else 0
  have hnon (p:ℕ) : 0≤goldbachSieveFactor (N-p) := zero_le_one.trans (one_le_goldbachSieveFactor _)
  have hlin (t:ℝ) (ht : t∈Set.Icc 1 (N:ℝ)) :
      (∑p∈Icc 1 ⌊t⌋₊,a p)≤(2*C/log N)*t := by
    simp only [a,←sum_filter]
    by_cases hl : sqrt N≤t
    · have hsub : (Icc 1 ⌊t⌋₊).filter (fun p => p∈P) ⊆ (primeFinset t).filter (fun p => p<N) := by
        intro p hp
        obtain ⟨hi,hp⟩ := mem_filter.mp hp
        obtain ⟨_,hfloor⟩ := mem_Icc.mp hi
        obtain ⟨hb,hpN⟩ := mem_filter.mp hp
        have hprime := (mem_filter.mp (mem_filter.mp hb).1).2
        exact mem_filter.mpr ⟨mem_primeFinset_iff.mpr ⟨hprime,(Nat.cast_le.mpr hfloor).trans (Nat.floor_le (zero_le_one.trans ht.1))⟩,hpN⟩
      apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnon p)).trans
      apply (H hl (hroot.trans hl)).trans
      have hlog : log N/2≤log t := by rw [←Real.log_sqrt (by positivity)];exact log_le_log (by positivity) hl
      have htpos : 0<log t := by linarith
      rw [div_mul_eq_mul_div,div_le_div_iff₀ htpos hL]
      nlinarith [mul_nonneg (mul_nonneg hC.le (zero_le_one.trans ht.1)) (by linarith : 0≤2*log t-log N)]
    · have hE : (Icc 1 ⌊t⌋₊).filter (fun p => p∈P) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hi,hp⟩ := mem_filter.mp hp
        have hpt : (p:ℝ)≤t := (Nat.cast_le.mpr (mem_Icc.mp hi).2).trans (Nat.floor_le (zero_le_one.trans ht.1))
        exact hl ((mem_filter.mp (mem_filter.mp hp).1).2.trans hpt)
      rw [hE,sum_empty];exact mul_nonneg (by positivity) (zero_le_one.trans ht.1)
  have HS := sum_log_deficit_le (by linarith : (1:ℝ)≤N) a hlin
  rw [Nat.floor_natCast] at HS
  have hsub : P⊆Icc 1 N := fun p hp => by
    obtain ⟨h₂,hN⟩ := mem_Icc.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
    exact mem_Icc.mpr ⟨by omega,hN⟩
  have he : ∑p∈Icc 1 N,a p*(log N-log p)=∑p∈P,goldbachSieveFactor (N-p)*(log N-log p) := by
    rw [←sum_subset hsub]
    · apply sum_congr rfl;intro p hp;simp [a,hp]
    · intro p _ hp;simp [a,hp]
  rw [he] at HS
  have hlarge : ∑p∈largePrimeSet N,goldbachSieveFactor (N-p)*(log N-log p) =
      ∑p∈P,goldbachSieveFactor (N-p)*(log N-log p) := by
    apply (sum_subset (filter_subset ..) _).symm
    intro p hp hp'
    have hle := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
    have heq : p=N := by
      by_contra h
      exact hp' (mem_filter.mpr ⟨hp,by omega⟩)
    simp [heq]
  rw [hlarge]
  apply HS.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hL.le
  nlinarith

/-- A binary count weighted by the logarithmic deficit of the first prime. -/
theorem goldbach_binary_log_deficit :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      (∑p∈(Icc 2 N).filter Nat.Prime,(goldbachRepCount (N-p):ℝ)*(log N-log p)) ≤
        C*((N:ℝ)^2/(log N)^3) := by
  obtain ⟨B,hB,HB⟩ := goldbachRepCount_uniform_upper
  obtain ⟨D,hD,HD⟩ := largePrime_log_deficit
  refine ⟨1+B*D,by positivity,?_⟩
  have hcast := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [HB,hcast.eventually (eventually_const_log_pow_le_rpow 1 4 (by norm_num : (0:ℝ)<1/2)),
    eventually_ge_atTop (4:ℕ)] with N hb hl hN
  have hn : (4:ℝ)≤N := by exact_mod_cast hN
  have hL : 0<log N := log_pos (by linarith)
  let P := (Icc 2 N).filter Nat.Prime
  let S := P.filter fun p : ℕ => ¬sqrt N≤p
  let f (p:ℕ) := (goldbachRepCount (N-p):ℝ)*(log N-log p)
  have hdiff p (hp : p∈P) : 0≤log N-log p ∧ log N-log p≤log N := by
    obtain ⟨hi,hp⟩ := mem_filter.mp hp
    exact ⟨sub_nonneg.mpr (log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (mem_Icc.mp hi).2)),
      sub_le_self _ (log_nonneg (by exact_mod_cast hp.one_le))⟩
  have hsub : S⊆Icc 1 ⌊sqrt N⌋₊ := by
    intro p hp
    obtain ⟨hp,hp'⟩ := mem_filter.mp hp
    have hprime := (mem_filter.mp hp).2
    exact mem_Icc.mpr ⟨hprime.one_le,(Nat.le_floor_iff (sqrt_nonneg _)).mpr (le_of_not_ge hp')⟩
  have hcard : (S.card:ℝ)≤sqrt N := by
    apply le_trans _ (Nat.floor_le (sqrt_nonneg _))
    exact_mod_cast (card_le_card hsub).trans_eq (by simp [Nat.card_Icc])
  have hsmall : (∑p∈S,f p)≤sqrt N*(N*log N) := by
    calc
      _ ≤ ∑_p∈S,(N:ℝ)*log N := by
        apply sum_le_sum;intro p hp
        have h := (goldbachRepCount_le_self (N-p)).trans (Nat.sub_le ..)
        exact mul_le_mul (by exact_mod_cast h) (hdiff p (mem_filter.mp hp).1).2
          (hdiff p (mem_filter.mp hp).1).1 (by positivity)
      _ ≤ _ := by simp only [sum_const,nsmul_eq_mul];gcongr
  have hlarge : (∑p∈largePrimeSet N,f p)≤ B*((N:ℝ)/(log N)^2)*(D*N/log N) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (HD N hN) (by positivity : 0≤B*((N:ℝ)/(log N)^2)))
    rw [mul_sum]
    apply sum_le_sum;intro p hp
    dsimp only [f]
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hb (N-p) (Nat.sub_le ..)) (hdiff p (mem_filter.mp hp).1).1
  change (∑p∈P,f p)≤_
  rw [←sum_filter_add_sum_filter_not P (fun p : ℕ => sqrt N≤p)]
  change (∑p∈largePrimeSet N,f p)+(∑p∈S,f p)≤_
  have hsm : sqrt N*(N*log N)≤(N:ℝ)^2/(log N)^3 := by
    rw [one_mul,←sqrt_eq_rpow] at hl
    rw [le_div_iff₀ (pow_pos hL _)]
    have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg (sqrt_nonneg (N:ℝ)) (Nat.cast_nonneg (α:=ℝ) N))
    have he := congrArg (fun v : ℝ => N*v) (sq_sqrt (Nat.cast_nonneg (α:=ℝ) N))
    nlinarith only [hh,he]
  apply (add_le_add hlarge (hsmall.trans hsm)).trans_eq
  field_simp;ring

end AnalyticNumberTheory.AdditiveNumberTheory
