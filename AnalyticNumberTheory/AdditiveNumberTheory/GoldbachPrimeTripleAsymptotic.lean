import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachLogDeficit
import AnalyticNumberTheory.AdditiveNumberTheory.VinogradovThreePrimes

/-!
# The unweighted ternary Goldbach asymptotic

The von Mangoldt asymptotic and the binary sieve give the full leading
term for the actual number of ordered triples, with a fourth logarithm in
the error. Allowing the prime two does not affect that estimate.
-/

open Finset Real Filter Asymptotics
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem primeTripleAsymptotic (T : ℕ→ℕ)
    (ho : ∀N,goldbachTernaryOddCount N≤T N) (ha : ∀N,T N≤goldbachTernaryCount N) :
    (fun N : ℕ => (T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^4) := by
  obtain ⟨C,hC,H⟩ := goldbach_binary_log_deficit
  obtain ⟨B,hB,HB⟩ := (goldbachTernaryWeighted_asymptotic 1).exists_pos
  apply IsBigO.of_bound (3*C+327+B)
  have hcast := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [H,HB,hcast.eventually (eventually_const_log_pow_le_rpow 1 2 (by norm_num : (0:ℝ)<1/2)),
    hcast.eventually (eventually_const_log_pow_le_rpow 1 3 (by norm_num : (0:ℝ)<1)),eventually_ge_atTop (2:ℕ)] with
    N h hb hsqrt hcube hN
  let L := log (N:ℝ)
  have hnn : (2:ℝ)≤N := by exact_mod_cast hN
  have hn : 0<(N:ℝ) := by linarith
  have hL : 0<L := log_pos (by linarith)
  let M := goldbachTernarySingularSeries N * (N:ℝ)^2/2
  change ‖goldbachTernaryWeighted N-M‖≤B*‖(N:ℝ)^2/L^1‖ at hb
  rw [pow_one,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity)] at hb
  have hu := goldbachTernaryCount_log_weight_loss hN
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0≤3*(log N)^2)
  have hmain₁ : L^3*(T N:ℝ)-goldbachTernaryWeighted N≤3*C*((N:ℝ)^2/L) := by
    have hA : L^3*(T N:ℝ)≤L^3*(goldbachTernaryCount N:ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast ha N) (by positivity)
    have he : 3*(log N)^2*(C*((N:ℝ)^2/(log N)^3))=3*C*((N:ℝ)^2/L) := by
      change 3*L^2*(C*((N:ℝ)^2/L^3))=_;field_simp <;> ring
    rw [he] at hh
    change L^3*(_ : ℝ)-_≤_ at hu
    linarith only [hA,hu,hh,goldbachTernaryThetaWeighted_le_weighted N]
  have hpow := goldbachTernaryWeighted_sub_thetaWeighted_le hN
  have htwo := goldbachTernaryThetaWeighted_sub_odd_le hN
  have ho' : L^3*(goldbachTernaryOddCount N:ℝ)≤L^3*(T N:ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast ho N) (by positivity)
  have hr : (N:ℝ)^(3/2:ℝ) = N*sqrt N := by
    conv_rhs => lhs;rw [←Real.rpow_one (N:ℝ)]
    rw [sqrt_eq_rpow,←Real.rpow_add hn];norm_num
  have h₁ : (N:ℝ)^(3/2:ℝ)*L≤(N:ℝ)^2/L := by
    rw [hr,le_div_iff₀ hL]
    rw [one_mul,←sqrt_eq_rpow] at hsqrt
    change L^2≤sqrt N at hsqrt
    have hh := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hn.le (sqrt_nonneg (N:ℝ)))
    have he := congrArg (fun v : ℝ => N*v) (sq_sqrt hn.le)
    nlinarith only [he,hh]
  have h₂ : (N:ℝ)*L^2≤(N:ℝ)^2/L := by
    rw [one_mul,rpow_one] at hcube
    rw [le_div_iff₀ hL]
    change L^3≤N at hcube
    nlinarith only [mul_le_mul_of_nonneg_left hcube hn.le]
  change goldbachTernaryWeighted N-goldbachTernaryThetaWeighted N≤324*(N:ℝ)^(3/2:ℝ)*L at hpow
  change goldbachTernaryThetaWeighted N-L^3*(goldbachTernaryOddCount N:ℝ)≤3*N*L^2 at htwo
  have hmain₂ : goldbachTernaryWeighted N-L^3*(T N:ℝ)≤327*((N:ℝ)^2/L) := by
    linarith only [hpow,htwo,ho',h₁,h₂]
  have hscale : 0≤(N:ℝ)^2/L := by positivity
  have H' : |L^3*(T N:ℝ)-M|≤(3*C+327+B)*((N:ℝ)^2/L) := by
    rw [abs_le]
    have hA := (abs_le.mp hb).1
    have hB' := (abs_le.mp hb).2
    constructor <;>
      nlinarith only [hmain₁,hmain₂,hA,hB',mul_nonneg hC.le hscale,hscale]
  change ‖(T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*L^3)‖≤(3*C+327+B)*‖(N:ℝ)^2/L^4‖
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (by positivity)]
  have he : (T N:ℝ)-goldbachTernarySingularSeries N*(N:ℝ)^2/(2*L^3)=(L^3*(T N:ℝ)-M)/L^3 := by
    dsimp only [M];field_simp <;> ring
  rw [he,abs_div,abs_of_pos (pow_pos hL 3)]
  apply (div_le_div_of_nonneg_right H' (by positivity : 0≤L^3)).trans_eq
  field_simp <;> ring

/-- The number of ordered representations by three odd primes differs from
the singular-series main term by O(N²/log⁴ N). Repeated primes are allowed. -/
theorem goldbachTernaryOddCount_asymptotic :
    (fun N : ℕ => (goldbachTernaryOddCount N:ℝ)-
      goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^4) :=
  primeTripleAsymptotic _ (fun _ => le_rfl) goldbachTernaryOddCount_le_count

/-- The same ternary Goldbach asymptotic with all primes allowed. -/
theorem goldbachTernaryCount_asymptotic :
    (fun N : ℕ => (goldbachTernaryCount N:ℝ)-
      goldbachTernarySingularSeries N*(N:ℝ)^2/(2*(log N)^3)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2/(log N)^4) :=
  primeTripleAsymptotic _ goldbachTernaryOddCount_le_count (fun _ => le_rfl)

end AnalyticNumberTheory.AdditiveNumberTheory
