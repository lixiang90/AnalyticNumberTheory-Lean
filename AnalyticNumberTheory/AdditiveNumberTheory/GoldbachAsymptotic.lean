import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcReduction
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast

/-!
# The conditional ternary Goldbach asymptotic

Choosing complementary major-arc parameters reduces the normalized error to
the prime-sum approximation and a power of the major-arc denominator. The
Siegel–Walfisz hypothesis supplies arbitrary logarithmic savings on these arcs.
Under this hypothesis the classical ternary asymptotic follows with a
logarithmic saving of any prescribed natural order. A uniform lower bound on
the singular series for odd inputs then gives a representation by three odd primes.
-/

noncomputable section
open Finset MeasureTheory Filter
open scoped Classical Topology ArithmeticFunction.Moebius
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Normalize the circle-method error while retaining an additional major-arc contribution. -/
theorem abs_goldbachTernary_normalized_le_of_major {N M : ℕ} (hM : 1 ≤ M)
    (hNM : 2 * (M : ℝ) ^ 2 ≤ N) {D E : ℝ} (hD : 0 ≤ D)
    (hmajorIntegral : ‖majorArcIntegral (fun α => primeExpSum N α^3*e (-α*N)) M ((N:ℝ)/M) -
      (goldbachTernarySingularSeries N:ℂ)*((N-1).choose 2:ℕ)‖ ≤
      ((∑ q∈Icc 1 M, (q.totient:ℝ)*(D*(43*N^2)*(2/(q*((N:ℝ)/M))))) +
        (2*((N:ℝ)/M)^2*M*Real.sqrt M+32*(M:ℝ)^(-1/2:ℝ)*((N-1).choose 2:ℕ))) + E) :
    |goldbachTernaryWeighted N - goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ)| / (N : ℝ) ^ 2 ≤
      86 * M ^ 2 * (D / N) + 34 / Real.sqrt M +
        70000 * (2 / Real.sqrt M + (N : ℝ) ^ (-(1 / 5 : ℝ))) * (Real.log N) ^ 5 + E/(N:ℝ)^2 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < M := by linarith
  have hn2 : (2 : ℝ) ≤ N := by nlinarith
  have hn : (0 : ℝ) < N := by linarith
  have hMQ : 2 * (M : ℝ) ≤ N / M := (le_div_iff₀ hm0).mpr (by nlinarith)
  have h := abs_goldbachTernary_sub_le_of_major (by exact_mod_cast hn2) hM hMQ hmajorIntegral
  have hmajor : (∑ q ∈ Icc 1 M, (q.totient : ℝ) * (D * (43 * N ^ 2) * (2 / (q * ((N : ℝ) / M))))) ≤
      86 * (N : ℝ) * M ^ 2 * D := by
    calc
      _ ≤ ∑ _q ∈ Icc 1 M, (86 * (N : ℝ) * M * D) := by
        refine sum_le_sum fun q hq => ?_
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
        have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
        calc
          _ ≤ (q : ℝ) * (D * (43 * N ^ 2) * (2 / (q * ((N : ℝ) / M)))) := by gcongr
          _ = _ := by field_simp [hn.ne', hm0.ne', hq0.ne']; ring
      _ = _ := by simp [nsmul_eq_mul]; ring
  have hcount : (((N - 1).choose 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast (Nat.choose_le_pow (N - 1) 2).trans (Nat.pow_le_pow_left (Nat.sub_le N 1) 2)
  have hMs : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hm0
  have hNs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hiM : (M : ℝ) ^ (-1 / 2 : ℝ) = 1 / Real.sqrt M := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hm0.le, ← Real.sqrt_eq_rpow, one_div]
  have htrunc : 2 * ((N : ℝ) / M) ^ 2 * M * Real.sqrt M +
        32 * (M : ℝ) ^ (-1 / 2 : ℝ) * ((N - 1).choose 2 : ℕ) ≤ 34 * (N : ℝ) ^ 2 / Real.sqrt M := by
    rw [hiM]
    calc
      _ ≤ 2 * ((N : ℝ) / M) ^ 2 * M * Real.sqrt M + 32 * (1 / Real.sqrt M) * N ^ 2 := by gcongr
      _ = _ := by field_simp [hMs.ne', hm0.ne']; nlinarith [Real.sq_sqrt hm0.le]
  have hr : (N : ℝ) ^ (4 / 5 : ℝ) = N * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
    conv_rhs => lhs; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hn]; norm_num
  have hps : Chebyshev.psi (N : ℝ) ≤ 7 * N := by
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    exact (psi_le_const_mul_self hn.le).trans (mul_le_mul_of_nonneg_right (by linarith) hn.le)
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hminor : 10000 * (N * (M : ℝ) ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (4 / 5 : ℝ) +
      (N : ℝ) ^ (1 / 2 : ℝ) * ((N : ℝ) / M) ^ (1 / 2 : ℝ)) * (Real.log N) ^ 4 *
      (Chebyshev.psi N * Real.log N) ≤
        70000 * (N : ℝ) ^ 2 * (2 / Real.sqrt M + (N : ℝ) ^ (-(1 / 5 : ℝ))) * (Real.log N) ^ 5 := by
    rw [show - (1 / 2 : ℝ) = -1 / 2 by ring, hiM, hr, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_div hn.le]
    calc
      _ ≤ 10000 * (N * (1 / Real.sqrt M) + N * (N : ℝ) ^ (-(1 / 5 : ℝ)) +
          Real.sqrt N * (Real.sqrt N / Real.sqrt M)) * (Real.log N) ^ 4 * (7 * N * Real.log N) := by gcongr
      _ = _ := by field_simp [hMs.ne']; ring_nf; rw [Real.sq_sqrt hn.le]; ring
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  apply h.trans
  calc
    _ ≤ _ := add_le_add (add_le_add (add_le_add hmajor htrunc) (le_refl E)) hminor
    _ = _ := by field_simp [hn.ne', hMs.ne'] <;> ring

/-- With complementary parameters `M Q = N`, a common approximation error `D` on the major arcs
gives an explicit bound, normalized by the natural scale `N²`. -/
theorem abs_goldbachTernary_normalized_le {N M : ℕ} (hM : 1 ≤ M)
    (hNM : 2 * (M : ℝ) ^ 2 ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (happrox : ∀ q ∈ Icc 1 M, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a ((N : ℝ) / M),
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ ≤ D) :
    |goldbachTernaryWeighted N - goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ)| / (N : ℝ) ^ 2 ≤
      86 * M ^ 2 * (D / N) + 34 / Real.sqrt M +
        70000 * (2 / Real.sqrt M + (N : ℝ) ^ (-(1 / 5 : ℝ))) * (Real.log N) ^ 5 := by
  have hpos : 0<(M:ℝ) := by exact_mod_cast hM
  have hMQ : 2*(M:ℝ)≤N/M := (le_div_iff₀ hpos).mpr (by nlinarith only [hNM])
  have H := norm_goldbachTernary_majorArcIntegral_sub_series_le hM hMQ (fun _ => D) happrox
  simpa using abs_goldbachTernary_normalized_le_of_major hM hNM hD (E:=0) (by simpa using H)

/-- Any fixed power of the logarithm, even after scaling, is eventually bounded by a positive power. -/
theorem eventually_const_log_pow_le_rpow (C : ℝ) (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, C * (Real.log x) ^ k ≤ x ^ b := by
  have ho := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hb).tendsto_div_nhds_zero
  have ht := ((tendsto_const_nhds (x := C)).mul ho).eventually (gt_mem_nhds (by simp : C * 0 < 1))
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  simp only [Real.rpow_natCast] at hx
  change C * (Real.log x ^ k / x ^ b) < 1 at hx
  rw [← mul_div_assoc, div_lt_one (Real.rpow_pos_of_pos hx0 _)] at hx
  exact hx.le

private theorem eventually_log_pow_exp_sqrt_log (C : ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C * (Real.log x) ^ k * Real.exp (-c * Real.sqrt (Real.log (Real.sqrt x))) ≤ 1 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 * k : ℕ) : ℝ) c hc
  have ht' := ((tendsto_const_nhds (x := C * 2 ^ k)).mul ht).eventually
    (gt_mem_nhds (by simp : C * 2 ^ k * 0 < 1))
  have htarg : Tendsto (fun x : ℝ => Real.sqrt (Real.log (Real.sqrt x))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_sqrt_atTop)
  filter_upwards [htarg.eventually ht', eventually_ge_atTop (1 : ℝ)] with x hx hx1
  let u := Real.sqrt (Real.log (Real.sqrt x))
  change C * 2 ^ k * (u ^ ((2 * k : ℕ) : ℝ) * Real.exp (-c * u)) < 1 at hx
  rw [Real.rpow_natCast, pow_mul] at hx
  have hu : u ^ 2 = Real.log x / 2 := by
    dsimp only [u]
    rw [Real.sq_sqrt (Real.log_nonneg ((Real.one_le_sqrt).mpr hx1)),
      Real.log_sqrt (by linarith)]
  rw [hu] at hx
  change C * (Real.log x) ^ k * Real.exp (-c * u) ≤ 1
  convert hx.le using 1
  rw [div_pow]
  field_simp

/-- Siegel–Walfisz yields arbitrary logarithmic savings for the prime exponential sum
on major arcs with polylogarithmic denominators and complementary widths. -/
theorem siegelWalfisz_primeExpSum_log_saving (hSW : SiegelWalfiszBound) (B K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ (Real.log N) ^ B →
      ∀ q ∈ Icc 1 M, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a ((N : ℝ) / M),
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ ≤
        N / (Real.log N) ^ K := by
  obtain ⟨C, hC, c, hc, hsw⟩ := siegelWalfisz_primeExpSum_majorArc hSW (A := (2 * B : ℕ)) (by positivity)
  let d := K + 2 * B
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hcast.eventually (eventually_const_log_pow_le_rpow 126 d (by norm_num : (0 : ℝ) < 1 / 2)),
    hcast.eventually (eventually_const_log_pow_le_rpow 36 (d + 1) (by norm_num : (0 : ℝ) < 1)),
    hcast.eventually (eventually_log_pow_exp_sqrt_log (18 * C) d hc),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 4,
    eventually_ge_atTop (4 : ℕ)] with N hsmall hlin hexp hL hN
  intro M hM hmL q hq a ha α hα
  let L := Real.log N
  have hL4 : 4 ≤ L := hL
  have hL0 : 0 < L := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : 2 ≤ Real.sqrt (N : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hsqr := Real.sq_sqrt hn.le
  have hYN : Real.sqrt (N : ℝ) ≤ N := by nlinarith
  obtain ⟨hq1, hqM⟩ := mem_Icc.mp hq
  have hm0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqM' : (q : ℝ) ≤ M := by exact_mod_cast hqM
  have hqY : (q : ℝ) ≤ (Real.log (Real.sqrt N)) ^ ((2 * B : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_mul, Real.log_sqrt hn.le]
    exact (hqM'.trans hmL).trans (pow_le_pow_left₀ hL0.le (by nlinarith) B)
  have hb := hsw hY hYN hq1 hqY (a := (a : ℤ)) ((mem_filter.mp ha).2) hα
  simp only [Int.cast_natCast] at hb
  let E := max (7 * Real.sqrt N) (C * N * Real.exp (-c * Real.sqrt (Real.log (Real.sqrt N))))
  have hE : 0 ≤ E := le_max_of_le_left (by positivity)
  have hEs : 18 * L ^ d * E ≤ N := by
    change 18 * L ^ d * max _ _ ≤ N
    rw [mul_max_of_nonneg _ _ (by positivity)]
    apply max_le
    · change 126 * L ^ d ≤ (N : ℝ) ^ (1 / 2 : ℝ) at hsmall
      rw [← Real.sqrt_eq_rpow] at hsmall
      calc
        _ = 126 * L ^ d * Real.sqrt N := by ring
        _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt hn.le
    · change 18 * C * L ^ d * _ ≤ 1 at hexp
      calc
        _ = (18 * C * L ^ d * Real.exp (-c * Real.sqrt (Real.log (Real.sqrt N)))) * N := by ring
        _ ≤ 1 * N := mul_le_mul_of_nonneg_right hexp hn.le
        _ = _ := by simp
  have hratio : Real.log q / Real.log 2 ≤ 2 * M := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
    have hlq := Real.log_le_sub_one_of_pos hqpos
    have ht : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [mul_le_mul_of_nonneg_left ht hm0.le]
  have hfac : 1 + 2 * Real.pi * N / (q * ((N : ℝ) / M)) ≤ 9 * M := by
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    rw [show 2 * Real.pi * N / (q * ((N : ℝ) / M)) = 2 * Real.pi * M / q by field_simp]
    have hh := div_le_self (by positivity : (0 : ℝ) ≤ 2 * Real.pi * M) hq1'
    have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four hm0.le]
  apply hb.trans
  change (_ * E + _ * L) * _ ≤ N / L ^ K
  apply (le_div_iff₀ (pow_pos hL0 K)).mpr
  have hmφ : (q.totient : ℝ) ≤ M := by exact_mod_cast (Nat.totient_le q).trans hqM
  calc
    _ ≤ (M * E + (2 * M) * L) * (9 * M) * L ^ K := by gcongr
    _ = 9 * ((M : ℝ) ^ 2 * L ^ K) * (E + 2 * L) := by ring
    _ ≤ 9 * L ^ d * (E + 2 * L) := by
      have hpow : (M : ℝ) ^ 2 * L ^ K ≤ L ^ d := by
        change _ ≤ L ^ (K + 2 * B)
        rw [pow_add, mul_comm 2 B, pow_mul, mul_comm (L ^ K)]
        gcongr
      gcongr
    _ ≤ _ := by
      change 36 * L ^ (d + 1) ≤ (N : ℝ) ^ (1 : ℝ) at hlin
      rw [Real.rpow_one, pow_succ] at hlin
      nlinarith

/-- Under Siegel–Walfisz the ternary weighted representation count has an error
`O(N²/(log N)^A)` for every natural exponent `A`. The exact composition count in
the main term makes the statement valid for both parities. -/
theorem goldbachTernaryWeighted_sub_series_isBigO (hSW : SiegelWalfiszBound) (A : ℕ) :
    (fun N : ℕ => goldbachTernaryWeighted N -
      goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ))=O[atTop]
      (fun N : ℕ => (N : ℝ) ^ 2 / (Real.log N) ^ A) := by
  let k := A + 5
  let B := 2 * (k + 1)
  let K := 2 * B + A
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  apply Asymptotics.IsBigO.of_bound 210120
  filter_upwards [siegelWalfisz_primeExpSum_log_saving hSW B K,
    hcast.eventually (eventually_const_log_pow_le_rpow 2 (2 * B) (by norm_num : (0 : ℝ) < 1)),
    hcast.eventually (eventually_const_log_pow_le_rpow 1 k (by norm_num : (0 : ℝ) < 1 / 5)),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 2,
    eventually_ge_atTop (2 : ℕ)] with N hsw hsize hnslow hL hN
  let L := Real.log N
  let m := ⌈L ^ k⌉₊
  let M := m ^ 2
  have hL2 : 2 ≤ L := hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmlo : L ^ k ≤ (m : ℝ) := Nat.le_ceil _
  have hmhi : (m : ℝ) ≤ L ^ (k + 1) := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ L ^ k by positivity)
    change (m : ℝ) < L ^ k + 1 at ht
    have hk1 := one_le_pow₀ hL1 (n := k)
    rw [pow_succ]
    nlinarith
  have hm1 : 1 ≤ m := by exact_mod_cast ((one_le_pow₀ hL1 (n := k)).trans hmlo)
  have hM : 1 ≤ M := Nat.one_le_pow 2 m hm1
  have hMhi : (M : ℝ) ≤ L ^ B := by
    dsimp only [M, B]
    rw [Nat.cast_pow, mul_comm 2, pow_mul]
    gcongr
  have hM2 : (M : ℝ) ^ 2 ≤ L ^ (2 * B) := by rw [mul_comm 2 B, pow_mul]; gcongr
  change 2 * L ^ (2 * B) ≤ (N : ℝ) ^ (1 : ℝ) at hsize
  rw [Real.rpow_one] at hsize
  have hNM : 2 * (M : ℝ) ^ 2 ≤ N := by linarith
  have hz := abs_goldbachTernary_normalized_le hM hNM
    (show 0 ≤ (N : ℝ) / L ^ K by positivity) (hsw M hM hMhi)
  have hMsqrt : Real.sqrt M = (m : ℝ) := by simp [M, Real.sqrt_sq (Nat.cast_nonneg m)]
  change 1 * L ^ k ≤ (N : ℝ) ^ (1 / 5 : ℝ) at hnslow
  rw [one_mul] at hnslow
  have hmajor : 86 * (M : ℝ) ^ 2 * ((N / L ^ K) / N) ≤ 86 / L ^ A := by
    calc
      _ ≤ 86 * L ^ (2 * B) * ((N / L ^ K) / N) := by gcongr
      _ = _ := by dsimp only [K]; rw [pow_add]; field_simp
  have htrunc : 34 / Real.sqrt M ≤ 34 / L ^ A := by
    rw [hMsqrt]
    gcongr
    exact (pow_le_pow_right₀ hL1 (by dsimp [k]; omega : A ≤ k)).trans hmlo
  have hminor : (2 / Real.sqrt M + (N : ℝ) ^ (-(1 / 5 : ℝ))) * L ^ 5 ≤ 3 / L ^ A := by
    rw [hMsqrt, Real.rpow_neg hn.le, ← one_div]
    have hs : 2 / (m : ℝ) + 1 / (N : ℝ) ^ (1 / 5 : ℝ) ≤ 2 / L ^ k + 1 / L ^ k := by gcongr
    calc
      _ ≤ (2 / L ^ k + 1 / L ^ k) * L ^ 5 := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by dsimp only [k]; rw [pow_add]; field_simp; ring
  change _ ≤ 86 * (M : ℝ) ^ 2 * ((N / L ^ K) / N) + 34 / Real.sqrt M +
    70000 * (2 / Real.sqrt M + (N : ℝ) ^ (-(1 / 5 : ℝ))) * L ^ 5 at hz
  have herr : |goldbachTernaryWeighted N - goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ)|
      / (N : ℝ) ^ 2 ≤ 210120 / L ^ A := by
    apply hz.trans
    rw [mul_assoc (70000 : ℝ)]
    exact (add_le_add (add_le_add hmajor htrunc)
      (mul_le_mul_of_nonneg_left hminor (by norm_num : (0 : ℝ) ≤ 70000))).trans_eq (by ring)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (show 0 ≤ (N : ℝ) ^ 2 / L ^ A by positivity)]
  calc
    _ ≤ 210120 / L ^ A * (N : ℝ) ^ 2 := (div_le_iff₀ (sq_pos_of_pos hn)).mp herr
    _ = _ := by ring

/-- The ternary singular series is bounded uniformly, including at even targets. -/
theorem abs_goldbachTernarySingularSeries_le (N : ℕ) : |goldbachTernarySingularSeries N| ≤ 33 := by
  have h := abs_singularSeries_sub_sum_le (M := 1) le_rfl N
  simp only [Icc_self, sum_singleton, singularTermTernary_one, Nat.cast_one, Real.one_rpow, mul_one] at h
  exact abs_le.mpr ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- Replacing the exact number of compositions by its quadratic leading term
costs at most a linear error, uniformly in the singular series. -/
theorem goldbachTernary_composition_error {N : ℕ} (hN : 2≤N) :
    |goldbachTernarySingularSeries N * ((N-1).choose 2:ℕ) -
      goldbachTernarySingularSeries N * (N:ℝ)^2/2| ≤ 66*(N:ℝ) := by
  have hNR : (2:ℝ)≤N := by exact_mod_cast hN
  have hcount : |(((N - 1).choose 2 : ℕ) : ℝ) - (N : ℝ) ^ 2 / 2| ≤ 2 * (N : ℝ) := by
    rw [Nat.cast_choose_two, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  rw [mul_div_assoc,←mul_sub,abs_mul]
  exact (mul_le_mul (abs_goldbachTernarySingularSeries_le N) hcount (abs_nonneg _) (by norm_num)).trans_eq (by ring)

/-- Classical three-prime asymptotic formula for the von Mangoldt weighted count under
Siegel–Walfisz, with an arbitrary logarithmic saving. -/
theorem ternaryGoldbach_asymptotic (hSW : SiegelWalfiszBound) (A : ℕ) :
    (fun N : ℕ => goldbachTernaryWeighted N -
      goldbachTernarySingularSeries N * (N : ℝ) ^ 2 / 2)=O[atTop]
      (fun N : ℕ => (N : ℝ) ^ 2 / (Real.log N) ^ A) := by
  have hc := goldbachTernaryWeighted_sub_series_isBigO hSW A
  obtain ⟨C, hC⟩ := hc.bound
  apply Asymptotics.IsBigO.of_bound (C + 66)
  have hlog := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_const_log_pow_le_rpow 1 A (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hC, hlog, eventually_ge_atTop (2 : ℕ)] with N h hslow hN
  let L := Real.log N
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < L := Real.log_pos (by linarith)
  change 1 * L ^ A ≤ (N : ℝ) ^ (1 : ℝ) at hslow
  rw [one_mul, Real.rpow_one] at hslow
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (show 0 ≤ (N : ℝ) ^ 2 / L ^ A by positivity)] at h ⊢
  have hdiff : |goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ) -
      goldbachTernarySingularSeries N * (N : ℝ) ^ 2 / 2| ≤ 66 * ((N : ℝ) ^ 2 / L ^ A) := by
    apply (goldbachTernary_composition_error hN).trans
    have hNp : (N : ℝ) ≤ (N : ℝ) ^ 2 / L ^ A :=
      (le_div_iff₀ (pow_pos hL A)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hslow hnpos.le])
    linarith
  apply (abs_sub_le _ (goldbachTernarySingularSeries N * ((N - 1).choose 2 : ℕ)) _).trans
  exact (add_le_add h hdiff).trans_eq (by ring)

/-- Vinogradov's three-prime conclusion under the explicit Siegel–Walfisz hypothesis:
every sufficiently large odd natural number is a sum of three odd primes. -/
theorem eventually_odd_sum_three_odd_primes_of_siegelWalfisz (hSW : SiegelWalfiszBound) :
    ∀ᶠ N : ℕ in atTop, Odd N → ∃ p q r : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      r.Prime ∧ Odd r ∧ p + q + r = N := by
  obtain ⟨C, hC⟩ := (ternaryGoldbach_asymptotic hSW 1).bound
  obtain ⟨c, hc, hseries⟩ := goldbachTernarySingularSeries_pos_of_odd
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hC, (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop (8 * C / c),
    hcast.eventually (eventually_const_log_pow_le_rpow (8 * 324 / c) 1 (by norm_num : (0 : ℝ) < 1 / 2)),
    hcast.eventually (eventually_const_log_pow_le_rpow (24 / c) 2 (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (2 : ℕ)] with N herr hl hpowers htwo hN hodd
  let L := Real.log N
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < L := Real.log_pos (by linarith)
  have hL' : 8 * C ≤ c * L := by
    change 8 * C / c ≤ L at hl
    linarith [(div_le_iff₀ hc).mp hl]
  have hr : (N : ℝ) ^ (3 / 2 : ℝ) = N * Real.sqrt N := by
    conv_rhs => lhs; rw [← Real.rpow_one (N : ℝ)]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]; norm_num
  have hcorr1 : 324 * (N : ℝ) ^ (3 / 2 : ℝ) * L ≤ c / 8 * N ^ 2 := by
    change (8 * 324 / c) * L ^ 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) at hpowers
    rw [pow_one, ← Real.sqrt_eq_rpow] at hpowers
    have hs : 8 * 324 * L ≤ c * Real.sqrt N := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hpowers
      linarith
    rw [hr]
    have hh := mul_le_mul_of_nonneg_right hs
      (mul_nonneg hn.le (Real.sqrt_nonneg (N : ℝ)))
    have hsqr := Real.sq_sqrt hn.le
    nlinarith [congrArg (fun x : ℝ => c * N * x) hsqr]
  have hcorr2 : 3 * N * L ^ 2 ≤ c / 8 * N ^ 2 := by
    change (24 / c) * L ^ 2 ≤ (N : ℝ) ^ (1 : ℝ) at htwo
    rw [Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hc] at htwo
    nlinarith [mul_le_mul_of_nonneg_right htwo hn.le]
  have hR : goldbachTernarySingularSeries N * (N : ℝ) ^ 2 / 2 - goldbachTernaryWeighted N ≤
      c / 8 * N ^ 2 := by
    simp only [Real.norm_eq_abs, pow_one] at herr
    rw [abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) ^ 2 / L)] at herr
    apply (le_abs_self _).trans
    rw [abs_sub_comm]
    apply herr.trans
    rw [mul_div_assoc', div_le_iff₀ hL]
    nlinarith [mul_le_mul_of_nonneg_right hL' (sq_nonneg (N : ℝ))]
  have hcount : 0 < goldbachTernaryOddCount N := by
    by_contra! hnone
    have heq := Nat.eq_zero_of_le_zero hnone
    have hmain := mul_le_mul_of_nonneg_right (hseries N hodd) (sq_nonneg (N : ℝ))
    have h1 := (goldbachTernaryWeighted_sub_thetaWeighted_le hN).trans hcorr1
    have h2' := (goldbachTernaryThetaWeighted_sub_odd_le hN).trans hcorr2
    rw [heq, Nat.cast_zero, mul_zero, sub_zero] at h2'
    nlinarith [mul_pos hc (sq_pos_of_pos hn)]
  obtain ⟨⟨p, q, r⟩, htriple⟩ := Finset.card_pos.mp hcount
  obtain ⟨hmem, hp, hq, hr', hsum⟩ := mem_filter.mp htriple
  simp only [mem_product, mem_Icc] at hmem
  exact ⟨p, q, r, hp, hp.odd_iff.mpr hmem.1.1,
    hq, hq.odd_iff.mpr hmem.2.1.1, hr', hr'.odd_iff.mpr hmem.2.2.1, hsum⟩

end AnalyticNumberTheory.AdditiveNumberTheory
