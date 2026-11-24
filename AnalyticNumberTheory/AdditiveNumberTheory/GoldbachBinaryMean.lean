import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachBinaryMajorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachBinaryMinorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachAsymptotic
import AnalyticNumberTheory.PrimeDistribution.SiegelWalfisz

/-!
# Binary Goldbach on average

The binary Hardy–Littlewood main term approximates the von Mangoldt
weighted count in absolute mean over an initial interval.
-/

noncomputable section
open Finset MeasureTheory Filter
open scoped Classical Topology ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- The cutoff may exceed the represented integer in the binary convolution. -/
theorem goldbachBinaryWeighted_eq_representationIntegral_of_le {N n : ℕ} (hn : n ≤ N) :
    (goldbachBinaryWeighted n : ℂ) = representationIntegral (fun α => primeExpSum N α^2*e (-α*n)) := by
  rw [representationIntegral]
  simp only [primeExpSum,Nat.floor_natCast,sq,
    integral_expSum_mul_expSum_mul_e_neg]
  unfold goldbachBinaryWeighted
  push_cast
  simp only [apply_ite Complex.ofReal,Complex.ofReal_mul,Complex.ofReal_zero]
  have hsub : Icc 1 n ⊆ Icc 1 N := Icc_subset_Icc_right (a := 1) hn
  rw [← sum_subset (f := fun i => ∑ j ∈ Icc 1 N, if i+j=n then (Λ i:ℂ)*(Λ j:ℂ) else 0) hsub]
  · refine sum_congr rfl fun i _ => ?_
    apply sum_subset hsub
    intro j hj hj'
    have hjn : n < j := by simp only [mem_Icc] at *; omega
    simp [show i+j ≠ n by omega]
  · intro i hi hi'
    apply sum_eq_zero
    intro j _
    have hin : n < i := by simp only [mem_Icc] at *; omega
    simp [show i+j ≠ n by omega]

/-- A quantitative mean bound at complementary rational-arc parameters.
Here D bounds the error of each linear major-arc approximation. -/
theorem sum_abs_goldbachBinary_sub_main_le {N M : ℕ} (hM : 1 ≤ M)
    (hNM : 2*(M:ℝ)^2 ≤ N) (hL : 1 ≤ Real.log N) {D C : ℝ} (hD : 0 ≤ D)
    (hC : ∑ n ∈ Ioc 0 N, binarySeriesMoment n ≤ C*N)
    (happrox : ∀ q ∈ Icc 1 M, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a ((N:ℝ)/M),
      ‖primeExpSum N α - (μ q:ℂ)/q.totient*mainExpSum N (α-a/q)‖ ≤ D) :
    ∑ n ∈ Ioc 0 N, |goldbachBinaryWeighted n - goldbachBinarySingularSeries n*(n-1:ℕ)| ≤
      14*N*(M:ℝ)^2*D + N^2*C/(M:ℝ)^(1/8:ℝ) +
        30000*(N:ℝ)^2*(2/Real.sqrt M+(N:ℝ)^(-(1/5):ℝ))*(Real.log N)^5 := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0:ℝ)<M := by linarith
  have hn2 : (2:ℝ) ≤ N := by nlinarith
  have hn : (0:ℝ)<N := by linarith
  let Q := (N:ℝ)/M
  have hMQ : 2*(M:ℝ) ≤ Q := (le_div_iff₀ hm0).mpr (by nlinarith)
  have hQ : 0 < Q := div_pos hn hm0
  let Z := fun n : ℕ => fun α : ℝ => primeExpSum N α^2*e (-α*n)
  let U := fun n : ℕ => minorArcIntegral (Z n) M Q
  let B : ℝ := 10000 * (N * (M:ℝ)^(-(1/2):ℝ) + (N:ℝ)^(4/5:ℝ) +
        (N:ℝ)^(1/2:ℝ)*Q^(1/2:ℝ))*(Real.log N)^4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : majorArcDenoms (M:ℝ) = Icc 1 M := by simp [majorArcDenoms]
  have hpt (n : ℕ) (hn' : n ∈ Ioc 0 N) :
      |goldbachBinaryWeighted n - goldbachBinarySingularSeries n*(n-1:ℕ)| ≤
      14*(M:ℝ)^2*D + (N/(M:ℝ)^(1/8:ℝ))*binarySeriesMoment n + ‖U n‖ := by
    obtain ⟨hn0,hnN⟩ := mem_Ioc.mp hn'
    have he : Function.Periodic (fun α : ℝ => e (-α*n)) 1 := by
      simpa only [Int.cast_neg,Int.cast_natCast,mul_neg,neg_mul] using e_periodic_mul_int (-(n:ℤ))
    have hper : Function.Periodic (Z n) 1 := by
      intro α
      dsimp only [Z]
      rw [periodic_primeExpSum N α]
      exact congrArg (_ * ·) (he α)
    have hc : Continuous (Z n) := ((continuous_primeExpSum N).pow 2).mul (continuous_e.comp (continuous_neg.mul continuous_const))
    have hdecomp := representationIntegral_eq_majorArcIntegral_add_minorArcIntegral_of_continuous hper hc hm hMQ
    have h1 := norm_goldbachBinary_majorArcIntegral_sub_le N n hm hMQ (fun _ => D) (by simpa only [hI] using happrox)
    rw [hI] at h1
    have hs : (∑ q ∈ Icc 1 M,(q.totient:ℝ)*(D*(7*N)*(2/(q*Q)))) ≤ 14*(M:ℝ)^2*D := by
      calc
        _ ≤ ∑ _q ∈ Icc 1 M, 14*M*D := by
          apply sum_le_sum
          intro q hq
          have hq0 : (0:ℝ)<q := by exact_mod_cast (mem_Icc.mp hq).1
          calc
            _ ≤ (q:ℝ)*(D*(7*N)*(2/(q*Q))) := by gcongr; exact_mod_cast Nat.totient_le q
            _ = _ := by dsimp [Q]; field_simp; ring
        _ = _ := by simp [nsmul_eq_mul]; ring
    have h2 := norm_binaryModelSum_sub_series_le hn0 hnN hM hNM
    rw [← Real.norm_eq_abs,← Complex.norm_real,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_natCast,
      goldbachBinaryWeighted_eq_representationIntegral_of_le hnN,hdecomp,add_sub_right_comm]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (h1.trans hs) h2)
  have h2 := sum_sq_goldbachBinary_minorArcIntegral_le (by exact_mod_cast hn2) hm hMQ (Ioc 0 N)
  change (∑ n ∈ Ioc 0 N, ‖U n‖^2) ≤ B^2*(Chebyshev.psi N*Real.log N) at h2
  have hpsi : Chebyshev.psi N ≤ 7*N := by
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    exact (psi_le_const_mul_self hn.le).trans (mul_le_mul_of_nonneg_right (by linarith) hn.le)
  have hcs := sum_mul_sq_le_sq_mul_sq (Ioc 0 N) (fun _ => (1:ℝ)) (fun n => ‖U n‖)
  simp only [one_mul,one_pow,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one] at hcs
  have hminor : (∑ n ∈ Ioc 0 N, ‖U n‖) ≤ 3*B*N*Real.log N := by
    have hh : (∑ n ∈ Ioc 0 N, ‖U n‖)^2 ≤ N*(B^2*(7*N*Real.log N)) := by
      exact hcs.trans (mul_le_mul_of_nonneg_left (h2.trans (by gcongr)) hn.le)
    have hr := mul_le_mul_of_nonneg_left (show 7*Real.log N ≤ 9*(Real.log N)^2 by nlinarith)
      (show 0 ≤ B^2*(N:ℝ)^2 by positivity)
    exact le_of_pow_le_pow_left₀ (by decide : 2≠0) (by positivity) (by nlinarith)
  have hBr : B = 10000*N*(2/Real.sqrt M+(N:ℝ)^(-(1/5):ℝ))*(Real.log N)^4 := by
    have hr : (N:ℝ)^(4/5:ℝ) = N*(N:ℝ)^(-(1/5):ℝ) := by
      conv_rhs => lhs; rw [← Real.rpow_one (N:ℝ)]
      rw [← Real.rpow_add hn]; norm_num
    dsimp only [B,Q]
    rw [Real.rpow_neg hm0.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,Real.sqrt_div hn.le,hr]
    field_simp; nlinarith [Real.sq_sqrt hn.le]
  calc
    _ ≤ _ := sum_le_sum hpt
    _ = N*(14*(M:ℝ)^2*D) + (N/(M:ℝ)^(1/8:ℝ))*(∑ n ∈ Ioc 0 N,binarySeriesMoment n) + ∑ n ∈ Ioc 0 N, ‖U n‖ := by
      simp [sum_add_distrib,mul_sum,nsmul_eq_mul]
    _ ≤ N*(14*(M:ℝ)^2*D) + (N/(M:ℝ)^(1/8:ℝ))*(C*N) + 3*B*N*Real.log N := by gcongr
    _ = _ := by rw [hBr]; ring

/-- Mean binary Goldbach asymptotic with a logarithmic saving of arbitrary
order. The constants are independent of the length of the averaging interval. -/
theorem goldbachBinaryWeighted_mean_isBigO (A : ℕ) :
    (fun N : ℕ => ∑ n ∈ Ioc 0 N, |goldbachBinaryWeighted n -
      goldbachBinarySingularSeries n*(n-1:ℕ)|) =O[atTop]
      (fun N : ℕ => (N:ℝ)^2 / (Real.log N)^A) := by
  obtain ⟨C,hC,hmean⟩ := sum_binarySeriesMoment_le
  let k := A+5
  let B := 8*(k+1)
  let K := 2*B+A
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have slow (c : ℝ) (j : ℕ) {b : ℝ} (hb : 0 < b) :
      ∀ᶠ N : ℕ in atTop, c*(Real.log N)^j ≤ (N:ℝ)^b := by
    have ho := (isLittleO_log_rpow_rpow_atTop (j:ℝ) hb).tendsto_div_nhds_zero
    have ht := ((tendsto_const_nhds (x := c)).mul ho).eventually (gt_mem_nhds (by simp : c*0<1))
    filter_upwards [hcast.eventually ht,eventually_ge_atTop (1:ℕ)] with N h hN
    change c*((Real.log N)^(j:ℝ)/(N:ℝ)^b)<1 at h
    rw [Real.rpow_natCast,← mul_div_assoc,div_lt_one (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)] at h
    exact h.le
  apply Asymptotics.IsBigO.of_bound (C+90014)
  filter_upwards [siegelWalfisz_primeExpSum_log_saving siegelWalfisz B K,
    slow 2 (2*B) (by norm_num : (0:ℝ)<1), slow 1 k (by norm_num : (0:ℝ)<1/5),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with N hsw hsize hslow hL hN
  let L := Real.log N
  let m := ⌈L^k⌉₊
  let M := m^8
  have hL2 : 2 ≤ L := hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hn : (0:ℝ) < N := by exact_mod_cast (by omega : 0<N)
  have hmlo : L^k ≤ (m:ℝ) := Nat.le_ceil _
  have hmhi : (m:ℝ) ≤ L^(k+1) := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ L^k by positivity)
    change (m:ℝ)<L^k+1 at ht
    have h1 := one_le_pow₀ hL1 (n := k)
    rw [pow_succ]
    linarith only [ht,h1,mul_le_mul_of_nonneg_left hL2 (zero_le_one.trans h1)]
  have hm1 : 1 ≤ m := by exact_mod_cast (one_le_pow₀ hL1 (n := k)).trans hmlo
  have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0:ℝ) < m := by linarith
  have hM : 1 ≤ M := Nat.one_le_pow 8 m hm1
  have hMhi : (M:ℝ) ≤ L^B := by
    dsimp only [M,B]
    rw [Nat.cast_pow,mul_comm 8,pow_mul]
    gcongr
  have hM2 : (M:ℝ)^2 ≤ L^(2*B) := by rw [mul_comm 2 B,pow_mul]; gcongr
  rw [Real.rpow_one] at hsize
  have hNM : 2*(M:ℝ)^2 ≤ N := (mul_le_mul_of_nonneg_left hM2 (by norm_num)).trans hsize
  have hroot : (M:ℝ)^(1/8:ℝ) = m := by
    dsimp only [M]
    rw [Nat.cast_pow,← Real.rpow_natCast (m:ℝ) 8,← Real.rpow_mul hm0.le]
    norm_num
  have hsqrt : (m:ℝ) ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    change (m:ℝ)^2 ≤ (m^8:ℕ)
    rw [Nat.cast_pow]
    exact pow_le_pow_right₀ hm1' (by decide)
  have h0 := sum_abs_goldbachBinary_sub_main_le hM hNM hL1
    (show 0 ≤ (N:ℝ)/L^K by positivity) (hmean N) (hsw M hM hMhi)
  change 1*L^k ≤ (N:ℝ)^(1/5:ℝ) at hslow
  rw [one_mul] at hslow
  have hmaj : 14*N*(M:ℝ)^2*((N:ℝ)/L^K) ≤ 14*N^2/L^A := by
    calc
      _ ≤ 14*N*L^(2*B)*((N:ℝ)/L^K) := by gcongr
      _ = _ := by dsimp only [K]; rw [pow_add]; field_simp
  have htr : (N:ℝ)^2*C/(M:ℝ)^(1/8:ℝ) ≤ (N:ℝ)^2*C/L^A := by
    rw [hroot]
    gcongr
    exact (pow_le_pow_right₀ hL1 (by dsimp [k]; omega : A ≤ k)).trans hmlo
  have hmi : (2/Real.sqrt M + (N:ℝ)^(-(1/5):ℝ))*L^5 ≤ 3/L^A := by
    rw [Real.rpow_neg hn.le, ← one_div]
    calc
      _ ≤ (2/L^k + 1/L^k)*L^5 := by gcongr <;> exact hmlo.trans hsqrt
      _ = _ := by dsimp only [k]; rw [pow_add]; field_simp; ring
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  refine h0.trans ?_
  change 14*N*(M:ℝ)^2*((N:ℝ)/L^K) + _ + (30000*(N:ℝ)^2)*_*L^5 ≤ _
  rw [mul_assoc (30000*(N:ℝ)^2)]
  exact (add_le_add (add_le_add hmaj htr) (mul_le_mul_of_nonneg_left hmi (by positivity))).trans_eq (by ring)

end AnalyticNumberTheory.AdditiveNumberTheory
