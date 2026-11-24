import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachSingularIntegral
import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachBinarySeries

/-!
# Major arcs of the binary Goldbach problem

The cutoff in the exponential sums is fixed while the represented integer
varies. Completing the model integral extracts the number of compositions
into two positive parts and costs at most the reciprocal of the arc width.
-/

noncomputable section
open Finset MeasureTheory
open scoped Classical ArithmeticFunction.Moebius
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Two-variable Goldbach singular integral with cutoff N, target n, and
half-width H. -/
def binarySingularIntegral (N n : ℕ) (H : ℝ) : ℂ :=
  ∫ β in (-H)..H, mainExpSum N β ^ 2 * e (-β * n)

/-- Completing the period counts the ordered positive decompositions of n. -/
theorem binarySingularIntegral_half {N n : ℕ} (hn : n ≤ N) :
    binarySingularIntegral N n (1/2) = ((n-1:ℕ):ℂ) := by
  have hmain (x : ℝ) : mainExpSum N x = expSum (fun _ => 1) (Icc 1 N) x := by
    simp [mainExpSum,expSum]
  have h := integral_expSum_mul_expSum_mul_e_neg_shift
    (fun _ => 1) (fun _ => 1) (Icc 1 N) (Icc 1 N) n (-(1/2))
  simp only [← hmain,← sq,one_pow,show (-(1/2):ℝ)+1=1/2 by norm_num] at h
  rw [binarySingularIntegral,h]
  have row (i : ℕ) : (∑ j ∈ Icc 1 N, if i+j=n then (1:ℂ) else 0) =
      if i<n then 1 else 0 := by
    by_cases hi : i<n
    · simp only [hi,↓reduceIte]
      simp_rw [show ∀ j : ℕ, i+j=n ↔ j=n-i from fun j => by omega]
      rw [sum_ite_eq']
      simp [mem_Icc,show 1 ≤ n-i by omega,show n-i ≤ N by omega]
    · simp only [hi,↓reduceIte]
      apply sum_eq_zero
      intro j hj
      have := (mem_Icc.mp hj).1
      simp [show i+j≠n by omega]
  simp_rw [row]
  rw [← sum_filter]
  have hh : ((Icc 1 N).filter fun i => i<n) = Icc 1 (n-1) := by
    ext i
    simp only [mem_filter,mem_Icc]
    omega
  simp [hh]

private theorem norm_binary_tail_integral_le {f : ℝ → ℂ} (hf : Continuous f)
    {H : ℝ} (hH : 0 < H) (hhalf : H ≤ 1 / 2)
    (hb : ∀ x ∈ Set.Icc H (1 / 2), ‖f x‖ ≤ 1 / (4 * x ^ 2)) :
    ‖∫ x in H..(1 / 2), f x‖ ≤ 1 / (4 * H) := by
  have hz : (0 : ℝ) ∉ Set.uIcc H (1 / 2) := by
    rw [Set.uIcc_of_le hhalf]
    exact fun h => hH.not_ge h.1
  have hc : ContinuousOn (fun x : ℝ => 1 / (4 * x ^ 2)) (Set.uIcc H (1 / 2)) := by
    apply continuousOn_const.div (continuous_const.mul (continuous_id.pow 2)).continuousOn
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hz hx
    change (4 : ℝ) * x ^ 2 ≠ 0
    exact mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hx0)
  apply (intervalIntegral.norm_integral_le_integral_norm hhalf).trans
  apply (intervalIntegral.integral_mono_on hhalf (hf.norm.intervalIntegrable _ _)
    hc.intervalIntegrable hb).trans
  have he (x : ℝ) : 1 / (4 * x ^ 2) = (1 / 4) * x ^ (-2 : ℤ) := by
    simp [zpow_neg, div_mul_eq_div_mul_one_div, one_div, mul_comm]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
  norm_num
  field_simp [hH.ne']
  nlinarith [sq_nonneg H]

/-- Removing the two outer pieces of the unit period costs at most `1/(2H)`.
The bound is uniform in the truncation length `N`. -/
theorem norm_binarySingularIntegral_sub_le {N n : ℕ} (hn : n ≤ N) {H : ℝ}
    (hH : 0 < H) (hhalf : H ≤ 1 / 2) :
    ‖binarySingularIntegral N n H - ((n - 1 : ℕ):ℂ)‖ ≤ 1 / (2 * H) := by
  let f := fun β : ℝ => mainExpSum N β ^ 2 * e (-β * n)
  have hf : Continuous f :=
    ((continuous_mainExpSum N).pow 2).mul (continuous_e.comp (continuous_neg.mul continuous_const))
  have hb {β : ℝ} (hβ : 0 < |β|) (hh : |β| ≤ 1 / 2) : ‖f β‖ ≤ 1 / (4 * |β| ^ 2) := by
    dsimp only [f]
    rw [norm_mul, norm_e, mul_one, norm_pow]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_mainExpSum_le_inv_two_abs N hβ hh) 2).trans_eq
    ring
  have hpos := norm_binary_tail_integral_le hf hH hhalf (fun x hx => by
    have hx0 : 0 < x := hH.trans_le hx.1
    simpa only [abs_of_pos hx0] using hb (abs_pos.mpr hx0.ne') (by simpa only [abs_of_pos hx0] using hx.2))
  have hneg := norm_binary_tail_integral_le (hf.comp continuous_neg) hH hhalf (fun x hx => by
    have hx0 : 0 < x := hH.trans_le hx.1
    simpa only [Function.comp_apply, abs_neg, abs_of_pos hx0] using
      hb (β := -x) (by simpa only [abs_neg, abs_of_pos hx0] using hx0) (by simpa only [abs_neg, abs_of_pos hx0] using hx.2))
  change ‖∫ x in H..(1 / 2), f (-x)‖ ≤ _ at hneg
  rw [intervalIntegral.integral_comp_neg] at hneg
  have h1 := intervalIntegral.integral_add_adjacent_intervals («μ» := volume)
    (hf.intervalIntegrable (-(1 / 2)) (-H)) (hf.intervalIntegrable (-H) H)
  have h2 := intervalIntegral.integral_add_adjacent_intervals («μ» := volume)
    (hf.intervalIntegrable (-(1 / 2)) H) (hf.intervalIntegrable H (1 / 2))
  rw [← binarySingularIntegral_half hn, binarySingularIntegral, binarySingularIntegral]
  change ‖(∫ x in (-H)..H, f x) - ∫ x in (-(1 / 2))..(1 / 2), f x‖ ≤ _
  rw [← h2, ← h1, show ∀ u v w : ℂ, v - (u + v + w) = -(u + w) by intros; ring, norm_neg]
  apply (norm_add_le _ _).trans
  exact (add_le_add hneg hpos).trans_eq (by ring)

private def binaryModel (N n q : ℕ) (a : ℤ) (α : ℝ) : ℂ :=
  ((μ q : ℂ) / q.totient * mainExpSum N (α - a / q)) ^ 2 * e (-α * n)

private theorem continuous_binaryIntegrand (N n : ℕ) :
    Continuous (fun α : ℝ => primeExpSum N α ^ 2 * e (-α * n)) :=
  ((continuous_primeExpSum N).pow 2).mul (continuous_e.comp (continuous_neg.mul continuous_const))

private theorem continuous_binaryModel (N n q : ℕ) (a : ℤ) : Continuous (binaryModel N n q a) :=
  ((continuous_const.mul ((continuous_mainExpSum N).comp
    (continuous_id.sub continuous_const))).pow 2).mul
    (continuous_e.comp (continuous_neg.mul continuous_const))

private theorem setIntegral_binaryModel {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (N n : ℕ)
    {Q : ℝ} (hQ : 0 < Q) :
    ∫ α in majorArc q a Q, binaryModel N n q a α =
      ((μ q : ℂ) / q.totient) ^ 2 * e ((a : ℝ) * (-(n : ℝ)) / q) *
        binarySingularIntegral N n (1 / (q * Q)) := by
  rw [setIntegral_majorArc_eq _ hq a hQ, binarySingularIntegral,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro β _
  simp only [binaryModel, add_sub_cancel_left]
  rw [show -((a : ℝ) / q + β) * n = (a : ℝ) * (-(n : ℝ)) / q + -β * n by ring, e_add]
  ring

private theorem sum_setIntegral_binaryModel {q : ℕ} (hq : 1 ≤ q) (N n : ℕ)
    {Q : ℝ} (hQ : 0 < Q) :
    ∑ a ∈ coprimeResidues q, ∫ α in majorArc q a Q, binaryModel N n q a α =
      (singularTermBinary q n : ℂ) * binarySingularIntegral N n (1 / (q * Q)) := by
  simp_rw [setIntegral_binaryModel hq _ N n hQ]
  rw [← sum_mul, ← mul_sum]
  congr 1
  rw [div_pow, singularTermBinary]
  simp only [show q ≠ 0 by omega, ↓reduceIte]
  push_cast
  rw [← ramanujanSum_eq_ofReal_re hq, ramanujanSum]
  simp

private theorem norm_binaryModel_diff {q N n : ℕ} (hq : 0 < q) (a : ℤ) (α : ℝ) :
    ‖primeExpSum N α ^ 2 * e (-α * n) - binaryModel N n q a α‖ ≤
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ * (7 * N) := by
  let z := primeExpSum N α
  let w := (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)
  have hz : ‖z‖ ≤ 6 * N := norm_primeExpSum_le (Nat.cast_nonneg N) α
  have hmu : ‖(μ q : ℂ)‖ ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hw : ‖w‖ ≤ N := by
    dsimp only [w]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    have hc : ‖(μ q : ℂ)‖ / q.totient ≤ 1 :=
      (div_le_one (by linarith)).mpr (hmu.trans hφ)
    simpa only [one_mul] using mul_le_mul hc (norm_mainExpSum_le N (α - a / q))
      (norm_nonneg _) zero_le_one
  change ‖z ^ 2 * _ - w ^ 2 * _‖ ≤ ‖z - w‖ * _
  rw [← sub_mul, norm_mul, norm_e, mul_one, show z ^ 2 - w ^ 2 = (z-w)*(z+w) by ring,norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _)

/-- Squaring the major-arc approximations and integrating gives the truncated singular series,
with its singular integral at each arc width. The error `D q` bounds the linear
approximation pointwise on all major arcs of denominator `q`. -/
theorem norm_goldbachBinary_majorArcIntegral_sub_le (N n : ℕ) {P Q : ℝ} (hP : 1 ≤ P)
    (hPQ : 2 * P ≤ Q) (D : ℕ → ℝ)
    (happrox : ∀ q ∈ majorArcDenoms P, ∀ a ∈ coprimeResidues q, ∀ α ∈ majorArc q a Q,
      ‖primeExpSum N α - (μ q : ℂ) / q.totient * mainExpSum N (α - a / q)‖ ≤ D q) :
    ‖majorArcIntegral (fun α => primeExpSum N α ^ 2 * e (-α * n)) P Q -
      ∑ q ∈ majorArcDenoms P, (singularTermBinary q n : ℂ) *
        binarySingularIntegral N n (1 / (q * Q))‖ ≤
      ∑ q ∈ majorArcDenoms P, (q.totient : ℝ) * (D q * (7 * N) * (2 / (q * Q))) := by
  have hQ : 0 < Q := by linarith
  rw [majorArcIntegral_eq_sum_of_continuous (continuous_binaryIntegrand N n) hPQ, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  refine sum_le_sum fun q hq => ?_
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  rw [← sum_setIntegral_binaryModel hq1 N n hQ, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ coprimeResidues q, D q * (7 * N) * (2 / (q * Q)) := by
      refine sum_le_sum fun a ha => ?_
      have hf : IntegrableOn (fun α : ℝ => primeExpSum N α ^ 2 * e (-α * n)) (majorArc q a Q) :=
        (continuous_binaryIntegrand N n).continuousOn.integrableOn_Icc
      have hg : IntegrableOn (binaryModel N n q a) (majorArc q a Q) :=
        (continuous_binaryModel N n q a).continuousOn.integrableOn_Icc
      rw [← integral_sub hf hg]
      have hmeas : volume (majorArc q a Q) < ⊤ := by rw [volume_majorArc hq1 _ hQ]; simp
      have hb := norm_setIntegral_le_of_norm_le_const hmeas
        (fun α hα => (norm_binaryModel_diff (n := n) hq1 a α).trans (mul_le_mul_of_nonneg_right
          (by simpa using happrox q hq a ha α hα) (by positivity)))
      simpa [Measure.real, volume_majorArc hq1 _ hQ, ENNReal.toReal_ofReal (by positivity :
        (0 : ℝ) ≤ 2 / (q * Q))] using hb
    _ = _ := by
      simp [coprimeResidues, Nat.totient_eq_card_coprime, Nat.coprime_comm, nsmul_eq_mul]

/-- The weighted denominator moment controls both the missing tail and the
incomplete model integrals at every retained denominator. -/
theorem norm_binaryModelSum_sub_series_le {N n M : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    (hM : 1 ≤ M) (hMN : 2*(M:ℝ)^2 ≤ N) :
    ‖(∑ q ∈ Icc 1 M, (singularTermBinary q n:ℂ)*binarySingularIntegral N n (1/(q*((N:ℝ)/M)))) -
      (goldbachBinarySingularSeries n:ℂ) * ((n-1:ℕ):ℂ)‖ ≤
      (N/(M:ℝ)^(1/8:ℝ))*binarySeriesMoment n := by
  let S := Icc 1 M
  let z := fun q : ℕ => (singularTermBinary q n:ℂ)
  let J := fun q : ℕ => binarySingularIntegral N n (1/(q*((N:ℝ)/M)))
  let c : ℂ := (n-1:ℕ)
  let b := fun q : ℕ => (q:ℝ)^(1/8:ℝ)*|singularTermBinary q n|
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hNp : (0:ℝ)<N := by exact_mod_cast hn.trans hnN
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hr : 0 < (M:ℝ)^(1/8:ℝ) := Real.rpow_pos_of_pos hMp _
  have hn' : ‖c‖ ≤ N := by simpa [c] using (show ((n-1:ℕ):ℝ) ≤ N by exact_mod_cast (Nat.sub_le n 1).trans hnN)
  let u := fun q : ℕ => if q∈S then z q*J q else 0
  have hu : Summable u := summable_of_ne_finset_zero (s := S) (fun q hq => by simp [u,hq])
  have hz : Summable (fun q => z q*c) := ((Complex.ofRealCLM.hasSum (summable_singularTermBinary hn).hasSum).summable).mul_right c
  have hu' : ∑' q, u q = ∑ q ∈ S, z q*J q := by
    rw [tsum_eq_sum (s := S) (fun q hq => by simp [u,hq])]
    exact sum_congr rfl (fun q hq => by simp [u,hq])
  have hz' : ∑' q, z q*c = (goldbachBinarySingularSeries n:ℂ)*c := by
    rw [tsum_mul_right]
    congr 1
    exact (Complex.ofReal_tsum _).symm
  have hpt (q : ℕ) : ‖u q-z q*c‖ ≤ (N/(M:ℝ)^(1/8:ℝ))*b q := by
    by_cases hq : q = 0
    · subst q; simp [u,z,b,S]
    have hqp : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hqr := Real.rpow_pos_of_pos hqp (1/8)
    have hfactor : N*((q:ℝ)/M)^(1/8:ℝ)*|singularTermBinary q n| = (N/(M:ℝ)^(1/8:ℝ))*b q := by
      rw [Real.div_rpow hqp.le hMp.le]
      dsimp [b]; ring
    rw [← hfactor]
    by_cases hs : q∈S
    · obtain ⟨hq1,hqM⟩ := mem_Icc.mp hs
      have hqM' : (q:ℝ) ≤ M := by exact_mod_cast hqM
      have hQ : 0 < (N:ℝ)/M := div_pos hNp hMp
      have hlarge : 2 ≤ (q:ℝ)*(N/M) := by
        have ht : 2 ≤ (N:ℝ)/M := (le_div_iff₀ hMp).mpr (by nlinarith)
        exact ht.trans (le_mul_of_one_le_left hQ.le (by exact_mod_cast hq1))
      have hj := norm_binarySingularIntegral_sub_le hnN (one_div_pos.mpr (mul_pos hqp hQ))
        (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hlarge)
      have hratio : (q:ℝ)/M ≤ ((q:ℝ)/M)^(1/8:ℝ) := by
        conv_lhs => rw [← Real.rpow_one ((q:ℝ)/M)]
        exact Real.rpow_le_rpow_of_exponent_ge (div_pos hqp hMp)
          ((div_le_one hMp).mpr hqM') (by norm_num)
      have hj' : ‖J q-c‖ ≤ (N:ℝ)*((q:ℝ)/M)^(1/8:ℝ) := by
        apply hj.trans
        calc
          _ = (N:ℝ)*((q:ℝ)/M)/2 := by field_simp
          _ ≤ (N:ℝ)*((q:ℝ)/M) := by have := div_nonneg hqp.le hMp.le; nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_left hratio hNp.le
      simp only [u,hs,ite_true,← mul_sub,norm_mul,z,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hj' (abs_nonneg _)).trans_eq (mul_comm _ _)
    · have hMq : M ≤ q := by have : q ∉ Icc 1 M := hs; simp only [mem_Icc,not_and] at this; specialize this (by omega); omega
      have h1 : 1 ≤ ((q:ℝ)/M)^(1/8:ℝ) := Real.one_le_rpow ((one_le_div hMp).mpr (by exact_mod_cast hMq)) (by norm_num)
      simp only [u,hs,ite_false,zero_sub,norm_neg,norm_mul,z,Complex.norm_real,Real.norm_eq_abs]
      rw [mul_comm |singularTermBinary q n|]
      gcongr
      exact hn'.trans (le_mul_of_one_le_right hNp.le h1)
  have hb := (summable_binarySeriesMoment hn).mul_left ((N:ℝ)/(M:ℝ)^(1/8:ℝ))
  change ‖(∑ q ∈ S,z q*J q) - (goldbachBinarySingularSeries n:ℂ)*c‖ ≤ _
  rw [← hu', ← hz', ← hu.tsum_sub hz]
  calc
    _ ≤ ∑' q, ‖u q-z q*c‖ := norm_tsum_le_tsum_norm (hu.sub hz).norm
    _ ≤ ∑' q, (N/(M:ℝ)^(1/8:ℝ))*b q := (hu.sub hz).norm.tsum_le_tsum hpt hb
    _ = _ := by rw [tsum_mul_left]; rfl

end AnalyticNumberTheory.AdditiveNumberTheory
