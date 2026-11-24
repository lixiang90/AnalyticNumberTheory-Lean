import AnalyticNumberTheory.DirichletLFunctions.TuranWeights

/-!
# A finite prime sum detecting a Dirichlet L-function zero

Truncation suppresses the small and large indices exponentially in the order.
The proper prime powers contribute the same exponential saving uniformly.
-/

noncomputable section

open Finset Complex
open scoped Classical ArithmeticFunction
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.DirichletLFunctions

/-- The prime indices in a multiplicative interval. -/
def turanPrimes (X U : ℝ) : Finset ℕ := (Ioc ⌊X⌋₊ ⌊U⌋₊).filter Nat.Prime

private lemma laplace_nonneg (η : ℝ) (n : ℕ) : 0 ≤ mangoldtLaplaceTerm η n := by
  have h := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  dsimp only [mangoldtLaplaceTerm]; positivity

/-- Truncation to primes in a fixed logarithmic window, uniformly in the character. -/
theorem turan_prime_window_error :
    ∃ D > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {η : ℝ},
      0 < η → η ≤ 1/1024 → ∀ (t : ℝ) (m : ℕ) {X U : ℝ},
      1 ≤ X → X ≤ U → 1024*(η*Real.log X) ≤ m → 64*m ≤ η*Real.log U →
      ‖(∑' n, turanMangoldtTerm χ η t m n) - ∑ n ∈ turanPrimes X U, turanMangoldtTerm χ η t m n‖ ≤
        D*(1/256:ℝ)^m := by
  obtain ⟨B,hB,HB⟩ := mangoldtLaplaceTerm_sum_bound
  let P := ∑' n, higherPrimePowerWeight n
  have hP : 0 ≤ P := tsum_nonneg higherPrimePowerWeight_nonneg
  refine ⟨5*B+P,by positivity,?_⟩
  intro q _ χ η hη hη' t m X U hX hU hlow hhigh
  let W := turanPrimes X U
  let a := turanMangoldtTerm χ η t m
  let c := (1/256:ℝ)^m
  let g (n : ℕ) := mangoldtLaplaceTerm η n + mangoldtLaplaceTerm (η/4) n + higherPrimePowerWeight n
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hg (n : ℕ) : 0 ≤ g n := add_nonneg (add_nonneg (laplace_nonneg ..) (laplace_nonneg ..)) (higherPrimePowerWeight_nonneg n)
  obtain ⟨h1,h1'⟩ := HB hη (by linarith)
  obtain ⟨h2,h2'⟩ := HB (by linarith : 0<η/4) (by linarith)
  have hgs : Summable g := (h1.add h2).add summable_higherPrimePowerWeight
  let R (n : ℕ) := if n ∈ W then 0 else a n
  have hr (n : ℕ) : ‖R n‖ ≤ c*η*g n := by
    dsimp only [R]
    split_ifs with hn
    · rw [norm_zero]; positivity [hg n]
    by_cases hnp : n.Prime
    · have hno : n ∉ Ioc ⌊X⌋₊ ⌊U⌋₊ := fun h => hn (mem_filter.mpr ⟨h,hnp⟩)
      by_cases hl : n ≤ ⌊X⌋₊
      · have hnx : (n:ℝ) ≤ X := (by exact_mod_cast hl : (n:ℝ) ≤ ⌊X⌋₊).trans (Nat.floor_le (by linarith))
        have hs := norm_turan_term_small χ hη.le t m n ((by
          gcongr; exact_mod_cast hnp.pos : 1024*(η*Real.log n) ≤ 1024*(η*Real.log X)).trans hlow)
        apply hs.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only [g]; linarith [laplace_nonneg (η/4) n,higherPrimePowerWeight_nonneg n]
      · have hnU : U < n := (Nat.floor_lt (by linarith : 0≤U)).mp (by
          by_contra! hh; exact hno (mem_Ioc.mpr ⟨by omega,hh⟩))
        have hl' := norm_turan_term_large χ hη.le t m n (hhigh.trans
          (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hnU.le) hη.le))
        apply hl'.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only [g]; linarith [laplace_nonneg η n,higherPrimePowerWeight_nonneg n]
    · apply (norm_turan_term_nonprime χ hη hη' t m n hnp).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp only [g]; linarith [laplace_nonneg η n,laplace_nonneg (η/4) n]
  have hmajor := hgs.mul_left (c*η)
  have hrnorm : Summable (fun n => ‖R n‖) := hmajor.of_nonneg_of_le (fun n => norm_nonneg _) hr
  have hfin : Summable (fun n => if n ∈ W then a n else 0) :=
    summable_of_ne_finset_zero (s:=W) fun n hn => by simp [hn]
  have hadd : ∀ n, (if n ∈ W then a n else 0)+R n = a n := by intro n; by_cases h : n∈W <;> simp [R,h]
  have he : (∑' n, a n) = (∑ n ∈ W, a n) + ∑' n, R n := by
    have hfinite : (∑' n, if n ∈ W then a n else 0) = ∑ n ∈ W, a n := by
      rw [tsum_eq_sum (s:=W) (fun n hn => ite_eq_right hn)]
      exact sum_congr rfl (fun n hn => ite_eq_left hn)
    rw [←hfinite,←hfin.tsum_add hrnorm.of_norm]
    exact tsum_congr fun n => (hadd n).symm
  change ‖(∑' n, a n) - ∑ n ∈ W, a n‖ ≤ _
  rw [he,add_sub_cancel_left]
  apply ((norm_tsum_le_tsum_norm hrnorm).trans (hrnorm.tsum_le_tsum hr hmajor)).trans
  rw [tsum_mul_left]
  have hgg : (∑' n, g n) = (∑' n, mangoldtLaplaceTerm η n) + (∑' n, mangoldtLaplaceTerm (η/4) n)+P :=
    ((h1.add h2).tsum_add summable_higherPrimePowerWeight).trans (by rw [h1.tsum_add h2])
  rw [hgg]
  have hP' := mul_le_mul_of_nonneg_right (by linarith : η ≤ 1) hP
  change c*η*_ ≤ (5*B+P)*c
  rw [mul_assoc,mul_comm (5*B+P)]
  exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- A nearby zero forces a large finite prime sum for an order between `M` and `2M`. -/
theorem LFunction_turan_prime_detector :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
    ∀ {t η Y X U : ℝ}, (q:ℝ)*(|t|+2) ≤ Y → 0 < η → η ≤ 1/1024 → 1 ≤ η*Real.log Y →
    1 ≤ X → X ≤ U → ∀ {ρ : ℂ}, DirichletCharacter.LFunction χ ρ = 0 →
      ‖(((1+η:ℝ):ℂ)+(t:ℂ)*I)-ρ‖ ≤ 2*η →
    ∀ {M : ℕ}, C*(1+η*Real.log Y) ≤ M → 1024*(η*Real.log X) ≤ M →
      128*(M:ℝ) ≤ η*Real.log U →
      ∃ m ∈ Icc M (2*M), (1/128:ℝ)^(2*M+1) ≤
        ‖∑ n ∈ turanPrimes X U, turanMangoldtTerm χ η t m n‖ := by
  obtain ⟨C,hC,HC⟩ := LFunction_turan_zero_detector
  obtain ⟨D,hD,HD⟩ := turan_prime_window_error
  refine ⟨max C (128*D+1),lt_of_lt_of_le hC (le_max_left ..),?_⟩
  intro q _ χ hχ t η Y X U hY hη hη' hg hX hU ρ hz hd M hM hlow hhigh
  have hCM := (mul_le_mul_of_nonneg_right (le_max_left C (128*D+1)) (by linarith : 0≤1+η*Real.log Y)).trans hM
  have hDM : 128*D ≤ M := by
    have := (mul_le_mul (le_max_right C (128*D+1)) (by linarith : 1≤1+η*Real.log Y) zero_le_one (by positivity)).trans hM
    linarith
  obtain ⟨k,hk,hbig⟩ := HC hχ hY hη hη' hg hz hd hCM
  obtain ⟨hk₁,hk₂⟩ := mem_Ioc.mp hk
  let m := k-1
  have hkm : k=m+1 := by dsimp [m]; omega
  have hm₁ : M ≤ m := by omega
  have hm₂ : m ≤ 2*M := by omega
  have hmR : (M:ℝ) ≤ m := by exact_mod_cast hm₁
  have hmR' : (m:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast hm₂
  have herr := HD χ hη hη' t m hX hU (hlow.trans hmR) (by linarith)
  have htotal : (1/64:ℝ)^(m+1) ≤ ‖∑' n, turanMangoldtTerm χ η t m n‖ := by
    rw [(hasSum_turanMangoldtTerm χ hη t m).tsum_eq,norm_mul,norm_neg,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hη,←hkm]
    exact hbig
  have hm4 : (m:ℝ) ≤ 4^m := by
    calc
      (m:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast (Nat.lt_two_pow_self (n:=m)).le
      _ ≤ (4:ℝ)^m := by gcongr; norm_num
  have herror : D*(1/256:ℝ)^m ≤ (1/128)*(1/64:ℝ)^m := by
    have h := mul_le_mul_of_nonneg_right ((hDM.trans hmR).trans hm4) (show 0≤(1/256:ℝ)^m by positivity)
    rw [mul_assoc,←mul_pow] at h
    norm_num at h
    linarith only [h]
  refine ⟨m,mem_Icc.mpr ⟨hm₁,hm₂⟩,?_⟩
  calc
    (1/128:ℝ)^(2*M+1) ≤ (1/128:ℝ)^(m+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ (1/128)*(1/64:ℝ)^m := by rw [pow_succ,mul_comm]; gcongr; norm_num
    _ ≤ _ := by
      have htriangle := (norm_sub_norm_le (∑' n, turanMangoldtTerm χ η t m n)
        (∑ n ∈ turanPrimes X U, turanMangoldtTerm χ η t m n)).trans (herr.trans herror)
      rw [pow_succ] at htotal
      linarith

end AnalyticNumberTheory.DirichletLFunctions
