import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import AnalyticNumberTheory.PrimeDistribution.DirichletPolynomialSampling

/-!
# Dyadic decomposition of Möbius zero detectors

The coefficients and their square mean are shared by the zeta detector and its
Dirichlet-character twists.
-/

noncomputable section

open Finset Complex
open scoped Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.PrimeDistribution.ZeroDetector

/-- Detector coefficients restricted to the dyadic block beginning at `2^i`. -/
def blockCoeff (X i n : ℕ) : ℂ :=
  if X < n ∧ n ≤ X^2 ∧ Nat.log 2 n = i then zetaDetectorCoeff X n else 0

/-- Indices of dyadic blocks which meet the detector support. -/
def blocks (X : ℕ) : Finset ℕ :=
  (range (Nat.log 2 (X^2)+1)).filter fun i => X < 2*(2^i) ∧ 2^i ≤ X^2

private lemma logBlock_shape {n : ℕ} (hn : n ≠ 0) :
    2^(Nat.log 2 n) ≤ n ∧ n < 2*2^(Nat.log 2 n) :=
  ⟨Nat.pow_log_le_self 2 hn, by simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self one_lt_two n⟩

/-- A multiplicatively twisted detector decomposes into the same dyadic blocks. -/
lemma tail_twist_by_blocks (g : ℕ → ℂ) (X : ℕ) (s : ℂ) :
    ∑ n ∈ Ioc X (X^2), zetaDetectorCoeff X n*g n*(n:ℂ)^(-s) =
      ∑ i ∈ blocks X, dirichletPoly (fun n => blockCoeff X i n*g n) (2*2^i) s := by
  have hmap (n : ℕ) (hn : n ∈ Ioc X (X^2)) : Nat.log 2 n ∈ blocks X := by
    obtain ⟨hX,hr⟩ := mem_Ioc.mp hn
    have h := logBlock_shape (by omega : n ≠ 0)
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hr)), hX.trans h.2, h.1.trans hr⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun i hi => ?_
  unfold dirichletPoly
  simp only [blockCoeff, ite_mul, zero_mul, ← sum_filter]
  congr 1
  ext n
  simp only [mem_filter,mem_Ioc,mem_Icc]
  constructor
  · rintro ⟨⟨h₁,h₂⟩, h₃⟩
    have h := logBlock_shape (by omega : n ≠ 0)
    rw [h₃] at h
    exact ⟨⟨by omega,h.2.le⟩,h₁,h₂,h₃⟩
  · tauto

/-- The divisor-square mean bounds a block at the left edge of a strip. -/
lemma block_energy {X i : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    dirichletPolyEnergy (blockCoeff X i) (2*2^i) σ ≤
      (2*(2^i:ℕ) : ℝ) * (1+Real.log (2*(2^i:ℕ):ℝ))^3 * ((2^i:ℕ):ℝ)^(-2*σ) := by
  let M := 2^i
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  have hcoef (n : ℕ) (_ : n ∈ Icc 1 (2*M)) :
      ‖blockCoeff X i n‖^2*(n:ℝ)^(-2*σ) ≤ (n.divisors.card:ℝ)^2*(M:ℝ)^(-2*σ) := by
    unfold blockCoeff
    split_ifs with h
    · have hmn : M ≤ n := by dsimp [M]; rw [← h.2.2]; exact (logBlock_shape (by omega : n ≠ 0)).1
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_zetaDetectorCoeff_le ..) 2)
        (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast hmn) (by linarith))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]; positivity
  apply (sum_le_sum hcoef).trans
  rw [← sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h := sum_Icc_card_divisors_sq_le (2*M)
  rw [max_eq_left (by omega)] at h
  exact_mod_cast h

/-- At most logarithmically many summands occur in the dyadic decomposition. -/
lemma block_count_le {X : ℕ} (hX : 1 ≤ X) :
    ((blocks X).card : ℝ) ≤ 5*(1+Real.log X) := by
  have hcard : (blocks X).card ≤ Nat.log 2 (X^2)+1 :=
    (card_le_card (filter_subset ..)).trans_eq (card_range _)
  have hpow : (2:ℝ)^(Nat.log 2 (X^2)) ≤ (X:ℝ)^2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (by positivity : X^2≠0)
  have h := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hlog₂ : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog := Real.log_nonneg (by exact_mod_cast hX : (1:ℝ)≤X)
  have hcar : ((blocks X).card:ℝ) ≤ (Nat.log 2 (X^2)+1:ℕ) := Nat.cast_le.mpr hcard
  push_cast at hcar
  nlinarith only [hcar,h,hlog,mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (X^2)))]


/-- Upper bound for the coefficient and length factors in a sampled dyadic block.
Here `H` bounds the length factor in units of the lower endpoint `2^i`. -/
theorem block_bound {X i : ℕ} (hX : 1 ≤ X) (hi : i ∈ blocks X)
    {σ K H W : ℝ} (hσ : σ ∈ Set.Icc (3/4:ℝ) 1) (hK : 0 ≤ K)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hlen : W ≤ H*(2^i:ℕ)) :
    9*(K*(1+Real.log X)) * (W*(1+Real.log (2*(2^i:ℕ):ℝ))^4 *
      dirichletPolyEnergy (blockCoeff X i) (2*2^i) σ) ≤
      (18*H*3^7*K) * (1+Real.log X)^8 * (X:ℝ)^(4*(1-σ)) := by
  let M := 2^i
  let L := 1+Real.log X
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  obtain ⟨hXM,hMX⟩ := (mem_filter.mp hi).2
  change X < 2*M at hXM
  change M ≤ X^2 at hMX
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ)<M := by linarith
  have hX0 : (0:ℝ)<X := by linarith
  have hl : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hXr]
  have hlog : 1+Real.log (2*(M:ℝ)) ≤ 3*L := by
    rw [Real.log_mul (by norm_num) hM0.ne']
    have h := Real.log_le_log hM0 (by exact_mod_cast hMX : (M:ℝ) ≤ (X:ℝ)^2)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    dsimp only [L]; linarith [Real.log_nonneg hXr, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog0 : 0 ≤ 1+Real.log (2*(M:ℝ)) := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2*(M:ℝ)); linarith
  have hsave : (M:ℝ)^2*(M:ℝ)^(-2*σ) ≤ (X:ℝ)^(4*(1-σ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hM0]
    have h := Real.rpow_le_rpow hM0.le (by exact_mod_cast hMX : (M:ℝ) ≤ (X:ℝ)^2) (by linarith [hσ.2] : 0 ≤ 2+ -2*σ)
    apply h.trans_eq
    rw [← Real.rpow_two, ← Real.rpow_mul hX0.le]; congr 1; ring
  have he := block_energy (X:=X) (i:=i) (by linarith [hσ.1] : 0 ≤ σ)
  change _ ≤ (2*(M:ℝ))*(1+Real.log (2*(M:ℝ)))^3*(M:ℝ)^(-2*σ) at he
  change 9*(K*L)*(W * (1+Real.log (2*(M:ℝ)))^4 * _) ≤ _
  calc
    _ ≤ 9*(K*L)*((H*M)*(3*L)^4*((2*(M:ℝ))*(3*L)^3*(M:ℝ)^(-2*σ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul _ (he.trans (by gcongr)) (sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
      gcongr
    _ = (18*H*3^7*K)*L^8 * ((M:ℝ)^2*(M:ℝ)^(-2*σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end AnalyticNumberTheory.PrimeDistribution.ZeroDetector
