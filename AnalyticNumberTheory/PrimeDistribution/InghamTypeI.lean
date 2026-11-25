import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import AnalyticNumberTheory.PrimeDistribution.DirichletPolynomialSampling

/-!
# Large values of divisor-bounded Dirichlet polynomials

The lower cutoff is comparable to the height, while the upper cutoff is free.
The strip sampling inequality permits varying real parts and clusters of ordinates.
-/

noncomputable section

open Finset Complex
open scoped Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.ExponentialSums

namespace AnalyticNumberTheory.PrimeDistribution.Ingham

/-- Detector coefficients restricted to the dyadic block beginning at `2^i`. -/
private def blockCoeff (a : ℕ → ℂ) (X U i n : ℕ) : ℂ :=
  if X < n ∧ n ≤ U ∧ Nat.log 2 n = i then a n else 0

/-- Indices of dyadic blocks which meet the detector support. -/
private def blocks (X U : ℕ) : Finset ℕ :=
  (range (Nat.log 2 U+1)).filter fun i => X < 2*(2^i) ∧ 2^i ≤ U

private lemma logBlock_shape {n : ℕ} (hn : n ≠ 0) :
    2^(Nat.log 2 n) ≤ n ∧ n < 2*2^(Nat.log 2 n) :=
  ⟨Nat.pow_log_le_self 2 hn, by simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self one_lt_two n⟩

/-- Partition the detector tail by the integer part of its base-two logarithm. -/
private lemma tail_by_blocks (a : ℕ → ℂ) (X U : ℕ) (s : ℂ) :
    ∑ n ∈ Ioc X U, a n*(n:ℂ)^(-s) =
      ∑ i ∈ blocks X U, dirichletPoly (blockCoeff a X U i) (2*2^i) s := by
  have hmap (n : ℕ) (hn : n ∈ Ioc X U) : Nat.log 2 n ∈ blocks X U := by
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
private lemma block_energy {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (n.divisors.card:ℝ)) {X U i : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    dirichletPolyEnergy (blockCoeff a X U i) (2*2^i) σ ≤
      (2*(2^i:ℕ) : ℝ) * (1+Real.log (2*(2^i:ℕ):ℝ))^3 * ((2^i:ℕ):ℝ)^(-2*σ) := by
  let M := 2^i
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  have hcoef (n : ℕ) (_ : n ∈ Icc 1 (2*M)) :
      ‖blockCoeff a X U i n‖^2*(n:ℝ)^(-2*σ) ≤ (n.divisors.card:ℝ)^2*(M:ℝ)^(-2*σ) := by
    unfold blockCoeff
    split_ifs with h
    · have hmn : M ≤ n := by dsimp [M]; rw [← h.2.2]; exact (logBlock_shape (by omega : n ≠ 0)).1
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (ha n) 2)
        (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast hmn) (by linarith))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]; positivity
  apply (sum_le_sum hcoef).trans
  rw [← sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h := sum_Icc_card_divisors_sq_le (2*M)
  rw [max_eq_left (by omega)] at h
  exact_mod_cast h

private lemma block_count {X U : ℕ} (hU : 1 ≤ U) :
    ((blocks X U).card:ℝ) ≤ 2*(1+Real.log U) := by
  have hc : (blocks X U).card ≤ Nat.log 2 U + 1 :=
    (card_le_card (filter_subset ..)).trans_eq (card_range _)
  have hpow : (2:ℝ)^(Nat.log 2 U) ≤ U := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : U≠0)
  have h := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at h
  have h₂ : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc' : ((blocks X U).card:ℝ) ≤ (Nat.log 2 U:ℝ)+1 := by exact_mod_cast hc
  nlinarith only [hc',h,mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 U))]

private theorem sampled_block {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (n.divisors.card:ℝ))
    {X U i : ℕ} (hi : i ∈ blocks X U) {S : Finset ℂ} {K σ : ℝ}
    (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hK : 0 ≤ K)
    (hre : ∀ z ∈ S, z.re ∈ Set.Icc σ (σ+1))
    (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < (2*X+1:ℕ))
    (hcount : ∀ j < 2*X+1, ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K) :
    ∑ z ∈ S, ‖dirichletPoly (blockCoeff a X U i) (2*2^i) z‖^2 ≤
      (18*(10+4*Real.pi)*2^7*K)*(1+Real.log U)^7*(U:ℝ)^(2*(1-σ)) := by
  let M := 2^i
  let L := 1+Real.log U
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  obtain ⟨hXM,hMU⟩ := (mem_filter.mp hi).2
  change X < 2*M at hXM
  change M ≤ U at hMU
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ)<M := by linarith
  have hU : 1 ≤ U := hM.trans hMU
  have hUr : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hlogU := Real.log_nonneg hUr
  have hl : 1 ≤ L := by dsimp [L]; linarith
  have hlog : 1+Real.log (2*(M:ℝ)) ≤ 2*L := by
    rw [Real.log_mul (by norm_num) hM0.ne']
    have h := Real.log_le_log hM0 (by exact_mod_cast hMU : (M:ℝ) ≤ U)
    dsimp only [L]; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog0 : 0 ≤ 1+Real.log (2*(M:ℝ)) := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2*(M:ℝ)); linarith
  have hsave : (M:ℝ)^2*(M:ℝ)^(-2*σ) ≤ (U:ℝ)^(2*(1-σ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hM0, show 2+-2*σ = 2*(1-σ) by ring]
    exact Real.rpow_le_rpow hM0.le (by exact_mod_cast hMU) (by linarith [hσ.2])
  have hlen : 2*((2*X+1:ℕ):ℝ)+2*Real.pi*(2*M:ℕ) ≤ (10+4*Real.pi)*(M:ℝ) := by
    push_cast
    have hxm : (X:ℝ)<2*M := by exact_mod_cast hXM
    nlinarith
  have he := block_energy ha (X:=X) (U:=U) (i:=i) hσ.1
  change _ ≤ (2*(M:ℝ))*(1+Real.log (2*(M:ℝ)))^3*(M:ℝ)^(-2*σ) at he
  apply (dirichletPoly_sampling_strip hK hre him hcount (blockCoeff a X U i) (N:=2*M) (by omega)).trans
  push_cast at hlen ⊢
  calc
    _ ≤ 9*K*(((10+4*Real.pi)*M)*(2*L)^4*((2*(M:ℝ))*(2*L)^3*(M:ℝ)^(-2*σ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul _ (he.trans (by gcongr)) (sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
      gcongr
    _ = (18*(10+4*Real.pi)*2^7*K)*L^7 * ((M:ℝ)^2*(M:ℝ)^(-2*σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end AnalyticNumberTheory.PrimeDistribution.Ingham

namespace AnalyticNumberTheory.PrimeDistribution

open Ingham

/-- Type I large values for Ingham's zero detector. If each point detects a
divisor-bounded tail on `X < n ≤ U` at level `V`, the count costs
`U^(2−2σ)`, the maximum number of ordinates in a unit interval, and nine logarithms. -/
theorem ingham_typeI_count {X U : ℕ} (hU : 1 ≤ U) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (n.divisors.card:ℝ)) {S : Finset ℂ} {K σ V : ℝ}
    (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hre : ∀ z ∈ S, z.re ∈ Set.Icc σ (σ+1))
    (him : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < (2*X+1:ℕ))
    (hcount : ∀ j < 2*X+1, ((S.filter (fun z => ⌊z.im⌋₊=j)).card:ℝ) ≤ K)
    (hdet : ∀ z ∈ S, V ≤ ‖∑ n ∈ Ioc X U, a n*(n:ℂ)^(-z)‖) :
    (S.card:ℝ)*V^2 ≤ (72*(10+4*Real.pi)*2^7*K)*(1+Real.log U)^9*(U:ℝ)^(2*(1-σ)) := by
  let J := blocks X U
  let P (i : ℕ) (z : ℂ) := dirichletPoly (blockCoeff a X U i) (2*2^i) z
  let D := 18*(10+4*Real.pi)*2^7*K
  let L := 1+Real.log U
  let W := (U:ℝ)^(2*(1-σ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by exact_mod_cast hU : (1:ℝ)≤U)]
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have each (z : ℂ) (hz : z ∈ S) : V^2 ≤ (J.card:ℝ) * ∑ i ∈ J, ‖P i z‖^2 := by
    have hd := hdet z hz
    rw [tail_by_blocks] at hd
    have hn : V ≤ ∑ i ∈ J, ‖P i z‖ := hd.trans (norm_sum_le ..)
    have hcs := sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun i => ‖P i z‖)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
    exact (pow_le_pow_left₀ hV hn 2).trans hcs
  have heach := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul, ←mul_sum] at heach
  rw [sum_comm] at heach
  have hd (i : ℕ) (hi : i∈J) : ∑ z ∈ S, ‖P i z‖^2 ≤ D*L^7*W :=
    sampled_block ha hi hσ hK hre him hcount
  have ha' := mul_le_mul_of_nonneg_left (sum_le_sum hd) (Nat.cast_nonneg (α:=ℝ) J.card)
  simp only [sum_const,nsmul_eq_mul] at ha'
  have hJ : (J.card:ℝ) ≤ 2*L := block_count hU
  calc
    _ ≤ (J.card:ℝ)*((J.card:ℝ)*(D*L^7*W)) := heach.trans ha'
    _ ≤ (2*L)*((2*L)*(D*L^7*W)) := by gcongr
    _ = _ := by dsimp [D,L,W]; ring

end AnalyticNumberTheory.PrimeDistribution
