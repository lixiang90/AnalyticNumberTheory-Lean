import AnalyticNumberTheory.ExponentialSums.PrimeContourFrequencyScale
import AnalyticNumberTheory.ExponentialSums.PrimeFrequencyShift
import AnalyticNumberTheory.AdditiveNumberTheory.RationalRefinement

/-! # The two-contour method at nearby real frequencies -/

noncomputable section
open Complex Finset Real
open AnalyticNumberTheory.AdditiveNumberTheory

namespace AnalyticNumberTheory.ExponentialSums

/-- A uniform initial-segment version of the rational contour bound.
It also covers cutoffs below the modulus and moduli larger than x. -/
theorem primeExpSum_rational_contour_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {a : ℤ} {x y : ℝ},
      a.natAbs.Coprime q → 1 ≤ x → 0 ≤ y → y ≤ x →
      ‖primeExpSum y ((a : ℝ)/q)‖ ≤
        C*(x/(q : ℝ)^(1/4 : ℝ)+x^(7/8 : ℝ)*(q : ℝ)^(1/8 : ℝ))*(1+Real.log x)^3 := by
  obtain ⟨K,hK,rational⟩ := primeExpSum_rational_contour
  refine ⟨max 6 K, (by norm_num : (0 : ℝ) < 6).trans_le (le_max_left ..), ?_⟩
  intro q _ a x y ha hx hy hyx
  let R := x/(q : ℝ)^(1/4 : ℝ)+x^(7/8 : ℝ)*(q : ℝ)^(1/8 : ℝ)
  let L := 1+Real.log x
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq₀ := zero_lt_one.trans_le hq
  have hx₀ := zero_lt_one.trans_le hx
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL₀ := zero_le_one.trans hL
  change _ ≤ max 6 K*R*L^3
  by_cases hqy : (q : ℝ) ≤ y
  · apply (rational ha hqy).trans
    calc
      _ ≤ K*(R*L^3) := mul_le_mul_of_nonneg_left (primeContourRationalScale_le_at_larger_cutoff
        (hq.trans hqy) hyx hq₀) hK.le
      _ ≤ (max 6 K)*(R*L^3) := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
      _ = _ := by ring
  · have hyR : y ≤ R := (le_contour_denominator_term hy hyx (le_of_not_ge hqy)).trans
      (le_add_of_nonneg_left (by positivity : 0 ≤ x/(q : ℝ)^(1/4 : ℝ)))
    exact (norm_primeExpSum_le hy _).trans ((mul_le_mul (le_max_left ..) hyR hy (by positivity)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)))

/-- For |α−a/q| ≤ 1/q², the sharp von Mangoldt sum up to any y ≤ x
is bounded by (x q^(−1/8)+x^(7/8)q^(1/8))(1+log x)³, up to an absolute
constant. The argument uses partial summation and Farey refinement. -/
theorem primeExpSum_contour :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {q : ℕ} {α x y : ℝ}, 1 ≤ q → a.natAbs.Coprime q →
      |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2 → 1 ≤ x → 0 ≤ y → y ≤ x →
      ‖primeExpSum y α‖ ≤ C*primeContourFrequencyScale x q*(1+Real.log x)^3 := by
  obtain ⟨C,hC,rational⟩ := primeExpSum_rational_contour_uniform
  let K := C*(1+4*Real.pi)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨3*K, by positivity, ?_⟩
  intro a q α x y hq ha hα hx hy hyx
  let R (s : ℕ) := x/(s : ℝ)^(1/4 : ℝ)+x^(7/8 : ℝ)*(s : ℝ)^(1/8 : ℝ)
  let V := primeContourFrequencyScale x q
  let L := 1+Real.log x
  have hx₀ := zero_lt_one.trans_le hx
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ := zero_lt_one.trans_le hq₁
  have hR (s : ℕ) : 0 ≤ R s := by dsimp only [R]; positivity
  have hu : 0 ≤ x/(q : ℝ)^(1/8 : ℝ) := by positivity
  have hv : 0 ≤ x^(7/8 : ℝ)*(q : ℝ)^(1/8 : ℝ) := by positivity
  have hV : 0 ≤ V := add_nonneg hu hv
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have narrow {s : ℕ} [NeZero s] {b : ℤ} (hb : b.natAbs.Coprime s) (hβ : x*|α-(b : ℝ)/s| ≤ 2)
      (hscale : R s ≤ 3*V) : ‖primeExpSum y α‖ ≤ (3*K)*V*L^3 := by
    let β := α-(b : ℝ)/s
    have hmain : 0 ≤ C*R s*L^3 := by positivity [hR s]
    have h := norm_primeExpSum_shift_of_bound (α := (b : ℝ)/s) hy hmain
      (fun t ht => rational hb hx ht.1 (ht.2.trans hyx)) β
    rw [show (b : ℝ)/s+β=α by dsimp only [β]; ring] at h
    have hyβ := (mul_le_mul_of_nonneg_right hyx (abs_nonneg β)).trans hβ
    have hf : 1+2*Real.pi*y*|β| ≤ 1+4*Real.pi := by
      nlinarith only [mul_le_mul_of_nonneg_left hyβ Real.pi_pos.le]
    calc
      _ ≤ (C*R s*L^3)*(1+4*Real.pi) := h.trans (mul_le_mul_of_nonneg_left hf hmain)
      _ = K*(R s)*L^3 := by dsimp only [K]; ring
      _ ≤ K*(3*V)*L^3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hK.le) (by positivity)
      _ = _ := by ring
  by_cases hnear : x*|α-(a : ℝ)/q| ≤ 2
  · letI : NeZero q := ⟨by omega⟩
    apply narrow ha hnear
    have hpow := Real.rpow_le_rpow_of_exponent_le hq₁ (by norm_num : (1/8 : ℝ) ≤ 1/4)
    have hfirst := div_le_div_of_nonneg_left hx₀.le (Real.rpow_pos_of_pos hq₀ _) hpow
    have hle : R q ≤ V := add_le_add hfirst le_rfl
    linarith only [hle,hV]
  · obtain ⟨b,r,hr,hb,hrlo,hrhi,hap⟩ := exists_narrow_rational_approximation hx₀ hq ha hα (lt_of_not_ge hnear)
    letI : NeZero r := ⟨by omega⟩
    apply narrow hb hap.le
    apply (primeContour_scale_of_refinement hx₀ hq₁ hrlo.le ((le_div_iff₀ hq₀).mp hrhi)).trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) (by norm_num)

end AnalyticNumberTheory.ExponentialSums
