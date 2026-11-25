import AnalyticNumberTheory.PrimeDistribution.HuxleyCutoffConditions
import AnalyticNumberTheory.PrimeDistribution.HuxleyBalance
import AnalyticNumberTheory.PrimeDistribution.InghamBalance

/-!
# The rational exponent in Huxley's density estimate

Balancing three of the four terms exactly gives a smaller density exponent
in the interior of the interval from three quarters to one.
-/

noncomputable section
open Real Set
namespace AnalyticNumberTheory.PrimeDistribution

/-- The power of the mollifier length in the sharp Huxley balance. -/
def huxleyRationalMollifierExponent (σ : ℝ) := (2*σ-1)/(2*(σ^2+σ-1))

/-- The power of the Riesz cutoff in the sharp Huxley balance. -/
def huxleyRationalCutoffExponent (σ : ℝ) := (5*σ-3)/(2*(σ^2+σ-1))

/-- Huxley's rational density exponent for `3/4≤σ≤1`. -/
def huxleyRationalExponent (σ : ℝ) := (5*σ-3)*(1-σ)/(σ^2+σ-1)

private theorem rational_denominator_pos {σ : ℝ} (hσ : 3/4≤σ) : 0<σ^2+σ-1 := by
  nlinarith only [hσ,mul_nonneg (sub_nonneg.mpr hσ) (by linarith : 0≤σ+3/4)]

/-- The exact excess of the density power over each of the four powers in
the large-value estimate. Three are equalities and the fourth leaves a
nonnegative remainder. -/
theorem huxley_rational_power_identities {σ : ℝ} (hσ : 3/4≤σ) :
    let a := huxleyRationalMollifierExponent σ
    let b := huxleyRationalCutoffExponent σ
    let p := huxleyRationalExponent σ
    b*(2*(1-σ))=p ∧ 1+a*(4-6*σ)=p ∧
      p-(1/3+a*(2/3)+b*(1/2-σ)*(4/3))=2*(1-σ)*(3*σ-2)/(3*(σ^2+σ-1)) ∧
      1+a*(2/5)+b*(1/2-σ)*(12/5)=p := by
  let d := σ^2+σ-1
  have hd : 0<d := rational_denominator_pos hσ
  let a := (2*σ-1)/(2*d)
  let b := (5*σ-3)/(2*d)
  let p := (5*σ-3)*(1-σ)/d
  change b*(2*(1-σ))=p ∧ 1+a*(4-6*σ)=p ∧
    p-(1/3+a*(2/3)+b*(1/2-σ)*(4/3))=2*(1-σ)*(3*σ-2)/(3*d) ∧
    1+a*(2/5)+b*(1/2-σ)*(12/5)=p
  dsimp only [a,b,p]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp [hd.ne'] <;> dsimp [d] <;> ring

/-- The optimal rational powers satisfy the four large-value constraints,
with equality for the diagonal, spacing, and twelve-fifths terms. -/
theorem huxley_rational_cutoff_conditions {σ : ℝ} (hσ : σ∈Icc (3/4:ℝ) 1) :
    HuxleyCutoffConditions σ (huxleyRationalMollifierExponent σ) (huxleyRationalCutoffExponent σ)
      (huxleyRationalExponent σ) := by
  let d := σ^2+σ-1
  have hd : 0<d := rational_denominator_pos hσ.1
  have hd₂ : 0<2*d := by positivity
  have hs := mul_nonneg (by linarith [hσ.1] : 0≤σ) (sub_nonneg.mpr hσ.2)
  have ht := mul_nonneg (sub_nonneg.mpr hσ.1) (by linarith [hσ.1] : 0≤σ+3/4)
  have hu := mul_nonneg (by linarith [hσ.1] : 0≤2*σ-1) (sub_nonneg.mpr hσ.2)
  have hv := mul_nonneg (by linarith [hσ.1] : 0≤σ) (by linarith [hσ.1] : 0≤3*σ-2)
  have hw := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (sub_nonneg.mpr hσ.2))
    (by linarith [hσ.1] : 0≤3*σ-2)) (by positivity : 0≤3*d)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := huxley_rational_power_identities hσ.1
  change HuxleyCutoffConditions σ ((2*σ-1)/(2*d)) ((5*σ-3)/(2*d)) ((5*σ-3)*(1-σ)/d)
  constructor
  · apply (le_div_iff₀ hd₂).mpr;dsimp [d];nlinarith only [hs]
  · apply (div_le_iff₀ hd₂).mpr;dsimp [d];nlinarith only [ht]
  · apply (le_div_iff₀ hd₂).mpr;dsimp [d];nlinarith only [hu]
  · apply (div_le_iff₀ hd₂).mpr;dsimp [d];nlinarith only [hv]
  · exact h₁
  · exact h₂.le
  · change 1/3+huxleyRationalMollifierExponent σ*(2/3)+huxleyRationalCutoffExponent σ*(1/2-σ)*(4/3)≤huxleyRationalExponent σ
    dsimp only [d] at hw
    linarith only [h₃,hw]
  · exact h₄.le

/-- Exact saving over the uniform density exponent with coefficient `12/5`. -/
theorem huxley_uniform_sub_rational {σ : ℝ} (hσ : 3/4≤σ) :
    huxleyExponent σ-huxleyRationalExponent σ=
      (1-σ)*(3*σ-1)*(4*σ-3)/(5*(σ^2+σ-1)) := by
  let d := σ^2+σ-1
  have hd : 0<d := rational_denominator_pos hσ
  change 12/5*(1-σ)-(5*σ-3)*(1-σ)/d=(1-σ)*(3*σ-1)*(4*σ-3)/(5*d)
  field_simp [hd.ne'];dsimp [d];ring

/-- The rational exponent is nonnegative and never exceeds the uniform
linear exponent on its closed range. -/
theorem huxley_rational_exponent_bounds {σ : ℝ} (hσ : σ∈Icc (3/4:ℝ) 1) :
    0≤huxleyRationalExponent σ ∧ huxleyRationalExponent σ≤huxleyExponent σ := by
  have hd := rational_denominator_pos hσ.1
  constructor
  · unfold huxleyRationalExponent
    exact div_nonneg (mul_nonneg (by linarith [hσ.1]) (sub_nonneg.mpr hσ.2)) hd.le
  · apply sub_nonneg.mp
    rw [huxley_uniform_sub_rational hσ.1]
    exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hσ.2) (by linarith [hσ.1]))
      (by linarith [hσ.1])) (by positivity)

/-- Every interior abscissa in Huxley's range gives a strict improvement. -/
theorem huxley_rational_exponent_lt {σ : ℝ} (hσ : σ∈Ioo (3/4:ℝ) 1) :
    huxleyRationalExponent σ<huxleyExponent σ := by
  have hd := rational_denominator_pos hσ.1.le
  apply sub_pos.mp
  rw [huxley_uniform_sub_rational hσ.1.le]
  exact div_pos (mul_pos (mul_pos (sub_pos.mpr hσ.2) (by linarith [hσ.1])) (by linarith [hσ.1])) (by positivity)

/-- Ingham's density exponent up to three quarters and Huxley's rational
exponent from three quarters to one. -/
def inghamHuxleyExponent (σ : ℝ) :=
  if 3/4≤σ then huxleyRationalExponent σ else inghamExponent σ

/-- The combined exponent is nonnegative and is always bounded by the
classical uniform Huxley exponent on the right half of the critical strip. -/
theorem ingham_huxley_exponent_bounds {σ : ℝ} (hσ : σ∈Icc (1/2:ℝ) 1) :
    0 ≤ inghamHuxleyExponent σ ∧ inghamHuxleyExponent σ≤huxleyExponent σ := by
  unfold inghamHuxleyExponent
  split_ifs with hs
  · exact huxley_rational_exponent_bounds ⟨hs,hσ.2⟩
  · unfold inghamExponent huxleyExponent
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hσ.2)) (by linarith [hσ.2])
    · apply (div_le_iff₀ (by linarith [hσ.2])).mpr
      nlinarith only [mul_nonneg (sub_nonneg.mpr hσ.2) (sub_nonneg.mpr (le_of_not_ge hs))]

end AnalyticNumberTheory.PrimeDistribution
