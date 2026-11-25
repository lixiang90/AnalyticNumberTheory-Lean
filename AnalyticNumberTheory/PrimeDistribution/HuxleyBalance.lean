import AnalyticNumberTheory.PrimeDistribution.HuxleyCutoffConditions

/-!
# A choice of cutoffs for Huxley's density estimate

On the strip from three quarters to one, a fixed smoothing length `T^(6/5)`
and a mollifier of length `T^(1/2 + 6(1−σ)/5)` control all four large-value
terms by the same target power.
-/
noncomputable section
open Real Set
namespace AnalyticNumberTheory.PrimeDistribution

def huxleyMollifierExponent (σ : ℝ) := 1/2+(6/5)*(1-σ)
def huxleyExponent (σ : ℝ) := (12/5)*(1-σ)

/-- All powers which arise in the two detector alternatives. -/
theorem huxley_balance_exponents {σ : ℝ} (hσ : σ∈Icc (3/4:ℝ) 1) :
    let a := huxleyMollifierExponent σ
    let p := huxleyExponent σ
    1/2≤a ∧ a≤1 ∧ (6/5)*(2*(1-σ))=p ∧ 1+a*(4-6*σ)≤p ∧
      1/3+a*(2/3)+(6/5)*(1/2-σ)*(4/3)≤p ∧
      1+a*(2/5)+(6/5)*(1/2-σ)*(12/5)≤p := by
  dsimp [huxleyMollifierExponent,huxleyExponent]
  constructor; · linarith [hσ.2]
  constructor; · linarith [hσ.1]
  constructor; · ring
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hσ.2) (sub_nonneg.mpr hσ.1)]
  constructor <;> linarith [hσ.1,hσ.2]

/-- The linear uniform choice satisfies the general four-term cutoff conditions. -/
theorem huxley_uniform_cutoff_conditions {σ : ℝ} (hσ : σ∈Icc (3/4:ℝ) 1) :
    HuxleyCutoffConditions σ (huxleyMollifierExponent σ) (6/5) (huxleyExponent σ) := by
  obtain ⟨ha,hb,h₁,h₂,h₃,h₄⟩ := huxley_balance_exponents hσ
  exact ⟨ha,hb,by norm_num,by norm_num,h₁,h₂,h₃,h₄⟩

/-- Rounding down the mollifier length loses at most a factor two at the lower endpoint. -/
theorem huxley_cutoff_range {T σ : ℝ} (hT : 1≤T) (hσ : σ∈Icc (3/4:ℝ) 1) :
    let P := T^(huxleyMollifierExponent σ)
    let X := ⌊P⌋₊
    1 ≤ X ∧ P/2≤(X:ℝ) ∧ (X:ℝ)≤P ∧ P≤T ∧
      T≤T^(6/5:ℝ) ∧ T^(6/5:ℝ)≤T^(3/2:ℝ) :=
  huxley_cutoff_range_of_conditions hT (huxley_uniform_cutoff_conditions hσ)

/-- Both polynomial terms and both integral terms are bounded, uniformly
including the integer parts of the cutoffs. -/
theorem huxley_balance_cutoffs {T σ : ℝ} (hT : 1≤T) (hσ : σ∈Icc (3/4:ℝ) 1) :
    let X := (⌊T^(huxleyMollifierExponent σ)⌋₊:ℝ)
    let Y := T^(6/5:ℝ)
    let Z := T^(huxleyExponent σ)
    (⌊Y⌋₊:ℝ)^(2*(1-σ)) + T*X^(4-6*σ) ≤ 5*Z ∧
      T^(1/3:ℝ)*X^(2/3:ℝ)*(Y^(1/2-σ))^(4/3:ℝ) +
      T*X^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ) ≤ 2*Z :=
  huxley_balance_cutoffs_of_conditions hT hσ (huxley_uniform_cutoff_conditions hσ)

end AnalyticNumberTheory.PrimeDistribution
