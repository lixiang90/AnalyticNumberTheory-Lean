import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The optimal cutoff in Ingham's zero-density argument

The finite detector and the critical-line integral have different exponents.
Their bounds coincide at `Y = X^(3/(4−2σ))`.
-/
noncomputable section
open Real Set
namespace AnalyticNumberTheory.PrimeDistribution

/-- Ingham's density exponent on the right half of the critical strip. -/
def inghamExponent (σ : ℝ) := 3*(1-σ)/(2-σ)

/-- The cutoff balancing the two parts of the zero detector. -/
def inghamCutoff (X σ : ℝ) := X^(3/(4-2*σ))

theorem inghamCutoff_range {X σ : ℝ} (hX : 1 ≤ X) (hσ : σ ∈ Icc (1/2:ℝ) 1) :
    X ≤ inghamCutoff X σ ∧ inghamCutoff X σ ≤ X^(3/2:ℝ) := by
  have hd : 0 < 4-2*σ := by linarith [hσ.2]
  unfold inghamCutoff
  refine ⟨?_, Real.rpow_le_rpow_of_exponent_le hX ((div_le_iff₀ hd).mpr (by linarith [hσ.2]))⟩
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
    ((le_div_iff₀ hd).mpr (by linarith [hσ.1]) : 1 ≤ 3/(4-2*σ))

theorem inghamCutoff_balance {X σ : ℝ} (hX : 0 < X) (hσ : σ ≤ 1) :
    (inghamCutoff X σ)^(2*(1-σ)) = X^(inghamExponent σ) ∧
    X^3*(inghamCutoff X σ)^(2-4*σ) = (X^(inghamExponent σ))^3 := by
  have hd : 4-2*σ≠0 := by linarith
  have he : 2-σ≠0 := by linarith
  unfold inghamCutoff inghamExponent
  constructor
  · rw [←Real.rpow_mul hX.le]; congr 1; field_simp; ring
  · rw [←Real.rpow_mul_natCast hX.le,←Real.rpow_mul hX.le,←Real.rpow_natCast,←Real.rpow_add hX]
    congr 1; push_cast; field_simp; ring

/-- Below the detector's separation from the critical line, the crude zero
count loses only a constant relative to the balanced power. -/
theorem ingham_near_half {X σ : ℝ} (hX : 1 < X) (hσ : σ ∈ Icc (1/2:ℝ) 1)
    (hnear : σ-1/2 ≤ (Real.log X)⁻¹) : X ≤ Real.exp 2 * X^(inghamExponent σ) := by
  have hlog := Real.log_pos hX
  have he : 0 < 2-σ := by linarith [hσ.2]
  have hc : (σ-1/2)*Real.log X ≤ 1 := by
    simpa only [inv_mul_cancel₀ hlog.ne'] using mul_le_mul_of_nonneg_right hnear hlog.le
  have hd : 1-inghamExponent σ = (2*σ-1)/(2-σ) := by unfold inghamExponent; field_simp; ring
  have hl : Real.log X*(1-inghamExponent σ) ≤ 2 := by
    rw [hd,mul_div_assoc',div_le_iff₀ he]
    nlinarith only [hc,hσ.2]
  calc
    X = X^(1-inghamExponent σ)*X^(inghamExponent σ) := by rw [← Real.rpow_add (by linarith),sub_add_cancel,Real.rpow_one]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Real.rpow_def_of_pos (by linarith)]
      exact Real.exp_le_exp.mpr hl



/-- Convert the cubic large-values estimate at the balanced cutoff into the
same power of the height as the finite-polynomial estimate. -/
theorem ingham_balanced_cubic {X σ R A D K : ℝ} (hX : 1 ≤ X) (hσ : σ ≤ 1)
    (hR : 0 ≤ R) (hA : 0 < A) (hD : 0 < D) (hK : 0 ≤ K)
    (hc : R^3*(1/(8*(A*(1+Real.log X)*(inghamCutoff X σ)^(1/2-σ))))^4 ≤
      D*(K*(1+Real.log X))^3*X^3*(1+Real.log X)^6) :
    R ≤ (1+D*K^3*(8*A)^4)*(1+Real.log X)^5*X^(inghamExponent σ) := by
  let L := 1+Real.log X
  let Y := inghamCutoff X σ
  let Z := X^(inghamExponent σ)
  let B := D*K^3*(8*A)^4
  have hX0 : 0<X := by linarith
  have hY0 : 0<Y := Real.rpow_pos_of_pos hX0 _
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hZ : 0 ≤ Z := Real.rpow_nonneg hX0.le _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsave : X^3*Y^(2-4*σ) = Z^3 := (inghamCutoff_balance hX0 hσ).2
  have hden : 0 < 8*(A*L*Y^(1/2-σ)) := by positivity
  change R^3*(1/(8*(A*L*Y^(1/2-σ))))^4 ≤ D*(K*L)^3*X^3*L^6 at hc
  rw [div_pow,one_pow,←div_eq_mul_one_div,div_le_iff₀ (pow_pos hden 4)] at hc
  have he : (Y^(1/2-σ))^4 = Y^(2-4*σ) := by
    rw [←Real.rpow_mul_natCast hY0.le]; congr 1; push_cast; ring
  have hb : R^3 ≤ B*L^13*Z^3 := by
    apply hc.trans_eq
    rw [←hsave]
    dsimp only [B]
    rw [show (8*(A*L*Y^(1/2-σ)))^4 = (8*A)^4*L^4*(Y^(1/2-σ))^4 by ring,he]
    ring
  have hpow : B ≤ (1+B)^3 := by nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg B)]
  change R ≤ (1+B)*L^5*Z
  apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (by positivity)
  apply hb.trans
  calc
    _ ≤ (1+B)^3*L^15*Z^3 := by gcongr <;> first | exact hpow | exact hL | norm_num
    _ = _ := by change _ = ((1+B)*L^5*Z)^3; ring

end AnalyticNumberTheory.PrimeDistribution
