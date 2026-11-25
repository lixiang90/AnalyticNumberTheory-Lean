import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Cutoff conditions in Huxley's zero-density method

The four large-value terms depend only on two cutoff exponents and one
target exponent. These lemmas retain the floor in the mollifier length.
-/

noncomputable section
open Real Set
namespace AnalyticNumberTheory.PrimeDistribution

/-- Conditions on the mollifier power `a`, smoothing power `b`, and
density power `p` in the two alternatives of Huxley's detector. -/
structure HuxleyCutoffConditions (σ a b p : ℝ) : Prop where
  half_le_mollifier : 1/2≤a
  mollifier_le_one : a≤1
  one_le_cutoff : 1≤b
  cutoff_le_three_halves : b≤3/2
  diagonal : b*(2*(1-σ))=p
  large_values : 1+a*(4-6*σ)≤p
  integral_four_thirds : 1/3+a*(2/3)+b*(1/2-σ)*(4/3)≤p
  integral_twelve_fifths : 1+a*(2/5)+b*(1/2-σ)*(12/5)≤p

/-- Rounding down the mollifier length loses at most a factor two at the lower endpoint. -/
theorem huxley_cutoff_range_of_conditions {T σ a b p : ℝ} (hT : 1≤T) (hc : HuxleyCutoffConditions σ a b p) :
    let P := T^a
    let X := ⌊P⌋₊
    1 ≤ X ∧ P/2≤(X:ℝ) ∧ (X:ℝ)≤P ∧ P≤T ∧
      T≤T^b ∧ T^b≤T^(3/2:ℝ) := by
  have ha := hc.half_le_mollifier
  have hb := hc.mollifier_le_one
  let P := T^a
  have hp : 1≤P := Real.one_le_rpow hT (by linarith)
  have hX : 1≤⌊P⌋₊ := (Nat.one_le_floor_iff _).mpr hp
  have hf : (1:ℝ)≤⌊P⌋₊ := by exact_mod_cast hX
  exact ⟨hX,by change P/2≤(⌊P⌋₊:ℝ); linarith [Nat.lt_floor_add_one P],
    Nat.floor_le (by linarith : 0≤P), (Real.rpow_le_rpow_of_exponent_le hT hb).trans_eq (Real.rpow_one _),
    by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hc.one_le_cutoff,
    Real.rpow_le_rpow_of_exponent_le hT hc.cutoff_le_three_halves⟩

/-- Both polynomial terms and both integral terms are bounded, uniformly
including the integer parts of the cutoffs. -/
theorem huxley_balance_cutoffs_of_conditions {T σ a b p : ℝ} (hT : 1≤T) (hσ : σ∈Icc (3/4:ℝ) 1)
    (hc : HuxleyCutoffConditions σ a b p) :
    let X := (⌊T^a⌋₊:ℝ)
    let Y := T^b
    let Z := T^p
    (⌊Y⌋₊:ℝ)^(2*(1-σ)) + T*X^(4-6*σ) ≤ 5*Z ∧
      T^(1/3:ℝ)*X^(2/3:ℝ)*(Y^(1/2-σ))^(4/3:ℝ) +
      T*X^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ) ≤ 2*Z := by
  let P := T^a
  let X := (⌊P⌋₊:ℝ)
  let Y := T^b
  let Z := T^p
  have hT0 : 0<T := by linarith
  have hP0 : 0<P := Real.rpow_pos_of_pos hT0 _
  have hY0 : 0<Y := Real.rpow_pos_of_pos hT0 _
  obtain ⟨hX,hXlow,hXP,_,_,_⟩ := huxley_cutoff_range_of_conditions hT hc
  change P/2≤X at hXlow
  change X≤P at hXP
  have hXr : 0≤X := Nat.cast_nonneg _
  have hfirst := hc.diagonal
  have hsec := hc.large_values
  have hthird := hc.integral_four_thirds
  have hfour := hc.integral_twelve_fifths
  have hu : (⌊Y⌋₊:ℝ)^(2*(1-σ))≤Z := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY0.le) (by linarith [hσ.2] : 0≤2*(1-σ))).trans_eq
    dsimp only [Y,Z]; rw [←Real.rpow_mul hT0.le,hfirst]
  have hxp : X^(4-6*σ) ≤ 4*P^(4-6*σ) := by
    apply (Real.rpow_le_rpow_of_nonpos (by positivity) hXlow (by linarith [hσ.1] : 4-6*σ≤0)).trans
    rw [Real.div_rpow hP0.le (by norm_num),div_eq_mul_inv,←Real.rpow_neg (by norm_num : 0≤(2:ℝ))]
    have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by linarith [hσ.2] : -(4-6*σ)≤2)
    rw [Real.rpow_two] at h2
    calc _ ≤ P^(4-6*σ)*2^2 := by gcongr
         _ = _ := by ring
  have hv : T*P^(4-6*σ) ≤ Z := by
    dsimp only [P,Z]
    rw [←Real.rpow_mul hT0.le]
    calc
      _ = T^(1+a*(4-6*σ)) := by rw [Real.rpow_add hT0,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT hsec
  have hterm {d e k : ℝ} (he : 0≤e)
      (h : d+a*e+b*(1/2-σ)*k ≤ p) :
      T^d*X^e*(Y^(1/2-σ))^k ≤ Z := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hXr hXP he) (Real.rpow_nonneg hT0.le d))
      (Real.rpow_nonneg (Real.rpow_nonneg hY0.le _) _)).trans
    dsimp only [Y,P,Z]
    rw [←Real.rpow_mul hT0.le,←Real.rpow_mul hT0.le,←Real.rpow_mul hT0.le,
      ←Real.rpow_add hT0,←Real.rpow_add hT0]
    exact Real.rpow_le_rpow_of_exponent_le hT h
  constructor
  · change _+T*X^(4-6*σ) ≤ 5*Z
    linarith only [hu, mul_le_mul_of_nonneg_left hxp hT0.le,hv]
  · have h₃ := hterm (by norm_num) hthird
    have h₄ := hterm (by norm_num) hfour
    rw [Real.rpow_one] at h₄
    change _+T*X^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ) ≤ 2*Z
    linarith only [h₃,h₄]

end AnalyticNumberTheory.PrimeDistribution
