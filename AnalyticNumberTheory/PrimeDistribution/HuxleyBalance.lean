import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

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

/-- Rounding down the mollifier length loses at most a factor two at the lower endpoint. -/
theorem huxley_cutoff_range {T σ : ℝ} (hT : 1≤T) (hσ : σ∈Icc (3/4:ℝ) 1) :
    let P := T^(huxleyMollifierExponent σ)
    let X := ⌊P⌋₊
    1 ≤ X ∧ P/2≤(X:ℝ) ∧ (X:ℝ)≤P ∧ P≤T ∧
      T≤T^(6/5:ℝ) ∧ T^(6/5:ℝ)≤T^(3/2:ℝ) := by
  obtain ⟨ha,hb,_⟩ := huxley_balance_exponents hσ
  let P := T^(huxleyMollifierExponent σ)
  have hp : 1≤P := Real.one_le_rpow hT (by linarith)
  have hX : 1≤⌊P⌋₊ := (Nat.one_le_floor_iff _).mpr hp
  have hf : (1:ℝ)≤⌊P⌋₊ := by exact_mod_cast hX
  exact ⟨hX,by change P/2≤(⌊P⌋₊:ℝ); linarith [Nat.lt_floor_add_one P],
    Nat.floor_le (by linarith : 0≤P), (Real.rpow_le_rpow_of_exponent_le hT hb).trans_eq (Real.rpow_one _),
    by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1:ℝ)≤6/5),
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)⟩

/-- Both polynomial terms and both integral terms are bounded, uniformly
including the integer parts of the cutoffs. -/
theorem huxley_balance_cutoffs {T σ : ℝ} (hT : 1≤T) (hσ : σ∈Icc (3/4:ℝ) 1) :
    let X := (⌊T^(huxleyMollifierExponent σ)⌋₊:ℝ)
    let Y := T^(6/5:ℝ)
    let Z := T^(huxleyExponent σ)
    (⌊Y⌋₊:ℝ)^(2*(1-σ)) + T*X^(4-6*σ) ≤ 5*Z ∧
      T^(1/3:ℝ)*X^(2/3:ℝ)*(Y^(1/2-σ))^(4/3:ℝ) +
      T*X^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ) ≤ 2*Z := by
  let a := huxleyMollifierExponent σ
  let P := T^a
  let X := (⌊P⌋₊:ℝ)
  let Y := T^(6/5:ℝ)
  let Z := T^(huxleyExponent σ)
  have hT0 : 0<T := by linarith
  have hP0 : 0<P := Real.rpow_pos_of_pos hT0 _
  have hY0 : 0<Y := Real.rpow_pos_of_pos hT0 _
  obtain ⟨hX,hXlow,hXP,_,_,_⟩ := huxley_cutoff_range hT hσ
  change P/2≤X at hXlow
  change X≤P at hXP
  have hXr : 0≤X := Nat.cast_nonneg _
  obtain ⟨_,_,hfirst,hsec,hthird,hfour⟩ := huxley_balance_exponents hσ
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
  have hterm {d e k : ℝ} (hd : 0≤d) (he : 0≤e) (hk : 0≤k)
      (h : d+a*e+(6/5)*(1/2-σ)*k ≤ huxleyExponent σ) :
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
  · have h₃ := hterm (by norm_num : (0:ℝ)≤1/3) (by norm_num) (by norm_num) hthird
    have h₄ := hterm (by norm_num : (0:ℝ)≤1) (by norm_num) (by norm_num) hfour
    rw [Real.rpow_one] at h₄
    change _+T*X^(2/5:ℝ)*(Y^(1/2-σ))^(12/5:ℝ) ≤ 2*Z
    linarith only [h₃,h₄]

end AnalyticNumberTheory.PrimeDistribution
