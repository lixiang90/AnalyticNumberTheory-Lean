import AnalyticNumberTheory.SieveMethods.SelbergSmallPrimeComparison
import AnalyticNumberTheory.AnalyticTools.HarmonicRemainder
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The local factors at two and three in the Selberg denominator

The harmonic sums on integers coprime to six can be written as a short
inclusion-exclusion sum. Keeping both local factors gives a lower estimate
whose constant term is explicit.
-/

open Finset Real
namespace AnalyticNumberTheory.SieveMethods

private theorem reciprocal_multiples (M d : ℕ) (hd : 0 < d) :
    (∑ m ∈ (Icc 1 M).filter (fun n => d ∣ n), (m:ℝ)⁻¹) =
      (d:ℝ)⁻¹ * (harmonic (M/d):ℝ) := by
  have himage : (Icc 1 M).filter (fun n => d ∣ n) = (Icc 1 (M/d)).image (d*·) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hM, hdm⟩ := mem_filter.mp hm
      obtain ⟨l,rfl⟩ := hdm
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hM
      exact mem_image.mpr ⟨l,mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left h₁,
        (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using h₂)⟩,rfl⟩
    · intro hm
      obtain ⟨l,hl,rfl⟩ := mem_image.mp hm
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hl
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd h₁,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp h₂⟩,dvd_mul_right _ _⟩
  rw [himage,sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hd h),harmonic_eq_sum_Icc]
  push_cast
  rw [mul_sum]
  simp [mul_comm]

/-- Inclusion-exclusion for the harmonic sum coprime to six. -/
theorem coprimeHarmonicSum_six (M : ℕ) :
    coprimeHarmonicSum 6 M = (harmonic M:ℝ) - (harmonic (M/2):ℝ)/2 -
      (harmonic (M/3):ℝ)/3 + (harmonic (M/6):ℝ)/6 := by
  have h₆ (n : ℕ) : n.Coprime 6 ↔ ¬2 ∣ n ∧ ¬3 ∣ n := by
    rw [show (6:ℕ)=2*3 by decide, Nat.coprime_mul_iff_right]
    rw [@Nat.coprime_comm n 2,@Nat.coprime_comm n 3,Nat.prime_two.coprime_iff_not_dvd,
      Nat.prime_three.coprime_iff_not_dvd]
  have hM : coprimeHarmonicSum 6 M =
      (∑n ∈ Icc 1 M,(n:ℝ)⁻¹) -
      (∑n ∈ (Icc 1 M).filter (fun n => 2∣n),(n:ℝ)⁻¹) -
      (∑n ∈ (Icc 1 M).filter (fun n => 3∣n),(n:ℝ)⁻¹) +
      (∑n ∈ (Icc 1 M).filter (fun n => 6∣n),(n:ℝ)⁻¹) := by
    simp only [coprimeHarmonicSum,sum_filter,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl; intro n _
    have hd : 6∣n ↔ 2∣n ∧ 3∣n := by
      exact ⟨fun h => ⟨(by decide : 2∣6).trans h,(by decide : 3∣6).trans h⟩,
        fun h => (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    by_cases h₂ : 2∣n <;> by_cases h₃ : 3∣n <;> simp [h₆,hd,h₂,h₃]
  rw [hM, reciprocal_multiples _ 2 (by decide),reciprocal_multiples _ 3 (by decide),
    reciprocal_multiples _ 6 (by decide)]
  have he : (harmonic M:ℝ) = ∑n ∈ Icc 1 M,(n:ℝ)⁻¹ := by rw [harmonic_eq_sum_Icc];push_cast;rfl
  rw [he];push_cast;ring

private theorem six_divisors : (6:ℕ).divisors={1,2,3,6} := by decide

/-- A finite harmonic comparison retaining the Euler factors at two and three. -/
theorem selbergDenominator_ge_six_harmonics (n : ℕ) :
    (harmonic n:ℝ)+(harmonic (n/2):ℝ)/2+(harmonic (n/3):ℝ)/6-
      (harmonic (n/4):ℝ)/2+(harmonic (n/6):ℝ)/12-(harmonic (n/9):ℝ)/6-
      (harmonic (n/12):ℝ)/12-(harmonic (n/18):ℝ)/12+(harmonic (n/36):ℝ)/12 ≤
        selbergDenominator n := by
  have hs : Squarefree 6 := (Nat.squarefree_mul (show Nat.Coprime 2 3 by decide)).mpr
    ⟨Nat.prime_two.squarefree,Nat.prime_three.squarefree⟩
  have h := selbergDenominator_ge_small_prime_model 6 n hs
  rw [six_divisors] at h
  simp (disch := decide) only [sum_insert,sum_singleton] at h
  norm_num [coprimeHarmonicSum_six, Nat.div_div_eq_div_mul, show Nat.totient 3 = 2 by decide,
    show Nat.totient 6 = 2 by decide] at h
  linarith

private theorem harmonic_scaled_bounds {x : ℝ} (hx : 0<x) (j : ℕ) (hj : 0<j) :
    let H := (harmonic (⌊x⌋₊/j):ℝ)
    (log x-log j+eulerMascheroniConstant - j/x ≤ H) ∧
    (H ≤ log x-log j+eulerMascheroniConstant + j/x) := by
  have hj' : (0:ℝ)<j := by exact_mod_cast hj
  have h := AnalyticTools.harmonic_floor_remainder (div_pos hx hj')
  rw [Nat.floor_div_natCast,Real.log_div hx.ne' hj'.ne',one_div_div,abs_le] at h
  constructor <;> linarith [h.1,h.2]

/-- Keeping the local factors at 2 and 3 gives an effective logarithmic lower bound. -/
theorem selbergDenominator_ge_two_prime_log {x : ℝ} (hx : 0<x) :
    log x+eulerMascheroniConstant+log 2/2+log 3/6-12/x ≤ selbergDenominator x := by
  have HM := selbergDenominator_ge_six_harmonics ⌊x⌋₊
  have he : selbergDenominator (⌊x⌋₊:ℕ) = selbergDenominator x := by
    simp [selbergDenominator]
  rw [he] at HM
  have h1 := harmonic_scaled_bounds hx 1 (by decide)
  have h2 := harmonic_scaled_bounds hx 2 (by decide)
  have h3 := harmonic_scaled_bounds hx 3 (by decide)
  have h4 := harmonic_scaled_bounds hx 4 (by decide)
  have h6 := harmonic_scaled_bounds hx 6 (by decide)
  have h9 := harmonic_scaled_bounds hx 9 (by decide)
  have h12 := harmonic_scaled_bounds hx 12 (by decide)
  have h18 := harmonic_scaled_bounds hx 18 (by decide)
  have h36 := harmonic_scaled_bounds hx 36 (by decide)
  dsimp only at h1 h2 h3 h4 h6 h9 h12 h18 h36
  simp only [Nat.div_one,Nat.cast_one,Real.log_one,Nat.cast_ofNat] at *
  have l4 : log 4=log 2+log 2 := by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
  have l6 : log 6=log 2+log 3 := by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
  have l9 : log 9=log 3+log 3 := by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
  have l12 : log 12=log 4+log 3 := by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
  have l18 : log 18=log 2+log 9 := by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
  have l36 : log 36=log 4+log 9 := by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
  simp only [l36,l18,l12,l4,l6,l9] at h4 h6 h9 h12 h18 h36
  linear_combination (norm := ring_nf) HM+h1.1+h2.1/2+h3.1/6+h4.2/2+h6.1/12+
    h9.2/6+h12.2/12+h18.2/12+h36.1/12
  norm_num

end AnalyticNumberTheory.SieveMethods
