import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Ordinary and logarithmic averages of divisor convolutions

A divisor convolution with the constant-one function has a Cesàro mean
whenever its coefficients divided by the divisor are absolutely summable.
For a logarithmically weighted sum the first logarithmic moment gives the
constant term after the leading logarithm is subtracted.
-/

open Filter Real Finset
open scoped Topology
namespace AnalyticNumberTheory.DirichletSeries

/-- Real interpolation of the constant term in the harmonic sum. -/
theorem tendsto_harmonic_floor_sub_log :
    Tendsto (fun x : ℝ => (harmonic ⌊x⌋₊:ℝ)-log x) atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := Real.tendsto_harmonic_sub_log.comp (tendsto_nat_floor_atTop (α:=ℝ))
  have h' := (Real.continuousAt_log (x:=1) one_ne_zero).tendsto.comp (tendsto_nat_floor_div_atTop (R:=ℝ))
  rw [Real.log_one] at h'
  rw [← add_zero Real.eulerMascheroniConstant]
  apply (h.add h').congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hfloor : (0:ℝ)<⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
  change (harmonic ⌊x⌋₊:ℝ)-log ⌊x⌋₊+log ((⌊x⌋₊:ℝ)/x)=_
  rw [Real.log_div hfloor.ne' (by linarith)]; ring

private theorem tsum_floor_eq_sum {h : ℕ→ℝ} (N : ℕ) :
    ∑' d : ℕ, h d*(↑(N/d):ℝ)=∑ d∈Icc 1 N,h d*(↑(N/d):ℝ) := by
  apply tsum_eq_sum
  intro d hd
  by_cases hz : d=0
  · simp [hz]
  · rw [Nat.div_eq_of_lt (by simp only [mem_Icc,not_and_or,not_le] at hd; omega : N<d)]
    simp

/-- Mean of a divisor convolution in the order obtained by summing over divisors first. -/
theorem tendsto_divisor_weighted_count {h : ℕ → ℝ} (H : Summable fun d : ℕ => |h d|/(d:ℝ)) :
    Tendsto (fun N : ℕ => (∑ d∈Icc 1 N,h d*(↑(N/d):ℝ))/(N:ℝ)) atTop (𝓝 (∑' d : ℕ,h d/(d:ℝ))) := by
  have hf (d : ℕ) : Tendsto (fun N : ℕ => h d*((↑(N/d):ℝ)/(N:ℝ))) atTop (𝓝 (h d/d)) := by
    by_cases hd : d=0
    · simp [hd]
    have hd0 : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hu : Tendsto (fun N : ℕ => (N:ℝ)/d) atTop atTop := tendsto_natCast_atTop_atTop.atTop_div_const hd0
    have hfloor := (tendsto_nat_floor_div_atTop (R:=ℝ)).comp hu
    have hh := hfloor.const_mul (h d/(d:ℝ))
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    change (h d/d)*((⌊(N:ℝ)/d⌋₊:ℝ)/((N:ℝ)/d))=_
    rw [Nat.floor_div_natCast,Nat.floor_natCast]; field_simp
  have hb : ∀ᶠ N : ℕ in atTop, ∀ d, ‖h d*((↑(N/d):ℝ)/(N:ℝ))‖≤|h d|/(d:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN d
    by_cases hd : d=0
    · simp [hd]
    have hd0 : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤(↑(N/d):ℝ)/N)]
    have hx : (↑(N/d):ℝ)*d≤N := by exact_mod_cast Nat.div_mul_le_self N d
    calc
      _ ≤ |h d| *(d:ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [div_le_iff₀ hN0,← div_eq_inv_mul,le_div_iff₀ hd0]; exact hx
      _ = _ := (div_eq_mul_inv ..).symm
  have hh := tendsto_tsum_of_dominated_convergence H hf hb
  apply hh.congr'
  exact .of_forall fun N => by
    change (∑' d : ℕ,h d*((↑(N/d):ℝ)/(N:ℝ)))=_
    simp_rw [← mul_div_assoc]
    rw [tsum_div_const,tsum_floor_eq_sum]

/-- Constant term in the logarithmic divisor average, assuming an absolute first log moment. -/
theorem tendsto_divisor_harmonic_centered {h : ℕ→ℝ} (h₀ : h 0=0)
    (H : Summable fun d : ℕ => |h d| *(1+log d)) :
    Tendsto (fun N : ℕ => ∑' d : ℕ, h d*((harmonic (N/d):ℝ)-log N)) atTop
      (𝓝 (∑' d : ℕ,h d*(Real.eulerMascheroniConstant-log d))) := by
  apply tendsto_tsum_of_dominated_convergence H
  · intro d
    by_cases hd : d=0
    · simp [hd,h₀]
    have hd0 : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hu : Tendsto (fun N : ℕ => (N:ℝ)/d) atTop atTop := tendsto_natCast_atTop_atTop.atTop_div_const hd0
    have hh := ((tendsto_harmonic_floor_sub_log.comp hu).sub_const (log d)).const_mul (h d)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    change h d*((harmonic ⌊(N:ℝ)/d⌋₊:ℝ)-log ((N:ℝ)/d)-log d)=_
    rw [Nat.floor_div_natCast,Nat.floor_natCast,Real.log_div (by exact_mod_cast (by omega : N≠0)) hd0.ne']; ring
  · filter_upwards [eventually_ge_atTop 1] with N hN d
    by_cases hd : d=0
    · simp [hd,h₀]
    have hd0 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
    have hN0 : (1:ℝ)≤N := by exact_mod_cast hN
    rw [Real.norm_eq_abs,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    by_cases h : d≤N
    · have hx : 1≤(N:ℝ)/d := (one_le_div (by linarith)).mpr (by exact_mod_cast h)
      have h₁ := log_le_harmonic_floor ((N:ℝ)/d) (by linarith : 0≤(N:ℝ)/d)
      have h₂ := harmonic_floor_le_one_add_log _ hx
      rw [Nat.floor_div_natCast,Nat.floor_natCast,Real.log_div (by linarith) (by linarith)] at h₁ h₂
      exact abs_le.mpr ⟨by linarith,by linarith [log_nonneg hd0]⟩
    · have hlog := Real.log_le_log (by linarith : (0:ℝ)<N) (show (N:ℝ)≤d by exact_mod_cast (by omega : N≤d))
      rw [Nat.div_eq_of_lt (by omega : N<d)]
      simp only [harmonic_zero,Rat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (log_nonneg hN0)]
      linarith

open scoped LSeries.notation

/-- Rearrange the ordinary summatory function of a divisor sum. -/
theorem sum_divisor_sum_eq_weighted_floor (h : ℕ → ℝ) (N : ℕ) :
    (∑ n∈Icc 1 N, ∑ d∈n.divisors,h d)=∑ d∈Icc 1 N,h d*(↑(N/d):ℝ) := by
  have hh := DivisorProblems.sum_Icc_convolution_eq_sum_sum_div h (fun _ => (1:ℝ)) N
  simp only [LSeries.convolution_def,mul_one] at hh
  simp_rw [Nat.sum_divisorsAntidiagonal (fun i _ : ℕ => h i)] at hh
  simpa using hh

/-- Rearrange a logarithmically weighted divisor sum as a harmonic kernel. -/
theorem sum_divisor_sum_div_eq_tsum_harmonic (h : ℕ → ℝ) (N : ℕ) :
    (∑ n∈Icc 1 N, (∑ d∈n.divisors,h d)/(n:ℝ))=∑' d : ℕ,(h d/d)*(harmonic (N/d):ℝ) := by
  let f (n : ℕ) := h n/(n:ℝ)
  let g (n : ℕ) := (n:ℝ)⁻¹
  have conv (n : ℕ) : (f ⍟ g) n=(∑d∈n.divisors,h d)/(n:ℝ) := by
    rw [LSeries.convolution_def,← Nat.sum_divisorsAntidiagonal (fun i _ : ℕ => h i),Finset.sum_div]
    apply sum_congr rfl
    intro p hp
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1,Nat.cast_mul]
    simp [f,g,div_eq_mul_inv]; ring
  have hsum := DivisorProblems.sum_Icc_convolution_eq_sum_sum_div f g N
  simp_rw [conv] at hsum
  have harm (m : ℕ) : ∑ i∈Icc 1 m,g i=(harmonic m:ℝ) := by
    simp [g,harmonic_eq_sum_Icc]
  simp_rw [harm] at hsum
  rw [hsum]
  symm
  apply tsum_eq_sum
  intro d hd
  by_cases hz : d=0
  · simp [hz]
  rw [Nat.div_eq_of_lt (by simp only [mem_Icc,not_and_or,not_le] at hd; omega : N<d)]
  simp

end AnalyticNumberTheory.DirichletSeries
