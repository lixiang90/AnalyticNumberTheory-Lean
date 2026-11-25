import AnalyticNumberTheory.DirichletSeries.EulerProductConvergence
import AnalyticNumberTheory.DirichletSeries.DivisorConvolutionMeans
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.PSeries

/-!
# Multiplicative coefficients of the one-dimensional Selberg weights

The choices c = 0 and c = 1 give the denominator and the absolute-weight mass
of the Selberg sieve. Their Möbius transforms vanish on cubes of primes.
-/

open ArithmeticFunction Nat Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
namespace AnalyticNumberTheory.SieveMethods

/-- On squarefree integers take the product of (p+c)/(p−1); on other integers take zero. -/
noncomputable def selbergWeightCoefficient (c : ℝ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).ppow 2).pmul (prodPrimeFactors fun p => ((p:ℝ)+c)/(p-1))

/-- Möbius transform used to compute the ordinary and logarithmic means of the sieve weights. -/
noncomputable def selbergMeanCoefficient (c : ℝ) : ArithmeticFunction ℝ :=
  selbergWeightCoefficient c * (μ : ArithmeticFunction ℝ)

theorem selbergWeightCoefficient_multiplicative (c : ℝ) : (selbergWeightCoefficient c).IsMultiplicative :=
  isMultiplicative_moebius.intCast.ppow.pmul (IsMultiplicative.prodPrimeFactors _)

theorem selbergMeanCoefficient_multiplicative (c : ℝ) : (selbergMeanCoefficient c).IsMultiplicative :=
  (selbergWeightCoefficient_multiplicative c).mul isMultiplicative_moebius.intCast

theorem sum_selbergMeanCoefficient_divisors (c : ℝ) (n : ℕ) :
    ∑ d∈n.divisors, selbergMeanCoefficient c d = selbergWeightCoefficient c n := by
  rw [← coe_mul_zeta_apply,selbergMeanCoefficient,mul_assoc,coe_moebius_mul_coe_zeta,mul_one]

theorem selbergWeightCoefficient_prime (c : ℝ) {p : ℕ} (hp : p.Prime) :
    selbergWeightCoefficient c p=((p:ℝ)+c)/(p-1) := by
  simp [selbergWeightCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    moebius_apply_prime hp,prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

theorem selbergWeightCoefficient_prime_pow (c : ℝ) {p k : ℕ} (hp : p.Prime) (hk : 2≤k) :
    selbergWeightCoefficient c (p^k)=0 := by
  simp [selbergWeightCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    moebius_apply_prime_pow hp (by omega : k≠0),show k≠1 by omega]

theorem selbergMeanCoefficient_prime_power_step (c : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    selbergMeanCoefficient c (p^(k+1)) =
      selbergWeightCoefficient c (p^(k+1))-selbergWeightCoefficient c (p^k) := by
  have h := sum_selbergMeanCoefficient_divisors c (p^(k+1))
  have h' := sum_selbergMeanCoefficient_divisors c (p^k)
  rw [Nat.sum_divisors_prime_pow hp,Finset.sum_range_succ] at h
  rw [Nat.sum_divisors_prime_pow hp] at h'
  linarith

/-- The nonconstant coefficients of a local factor occur at p and p². -/
theorem selbergMeanCoefficient_local (c : ℝ) {p : ℕ} (hp : p.Prime) :
    selbergMeanCoefficient c p=(1+c)/(p-1) ∧
    selbergMeanCoefficient c (p^2)= -((p:ℝ)+c)/(p-1) ∧
    ∀ k : ℕ, 3≤k → selbergMeanCoefficient c (p^k)=0 := by
  have ha := selbergMeanCoefficient_prime_power_step c hp 0
  have hb := selbergMeanCoefficient_prime_power_step c hp 1
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  simp only [pow_zero,pow_one,Nat.zero_add,selbergWeightCoefficient_prime c hp,
    (selbergWeightCoefficient_multiplicative c).1] at ha
  simp only [pow_one,selbergWeightCoefficient_prime c hp,
    selbergWeightCoefficient_prime_pow c hp (le_refl 2)] at hb
  refine ⟨?_,by rw [hb]; ring,?_⟩
  · rw [ha]; field_simp; ring
  · rintro (_|k) hk
    · omega
    rw [selbergMeanCoefficient_prime_power_step c hp,
      selbergWeightCoefficient_prime_pow c hp (by omega),selbergWeightCoefficient_prime_pow c hp (by omega),sub_self]

/-- Absolute convergence at 3/4 controls the first logarithmic moment at 1. -/
theorem selbergMeanCoefficient_summable {c : ℝ} (hc : 0≤c) (hc' : c≤1) :
    Summable (fun n : ℕ => |selbergMeanCoefficient c n*(n:ℝ)^(-(3/4):ℝ)|) := by
  let f (n : ℕ) := selbergMeanCoefficient c n*(n:ℝ)^(-(3/4):ℝ)
  have h₁ : f 1=1 := by simp [f,(selbergMeanCoefficient_multiplicative c).1]
  apply DirichletSeries.summable_of_local_euler_bounds (f:=f) (by simp [f]) h₁
    (fun {_ _} h => by simp only [f,(selbergMeanCoefficient_multiplicative c).2 h,Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]; ring)
    (fun n => 7*(n:ℝ)^(-(3/2):ℝ)) (fun _ => by positivity)
    ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).mul_left 7)
  intro p hp
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hpp : (0:ℝ)<p := by positivity
  obtain ⟨ha,hb,hd⟩ := selbergMeanCoefficient_local c hp
  have hsup (j : ℕ) (hj : j∉range 3) : |f (p^j)|=0 := by
    simp only [mem_range,not_lt] at hj
    simp [f,hd j hj]
  refine ⟨(hasSum_sum_of_ne_finset_zero hsup).summable,?_⟩
  rw [tsum_eq_sum hsup,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
  simp only [pow_zero,h₁,abs_one,pow_one,sum_range_zero,zero_add]
  have h₁' : f p≤4*(p:ℝ)^(-(3/2):ℝ) := by
    dsimp [f]; rw [ha]
    calc
      _ ≤ (4*(p:ℝ)^(-1:ℝ))*(p:ℝ)^(-(3/4):ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Real.rpow_neg_one,← div_eq_mul_inv,div_le_div_iff₀ (by linarith) hpp]
        nlinarith [mul_le_mul_of_nonneg_right hc' hpp.le]
      _ = 4*(p:ℝ)^(-(7/4):ℝ) := by rw [mul_assoc,← Real.rpow_add hpp]; norm_num
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
  have h₂' : |f (p^2)|≤3*(p:ℝ)^(-(3/2):ℝ) := by
    dsimp [f]; rw [hb,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤((p^2:ℕ):ℝ)^(-(3/4):ℝ))]
    rw [neg_div,abs_neg,abs_of_nonneg (div_nonneg (by positivity) (by linarith)),Nat.cast_pow,
      ← Real.rpow_natCast (p:ℝ) 2,← Real.rpow_mul hpp.le]
    norm_num
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ (by linarith)]; linarith
  have hfp : 0≤f p := by dsimp [f]; rw [ha]; exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  rw [abs_of_nonneg hfp]; linarith

/-- The normalized coefficients have an absolutely summable first logarithmic moment. -/
theorem selbergMeanCoefficient_log_summable {c : ℝ} (hc : 0≤c) (hc' : c≤1) :
    Summable (fun n : ℕ => |selbergMeanCoefficient c n/(n:ℝ)| *(1+Real.log n)) := by
  have H := (selbergMeanCoefficient_summable hc hc').mul_left 5
  apply H.of_nonneg_of_le
  · intro n
    by_cases hn : n=0
    · simp [hn]
    have h : (1:ℝ)≤n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    exact mul_nonneg (abs_nonneg _) (by linarith [Real.log_nonneg h])
  · intro n
    by_cases hn : n=0
    · simp [hn]
    have h : (1:ℝ)≤n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hpos : (0:ℝ)<n := by linarith
    have hpow : 1≤(n:ℝ)^(1/4:ℝ) := Real.one_le_rpow h (by norm_num)
    have hh := Real.log_le_rpow_div hpos.le (by norm_num : (0:ℝ)<1/4)
    have hh' : 1+Real.log n≤5*(n:ℝ)^(1/4:ℝ) := by linarith
    simp only [abs_div,abs_of_pos hpos,abs_mul,abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    calc
      _ ≤ (|selbergMeanCoefficient c n|/n)*(5*(n:ℝ)^(1/4:ℝ)) := by gcongr
      _ = _ := by
        rw [div_eq_mul_inv,← Real.rpow_neg_one]
        have he : (n:ℝ)^(-1:ℝ)*(n:ℝ)^(1/4:ℝ)=(n:ℝ)^(-(3/4):ℝ) := by rw [← Real.rpow_add hpos]; norm_num
        rw [← he]; ring

/-- Absolute convergence of the normalized mass and of its logarithmic moment separately. -/
theorem selbergMeanCoefficient_moments {c : ℝ} (hc : 0≤c) (hc' : c≤1) :
    Summable (fun n : ℕ => |selbergMeanCoefficient c n/(n:ℝ)|) ∧
    Summable (fun n : ℕ => |selbergMeanCoefficient c n/(n:ℝ)*Real.log n|) := by
  have h (n : ℕ) : 0≤Real.log n := by
    by_cases hn : n=0
    · simp [hn]
    exact Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  constructor
  · apply (selbergMeanCoefficient_log_summable hc hc').of_nonneg_of_le (fun _ => abs_nonneg _)
    intro n; nlinarith [mul_nonneg (abs_nonneg (selbergMeanCoefficient c n/(n:ℝ))) (h n)]
  · apply (selbergMeanCoefficient_log_summable hc hc').of_nonneg_of_le (fun _ => abs_nonneg _)
    intro n; rw [abs_mul,abs_of_nonneg (h n)]; nlinarith [abs_nonneg (selbergMeanCoefficient c n/(n:ℝ))]


end AnalyticNumberTheory.SieveMethods
