import AnalyticNumberTheory.SieveMethods.SelbergWeightMeans

/-!
# Local coefficients for the prime-pair Selberg denominator

At odd primes the density is `1/(p-1)`, giving the Selberg factor
`1/(p-2)`. The coefficient at two vanishes. Möbius convolution gives an
absolutely convergent Euler product after division by the index.
-/

open ArithmeticFunction Finset Real Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology
namespace AnalyticNumberTheory.SieveMethods

/-- The convergent common Euler factor for prime pairs, omitting two. -/
noncomputable def twinPrimeEulerConstant : ℝ :=
  ∏' p : Nat.Primes, if p.val=2 then 1 else 1-1/((p.val:ℝ)-1)^2

/-- The local correction to the common prime-pair constant at the odd factors of the shift. -/
noncomputable def primePairSingularFactor (h : ℕ) : ℝ :=
  twinPrimeEulerConstant * ∏ p∈h.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2))

/-- Selberg's denominator for primes lying in reduced classes modulo the divisors of the shift. -/
noncomputable def primePairDenominator (h : ℕ) (z : ℝ) : ℝ :=
  ∑d∈(Icc 1 ⌊z⌋₊).filter (fun d => Squarefree d ∧ d.Coprime h),
      ∏p∈d.primeFactors, ((p:ℝ)-2)⁻¹

/-- Squarefree arithmetic coefficient whose logarithmic mean is needed for the denominator. -/
noncomputable def primePairCoefficient : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).ppow 2).pmul (prodPrimeFactors fun p => (p:ℝ)/(p-2))

/-- Möbius transform of the prime-pair coefficient. -/
noncomputable def primePairMeanCoefficient : ArithmeticFunction ℝ :=
  primePairCoefficient*(μ : ArithmeticFunction ℝ)

theorem primePairCoefficient_multiplicative : primePairCoefficient.IsMultiplicative :=
  isMultiplicative_moebius.intCast.ppow.pmul (IsMultiplicative.prodPrimeFactors _)

theorem primePairMeanCoefficient_multiplicative : primePairMeanCoefficient.IsMultiplicative :=
  primePairCoefficient_multiplicative.mul isMultiplicative_moebius.intCast

theorem sum_primePairMeanCoefficient_divisors (n : ℕ) :
    ∑d∈n.divisors,primePairMeanCoefficient d=primePairCoefficient n := by
  rw [← coe_mul_zeta_apply,primePairMeanCoefficient,mul_assoc,coe_moebius_mul_coe_zeta,mul_one]

private theorem coefficient_prime {p : ℕ} (hp : p.Prime) : primePairCoefficient p=(p:ℝ)/(p-2) := by
  simp [primePairCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    moebius_apply_prime hp,prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

private theorem coefficient_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2≤k) :
    primePairCoefficient (p^k)=0 := by
  simp [primePairCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    moebius_apply_prime_pow hp (by omega : k≠0),show k≠1 by omega]

theorem primePairMeanCoefficient_local {p : ℕ} (hp : p.Prime) :
    primePairMeanCoefficient p=(p:ℝ)/(p-2)-1 ∧
    primePairMeanCoefficient (p^2) = -((p:ℝ)/(p-2)) ∧
    ∀ k : ℕ, 3≤k → primePairMeanCoefficient (p^k)=0 := by
  have hs (k : ℕ) : primePairMeanCoefficient (p^(k+1))=primePairCoefficient (p^(k+1))-primePairCoefficient (p^k) := by
    have h := sum_primePairMeanCoefficient_divisors (p^(k+1))
    have h' := sum_primePairMeanCoefficient_divisors (p^k)
    rw [Nat.sum_divisors_prime_pow hp,sum_range_succ] at h
    rw [Nat.sum_divisors_prime_pow hp] at h'
    linarith
  refine ⟨by simpa [primePairCoefficient_multiplicative.1,coefficient_prime hp] using hs 0,?_,?_⟩
  · simpa [coefficient_prime_pow hp (le_refl 2),coefficient_prime hp] using hs 1
  · rintro (_|k) hk
    · omega
    rw [hs,coefficient_prime_pow hp (by omega),coefficient_prime_pow hp (by omega),sub_self]

/-- Absolute convergence with room to include a logarithm at one. -/
theorem primePairMeanCoefficient_summable :
    Summable (fun n : ℕ => |primePairMeanCoefficient n*(n:ℝ)^(-(3/4):ℝ)|) := by
  let f (n : ℕ) := primePairMeanCoefficient n*(n:ℝ)^(-(3/4):ℝ)
  have h₁ : f 1=1 := by simp [f,primePairMeanCoefficient_multiplicative.1]
  apply DirichletSeries.summable_of_local_euler_bounds (f:=f) (by simp [f]) h₁
    (fun {_ _} h => by simp only [f,primePairMeanCoefficient_multiplicative.2 h,Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)];ring)
    (fun n => 9*(n:ℝ)^(-(3/2):ℝ)) (fun _ => by positivity)
    ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).mul_left 9)
  intro p hp
  have hpp : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  obtain ⟨hp₁,hp₂,hp₃⟩ := primePairMeanCoefficient_local hp
  have hsup (j : ℕ) (hj : j∉range 3) : |f (p^j)|=0 := by
    simp [f,hp₃ j (by simpa using hj)]
  refine ⟨(hasSum_sum_of_ne_finset_zero hsup).summable,?_⟩
  rw [tsum_eq_sum hsup,sum_range_succ,sum_range_succ,sum_range_succ]
  simp only [pow_zero,pow_one,h₁,abs_one,sum_range_zero,zero_add]
  have hbounds : |(p:ℝ)/(p-2)-1|≤6/p ∧ |(p:ℝ)/(p-2)|≤3 := by
    by_cases he : p=2
    · subst p;norm_num
    have h3 : (3:ℝ)≤p := by exact_mod_cast (show 3≤p by have := hp.two_le;omega)
    have hd : (0:ℝ)<p-2 := by linarith
    rw [show (p:ℝ)/(p-2)-1=2/(p-2) by field_simp;ring,abs_of_pos (by positivity),
      abs_of_pos (div_pos hpp hd),div_le_div_iff₀ hd hpp,div_le_iff₀ hd]
    constructor <;> linarith
  have h₁' : |f p|≤6*(p:ℝ)^(-(3/2):ℝ) := by
    rw [show |f p|=|(p:ℝ)/(p-2)-1| *(p:ℝ)^(-(3/4):ℝ) by simp [f,hp₁,abs_mul,Real.rpow_nonneg hpp.le]]
    calc _ ≤ (6/p)*(p:ℝ)^(-(3/4):ℝ) := by gcongr;exact hbounds.1
         _ = 6*(p:ℝ)^(-(7/4):ℝ) := by rw [div_eq_mul_inv,←Real.rpow_neg_one,mul_assoc,←Real.rpow_add hpp];norm_num
         _ ≤ _ := by exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by norm_num)) (by norm_num)
  have h₂' : |f (p^2)|≤3*(p:ℝ)^(-(3/2):ℝ) := by
    dsimp [f];rw [hp₂,abs_mul,abs_neg,abs_of_nonneg (by positivity : (0:ℝ)≤((p^2:ℕ):ℝ)^(-(3/4):ℝ)),
      Nat.cast_pow,← Real.rpow_natCast (p:ℝ) 2,←Real.rpow_mul hpp.le]
    norm_num
    exact mul_le_mul_of_nonneg_right hbounds.2 (by positivity)
  linarith

/-- Absolute first logarithmic moment of the normalized Möbius transform. -/
theorem primePairMeanCoefficient_log_summable :
    Summable (fun n : ℕ => |primePairMeanCoefficient n/(n:ℝ)| *(1+Real.log n)) := by
  have H := primePairMeanCoefficient_summable.mul_left 5
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
      _ ≤ (|primePairMeanCoefficient n|/n)*(5*(n:ℝ)^(1/4:ℝ)) := by gcongr
      _ = _ := by
        rw [div_eq_mul_inv,← Real.rpow_neg_one]
        have he : (n:ℝ)^(-1:ℝ)*(n:ℝ)^(1/4:ℝ)=(n:ℝ)^(-(3/4):ℝ) := by rw [← Real.rpow_add hpos];norm_num
        rw [←he];ring

end AnalyticNumberTheory.SieveMethods
