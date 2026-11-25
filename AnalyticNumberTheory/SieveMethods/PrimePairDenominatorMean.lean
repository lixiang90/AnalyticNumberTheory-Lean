import AnalyticNumberTheory.SieveMethods.PrimePairEulerCoefficients

/-!
# The logarithmic mean in the prime-pair sieve

The Möbius transform has Euler product `1/(2 C₂)`, where `C₂` is the
twin-prime constant. Its absolute first Real.log moment bounds the remainder
in the denominator independently of the sieve limit.
-/

open Finset ArithmeticFunction Real Filter
open scoped ArithmeticFunction.Moebius Topology
namespace AnalyticNumberTheory.SieveMethods

private noncomputable def coeff (n : ℕ) : ℝ := primePairMeanCoefficient n/(n:ℝ)

private theorem coeff_one : coeff 1=1 := by simp [coeff,primePairMeanCoefficient_multiplicative.1]

private theorem coeff_sum : Summable (fun n => |coeff n|) := by
  apply primePairMeanCoefficient_log_summable.of_nonneg_of_le (fun _ => abs_nonneg _)
  intro n
  have hn : 0≤Real.log n := by
    rcases eq_or_ne n 0 with rfl|hn
    · simp
    · exact log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn)
  dsimp [coeff];nlinarith [mul_nonneg (abs_nonneg (primePairMeanCoefficient n/(n:ℝ))) hn]

private theorem coeff_local {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ,coeff (p^j))=if p=2 then 1/2 else 1+1/((p:ℝ)*(p-2)) := by
  obtain ⟨ha,hb,hd⟩ := primePairMeanCoefficient_local hp
  have ht (j : ℕ) (hj : j∉range 3) : coeff (p^j)=0 := by
    simp [coeff,hd j (by simpa using hj)]
  rw [tsum_eq_sum ht,sum_range_succ,sum_range_succ,sum_range_succ]
  simp only [sum_range_zero,zero_add,pow_zero,pow_one,coeff_one]
  rw [coeff,ha,coeff,hb,Nat.cast_pow]
  split_ifs with h
  · subst p; norm_num
  · have h3 : (3:ℝ)≤p := by exact_mod_cast (show 3≤p by have := hp.two_le;omega)
    have hne : (p:ℝ)-2≠0 := by linarith
    field_simp [hne];ring

private theorem coeff_product :
    HasProd (fun p : Nat.Primes => if p.val=2 then (1:ℝ) else 1+1/((p.val:ℝ)*(p.val-2)))
      (2*∑' n,coeff n) := by
  have H := EulerProduct.eulerProduct_hasProd coeff_one
    (fun {m n} h => by dsimp [coeff];rw [primePairMeanCoefficient_multiplicative.2 h,Nat.cast_mul];ring)
    (by simpa only [Real.norm_eq_abs] using coeff_sum) (by simp [coeff])
  simp_rw [show ∀ p : Nat.Primes, (∑' k : ℕ,coeff (p.val^k))=(if p.val=2 then 1/2 else 1+1/((p.val:ℝ)*(p.val-2))) from fun p => coeff_local p.prop] at H
  let p₂ : Nat.Primes := ⟨2,Nat.prime_two⟩
  have hi := (hasProd_ite_eq p₂ (2:ℝ)).mul H
  apply hi.congr_fun
  intro p
  by_cases h : p.val=2
  · have he : p=p₂ := Subtype.ext h
    subst p; norm_num [p₂] <;> rfl
  · have he : p≠p₂ := fun hh => h (congrArg Subtype.val hh)
    simp [he,h]

private theorem coeff_mass_pos : 0 < 2*∑' n,coeff n := by
  apply zero_lt_one.trans_le (le_of_tendsto_of_tendsto' tendsto_const_nhds coeff_product _)
  intro S
  apply Finset.one_le_prod₀
  intro p _;split_ifs with h
  · rfl
  · have h3 : (3:ℝ)≤p.val := by exact_mod_cast (show 3≤p.val by have := p.prop.two_le;omega)
    have h2 : 0<(p.val:ℝ)-2 := by linarith
    exact le_add_of_nonneg_right (by positivity)

private theorem coeff_inverse_product :
    HasProd (fun p : Nat.Primes => if p.val=2 then 1 else 1-1/((p.val:ℝ)-1)^2)
      (2*∑' n,coeff n)⁻¹ := by
  apply (coeff_product.inv₀ coeff_mass_pos.ne').congr_fun
  intro p
  by_cases h : p.val=2
  · simp [h]
  · have h3 : (3:ℝ)≤p.val := by exact_mod_cast (show 3≤p.val by have := p.prop.two_le;omega)
    have hn : (p.val:ℝ)-2≠0 := by linarith
    have hp0 : (0:ℝ)<p.val := by linarith
    have hp1 : (p.val:ℝ)-1≠0 := by linarith
    have hpos : 0<(p.val:ℝ)*(p.val-2)+1 := by nlinarith [mul_nonneg hp0.le (show 0≤(p.val:ℝ)-2 by linarith)]
    simp only [h,ite_false]
    field_simp [hn,hp1,hp0.ne',hpos.ne'];ring

/-- The defining infinite product converges to the twin-prime constant. -/
theorem hasProd_twinPrimeEulerConstant :
    HasProd (fun p : Nat.Primes => if p.val=2 then 1 else 1-1/((p.val:ℝ)-1)^2)
      twinPrimeEulerConstant := coeff_inverse_product.multipliable.hasProd

/-- The universal lower Euler factor in the binary and ternary Goldbach
series has product twice the twin-prime constant, accounting for the prime two. -/
theorem hasProd_goldbach_lower_factor :
    HasProd (fun p : Nat.Primes => if p.val=2 then 2 else 1-1/((p.val:ℝ)-1)^2)
      (2*twinPrimeEulerConstant) := by
  let p₂ : Nat.Primes := ⟨2,Nat.prime_two⟩
  apply ((hasProd_ite_eq p₂ (2:ℝ)).mul hasProd_twinPrimeEulerConstant).congr_fun
  intro p
  by_cases h : p.val=2
  · have he : p=p₂ := Subtype.ext h
    subst p;norm_num [p₂] <;>rfl
  · have he : p≠p₂ := fun he => h (congrArg Subtype.val he)
    simp [h,he]

private theorem coeff_mass_eq : 2*twinPrimeEulerConstant*(∑' n,coeff n)=1 := by
  have hi : twinPrimeEulerConstant = (2*∑' n,coeff n)⁻¹ := coeff_inverse_product.tprod_eq
  have hne : (∑' n,coeff n)≠0 := fun he => by simpa [he] using coeff_mass_pos
  rw [hi];field_simp [hne]

theorem twinPrimeEulerConstant_pos : 0<twinPrimeEulerConstant := by
  have h := coeff_mass_eq
  by_contra! hn
  nlinarith only [h,mul_nonpos_of_nonpos_of_nonneg hn coeff_mass_pos.le]

private theorem coefficient_squarefree {n : ℕ} (hn : Squarefree n) :
    primePairCoefficient n/(n:ℝ) = ∏p∈n.primeFactors, ((p:ℝ)-2)⁻¹ := by
  have hprod : (∏p∈n.primeFactors,(p:ℝ))=n := by simpa only [Nat.cast_prod] using congrArg (fun t : ℕ => (t:ℝ)) (Nat.prod_primeFactors_of_squarefree hn)
  rw [primePairCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
    ← Int.cast_pow,moebius_sq_eq_one_of_squarefree hn,Int.cast_one,one_mul,prodPrimeFactors_apply hn.ne_zero]
  simp only [div_eq_mul_inv,prod_mul_distrib,hprod]
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne_zero
  field_simp

private theorem normalized_sum (N : ℕ) :
    (∑d∈Icc 1 N,primePairCoefficient d/(d:ℝ))=primePairDenominator 2 N := by
  classical
  rw [primePairDenominator,Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro n hn; by_cases hs : Squarefree n
  · rw [coefficient_squarefree hs]
    by_cases hc : n.Coprime 2
    · rw [if_pos ⟨hs,hc⟩]
    · simp only [hs,hc,and_false,ite_false]
      have h2 : 2∣n := by by_contra he;exact hc ((Nat.prime_two.coprime_iff_not_dvd.mpr he).symm)
      apply prod_eq_zero (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h2,hs.ne_zero⟩)
      norm_num
  · simp [hs,primePairCoefficient,pmul_apply,ppow_apply (by norm_num : 0<2),intCoe_apply,
      moebius_eq_zero_of_not_squarefree hs]

private theorem centered_limit :
    ∃ K : ℝ, Tendsto (fun N : ℕ => primePairDenominator 2 N-(∑' n,coeff n)*Real.log N) atTop (𝓝 K) := by
  let K := ∑' d : ℕ,coeff d*(Real.eulerMascheroniConstant-Real.log d)
  refine ⟨K,?_⟩
  have H := DirichletSeries.tendsto_divisor_harmonic_centered (h:=coeff) (by simp [coeff])
    primePairMeanCoefficient_log_summable
  apply H.congr'
  filter_upwards with N
  have hs (d : ℕ) (hd : d∉Icc 1 N) : coeff d*(harmonic (N/d):ℝ)=0 := by
    by_cases hz : d=0
    · simp [hz,coeff]
    rw [Nat.div_eq_of_lt (by simp only [mem_Icc,not_and_or,not_le] at hd;omega : N<d)]
    simp
  have hfin := (hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) hs).summable
  simp_rw [mul_sub]
  rw [hfin.tsum_sub (coeff_sum.of_abs.mul_right _),tsum_mul_right]
  congr 1
  change (∑' d : ℕ,(primePairMeanCoefficient d/d)*(harmonic (N/d):ℝ))=_
  rw [←DirichletSeries.sum_divisor_sum_div_eq_tsum_harmonic]
  simp_rw [sum_primePairMeanCoefficient_divisors]
  exact normalized_sum N

/-- An absolute additive error for the logarithmic Selberg denominator when only two is excluded. -/
theorem primePairDenominator_two_lower :
    ∃ L : ℝ, 0≤L ∧ ∀ {z : ℝ}, 2≤z → Real.log z-L ≤ 2*twinPrimeEulerConstant*primePairDenominator 2 z := by
  obtain ⟨K,hK⟩ := centered_limit
  let c := ∑' n,coeff n
  have hc : 0<c := by change 0<c; dsimp [c];linarith only [coeff_mass_pos]
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hK.eventually_const_lt (show K-1<K by linarith))
  let L := max (Real.log ((N:ℝ)+2)) (Real.log 2+2*twinPrimeEulerConstant*(1-K))
  refine ⟨L,(log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) N] : 1≤(N:ℝ)+2)).trans (le_max_left ..),?_⟩
  intro z hz
  have hz0 : 0<z := by linarith
  have hd : 0≤primePairDenominator 2 z := by
    unfold primePairDenominator;apply sum_nonneg
    intro n _;apply prod_nonneg;intro p hp
    have hp' : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    positivity
  by_cases hnz : N≤⌊z⌋₊
  · have hh := hN _ hnz
    have hf : (1:ℕ)≤⌊z⌋₊ := Nat.le_floor (by simpa using (le_trans (by norm_num : (1:ℝ)≤2) hz))
    have hfr : (1:ℝ)≤⌊z⌋₊ := by exact_mod_cast hf
    have hzz : z ≤ 2*⌊z⌋₊ := by linarith [Nat.lt_floor_add_one z]
    have hlog := Real.log_le_log hz0 hzz
    rw [Real.log_mul (by norm_num) (by positivity)] at hlog
    have he : primePairDenominator 2 (⌊z⌋₊:ℝ)=primePairDenominator 2 z := by simp [primePairDenominator]
    change K-1 < primePairDenominator 2 (⌊z⌋₊:ℝ)-c*Real.log ⌊z⌋₊ at hh
    rw [he] at hh
    have hm : 2*twinPrimeEulerConstant*c=1 := coeff_mass_eq
    have he' := mul_lt_mul_of_pos_left hh (mul_pos (by norm_num : (0:ℝ)<2) twinPrimeEulerConstant_pos)
    have hnorm : (2*twinPrimeEulerConstant)*(c*Real.log (⌊z⌋₊:ℝ))=Real.log (⌊z⌋₊:ℝ) := by rw [←mul_assoc,hm,one_mul]
    simp only [mul_sub,hnorm,mul_one] at he'
    linarith only [hlog,he',le_max_right (Real.log 2+2*twinPrimeEulerConstant*(1-K)) (Real.log ((N:ℝ)+2)),
      show Real.log 2+2*twinPrimeEulerConstant*(1-K)≤L from le_max_right ..]
  · have hzN : z ≤ (N:ℝ)+2 := by
      have : (⌊z⌋₊:ℝ)<N := by exact_mod_cast (not_le.mp hnz)
      linarith [Nat.lt_floor_add_one z]
    have hh : Real.log z≤L := (Real.log_le_log hz0 hzN).trans (le_max_left ..)
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) twinPrimeEulerConstant_pos.le) hd]

end AnalyticNumberTheory.SieveMethods
