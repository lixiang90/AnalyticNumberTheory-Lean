import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Summation of the Euler factors in a change of conductor

A divisor of the level contributes its totient. Averaging the missing
Euler factors with these weights saves an additional inverse prime,
which makes the product absolutely bounded.
-/
noncomputable section
open Real Finset
open scoped ArithmeticFunction
namespace AnalyticNumberTheory.DirichletLFunctions

private def totientWeight : ArithmeticFunction ℝ :=
  ⟨fun n=>(n.totient:ℝ),by simp⟩

private theorem totientWeight_mul : totientWeight.IsMultiplicative :=
  ⟨by simp [totientWeight],fun {x y} h=>by change ((x*y).totient:ℝ)=_;rw [Nat.totient_mul h];push_cast;rfl⟩

private theorem sum_divisor_quotient_totient (n : ℕ) :
    (∑d∈n.divisors,((n/d).totient:ℝ))=n := by
  have h := Nat.sum_divisorsAntidiagonal' (fun _ b : ℕ=>(b.totient:ℝ)) (n:=n)
  rw [Nat.sum_divisorsAntidiagonal (fun _ b : ℕ=>(b.totient:ℝ))] at h
  rw [h]
  exact_mod_cast Nat.sum_totient n

private theorem totient_convolution_primepow (w : ℕ→ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.prodPrimeFactors w*totientWeight) (p^(k+1))=
      (p:ℝ)^k*((p:ℝ)-1+w p) := by
  let P := ArithmeticFunction.prodPrimeFactors w
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b=>ArithmeticFunction.prodPrimeFactors w a*totientWeight b),Nat.sum_divisors_prime_pow hp,sum_range_succ']
  have h1 : (∑j∈range (k+1),P (p^(j+1))*totientWeight (p^(k+1)/p^(j+1)))=w p*(p:ℝ)^k := by
    have he (j : ℕ) : P (p^(j+1))=w p := by
      dsimp only [P];rw [ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_prime_pow (by omega) hp,prod_singleton]
    simp_rw [he];rw [←mul_sum]
    congr 1
    have h := sum_divisor_quotient_totient (p^k)
    rw [Nat.sum_divisors_prime_pow hp] at h
    change (∑j∈range (k+1),((p^(k+1)/p^(j+1)).totient:ℝ))=_
    simpa only [pow_succ,Nat.mul_div_mul_right _ _ hp.pos,Nat.cast_pow] using h
  change _+_=_
  rw [h1]
  simp only [pow_zero,Nat.div_one,ArithmeticFunction.IsMultiplicative.map_one (ArithmeticFunction.IsMultiplicative.prodPrimeFactors w),one_mul]
  change _+(((p^(k+1)).totient:ℕ):ℝ)=_
  rw [Nat.totient_prime_pow_succ hp];push_cast [hp.one_le];ring

/-- The totient-weighted convolution of the prime support weight has a
product upper bound. Each local excess w(p)−1 is divided by p. -/
theorem totient_euler_weight_product (w : ℕ→ℝ) (hw : ∀p,p.Prime → 1≤w p) (q : ℕ) :
    (∑d∈q.divisors,(d.totient:ℝ)*∏p∈(q/d).primeFactors,w p)≤
      (q:ℝ)*∏p∈q.primeFactors,(1+(w p-1)/p) := by
  classical
  let F := ArithmeticFunction.prodPrimeFactors w*totientWeight
  have hF : F.IsMultiplicative := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors w).mul totientWeight_mul
  have hcon (n : ℕ) : F n=∑d∈n.divisors,(d.totient:ℝ)*∏p∈(n/d).primeFactors,w p := by
    dsimp only [F];rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun a b=>ArithmeticFunction.prodPrimeFactors w a*totientWeight b)]
    apply sum_congr rfl;intro d hd
    have hx : n/d≠0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd))
    rw [ArithmeticFunction.prodPrimeFactors_apply hx,mul_comm];rfl
  have hpos (n : ℕ) : 0≤F n := by
    rw [hcon];exact sum_nonneg (fun d _=>mul_nonneg (Nat.cast_nonneg _) (prod_nonneg (fun p hp=>(by linarith [hw p (Nat.prime_of_mem_primeFactors hp)]))))
  rw [←hcon]
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    dsimp only [F];rw [totient_convolution_primepow w hp,Nat.primeFactors_prime_pow (by omega) hp,prod_singleton,Nat.cast_pow,pow_succ]
    have hx : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
    apply le_of_eq
    field_simp;ring
  | zero => simp
  | one => simp [hF.map_one]
  | coprime a b ha hb hab h₁ h₂ =>
    have hA : 0≤(a:ℝ)*∏p∈a.primeFactors,(1+(w p-1)/p) := (hpos a).trans h₁
    rw [hF.right hab,Nat.primeFactors_mul (by omega) (by omega),prod_union hab.disjoint_primeFactors,Nat.cast_mul]
    exact (mul_le_mul h₁ h₂ (hpos b) hA).trans_eq (by ring)

/-- The Euler loss on σ≥1/4 is absolutely bounded after conductor averaging. -/
theorem conductor_euler_fourth_weight_le : ∃ C : ℝ,0<C ∧ ∀q : ℕ,
    (∑d∈q.divisors,(d.totient:ℝ)*∏p∈(q/d).primeFactors,(1+(p:ℝ)^(-(1/4):ℝ))^4)≤C*q := by
  let w (p : ℕ) := (1+(p:ℝ)^(-(1/4):ℝ))^4
  let f (n : ℕ) := (n:ℝ)^(-(5/4):ℝ)
  have hs : Summable f := Real.summable_nat_rpow.mpr (by norm_num)
  have hpos (n : ℕ) : 0≤f n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let C := Real.exp (15*∑'n,f n)
  refine ⟨C,Real.exp_pos _,?_⟩;intro q
  have hw (p : ℕ) (_ : p.Prime) : 1≤w p := one_le_pow₀ (by linarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) p) (-(1/4):ℝ)]) (n:=4)
  have he (p : ℕ) (hp : p.Prime) : (w p-1)/(p:ℝ)≤15*f p := by
    let x := (p:ℝ)^(-(1/4):ℝ)
    have hx : 0≤x := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hx' : x≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_le) (by norm_num)
    have h₁ : x^2≤x := by nlinarith only [mul_nonneg hx (sub_nonneg.mpr hx')]
    have h₂ : x^3≤x^2 := by nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx')]
    have h₃ : x^4≤x^3 := by nlinarith only [mul_nonneg (pow_nonneg hx 3) (sub_nonneg.mpr hx')]
    have hpp : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
    have hpow : f p*(p:ℝ)=x := by
      dsimp [f,x];nth_rewrite 2 [←Real.rpow_one (p:ℝ)];rw [←Real.rpow_add hpp];norm_num
    rw [div_le_iff₀ hpp,mul_assoc, hpow]
    change (1+x)^4-1≤15*x
    nlinarith only [h₁,h₂,h₃]
  apply (totient_euler_weight_product w hw q).trans
  rw [mul_comm C]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc (∏p∈q.primeFactors,(1+(w p-1)/p))≤∏p∈q.primeFactors,Real.exp (15*f p) := by
         apply prod_le_prod₀
         · intro p hp;have hh := hw p (Nat.prime_of_mem_primeFactors hp);positivity [sub_nonneg.mpr hh]
         · intro p hp;linarith only [he p (Nat.prime_of_mem_primeFactors hp),Real.add_one_le_exp (15*f p)]
       _ = Real.exp (15*∑p∈q.primeFactors,f p) := by rw [←Real.exp_sum, mul_sum]
       _ ≤ C := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun n _=>hpos n)) (by norm_num))

end AnalyticNumberTheory.DirichletLFunctions
