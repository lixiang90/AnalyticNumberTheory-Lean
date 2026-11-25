import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Square terms in the convolution of a quadratic character with one

At every positive square, the real coefficient of `ζ L(s,χ)` is
at least one. Retaining these terms gives a lower bound on its
exponentially weighted sum.
-/

open Complex Real Finset ArithmeticFunction
open scoped ComplexOrder
namespace AnalyticNumberTheory.DirichletLFunctions
variable {N : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
private theorem one_le_zetaMul_prime_even {χ : DirichletCharacter ℂ N} (hχ : χ^2=1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : 1≤χ.zetaMul (p^(2*k)) := by
  rw [DirichletCharacter.zetaMul,coe_zeta_mul_apply]
  simp only [toArithmeticFunction,coe_mk,
    Nat.sum_divisors_prime_pow hp,pow_eq_zero_iff',hp.ne_zero,ne_eq,false_and,↓reduceIte,Nat.cast_pow,map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h|h|h
  · rw [h,geom_sum_succ']; cases k <;> simp
  · simp [h]; positivity
  · rw [h,neg_one_geom_sum,if_neg (by rintro ⟨v,hv⟩; omega)]

/-- Every positive square carries at least unit mass in `1*χ`. -/
theorem one_le_zetaMul_square {χ : DirichletCharacter ℂ N} (hχ : χ^2=1) {n : ℕ} (hn : 1≤n) :
    1≤(χ.zetaMul (n^2)).re := by
  have H : 1≤χ.zetaMul (n^2) := by
    rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero _ (by omega))]
    apply Finset.one_le_prod₀
    intro p hp
    rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    exact one_le_zetaMul_prime_even hχ (Nat.prime_of_mem_primeFactors hp) _
  exact H.1

/-- Absolute summability of the real coefficients with exponential damping. -/
theorem summable_zetaMul_re_exp (χ : DirichletCharacter ℂ N) {X : ℝ} (hX : 0<X) :
    Summable fun n : ℕ => (χ.zetaMul n).re*Real.exp (-(n:ℝ)/X) := by
  let q := Real.exp (-1/X)
  have hq : ‖q‖<1 := by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hX)
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  apply Summable.of_norm_bounded hs
  intro n
  have hnum : ‖χ.zetaMul n‖≤(n:ℝ) := by
    rw [DirichletCharacter.zetaMul,coe_zeta_mul_apply]
    exact (norm_sum_le _ _).trans <| calc
      _ ≤ ∑ _d ∈ n.divisors,(1:ℝ) := by
        apply sum_le_sum; intro d hd
        simp only [toArithmeticFunction,coe_mk,if_neg (Nat.pos_of_mem_divisors hd).ne']
        exact DirichletCharacter.norm_le_one _ _
      _ ≤ _ := by simpa using (show (n.divisors.card:ℝ)≤n by exact_mod_cast Nat.card_divisors_le_self n)
  rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,pow_one]
  have he : q^n=Real.exp (-(n:ℝ)/X) := by rw [←Real.exp_nat_mul]; congr 1; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hnum) (Real.exp_pos _).le

/-- A lower bound with its full floor for every positive real cutoff. -/
theorem sqrt_floor_le_zetaMul_exp {χ : DirichletCharacter ℂ N} (hχ : χ^2=1) {X : ℝ} (hX : 0<X) :
    Real.exp (-1)*(⌊Real.sqrt X⌋₊:ℝ)≤∑' n : ℕ,(χ.zetaMul n).re*Real.exp (-(n:ℝ)/X) := by
  let M := ⌊Real.sqrt X⌋₊
  let S := Icc 1 M
  let f (n : ℕ) := (χ.zetaMul n).re*Real.exp (-(n:ℝ)/X)
  have hs := summable_zetaMul_re_exp χ hX
  have hpos (n : ℕ) : 0≤f n := mul_nonneg (DirichletCharacter.zetaMul_nonneg hχ n).1 (Real.exp_pos _).le
  calc
    _ = ∑ _n ∈ S,Real.exp (-1) := by simp [S,M,mul_comm]
    _ ≤ ∑ n ∈ S,f (n^2) := by
      apply sum_le_sum; intro n hn
      obtain ⟨hn₁,hn₂⟩ := mem_Icc.mp hn
      have hn' : (n:ℝ)≤Real.sqrt X := (Nat.cast_le.mpr hn₂).trans (Nat.floor_le (Real.sqrt_nonneg _))
      have hn'' : (n:ℝ)^2≤X := (pow_le_pow_left₀ (Nat.cast_nonneg n) hn' 2).trans_eq (Real.sq_sqrt hX.le)
      have he : Real.exp (-1)≤Real.exp (-((n^2:ℕ):ℝ)/X) := by
        apply Real.exp_le_exp.mpr; rw [le_div_iff₀ hX]; push_cast; linarith
      exact he.trans (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_zetaMul_square hχ hn₁))
    _ = ∑ n ∈ S.image (fun n => n^2),f n := by
      rw [sum_image]; intro a _ b _ hab
      exact Nat.pow_left_injective (by decide : (2:ℕ)≠0) hab
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ => hpos n)

end AnalyticNumberTheory.DirichletLFunctions
