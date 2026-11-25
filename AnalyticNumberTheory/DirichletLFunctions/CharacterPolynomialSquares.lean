import AnalyticNumberTheory.DirichletLFunctions.Characters
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.SieveMethods.WeightedMeanValues

/-!
# Squares of character Dirichlet polynomials

Squaring a polynomial supported on a finite set gives the ordered factorization
count restricted to that set. The resulting coefficients are dominated by the
divisor function, and a tail above N is supported strictly above N squared.
-/
noncomputable section
open Real Complex Finset
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Number of ordered representations as a product of two indices of the
finite polynomial. -/
def factorPairCount (S : Finset ℕ) (k : ℕ) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1*p.2=k)).card

theorem factorPairCount_le_divisors (S : Finset ℕ) {k : ℕ} (hk : 0<k) :
    factorPairCount S k≤k.divisors.card := by
  have hsub : ((S ×ˢ S).filter (fun p=>p.1*p.2=k))⊆k.divisorsAntidiagonal :=
    fun p hp => Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hp).2,hk.ne'⟩
  have h := card_le_card hsub
  rw [←Nat.map_div_right_divisors,card_map] at h
  exact h

theorem factorPairCount_eq_zero {S : Finset ℕ} {N k : ℕ}
    (hS : ∀n∈S,N<n) (hk : k≤N^2) : factorPairCount S k=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hmem,he⟩ := mem_filter.mp hp
  obtain ⟨hm,hn⟩ := mem_product.mp hmem
  have hmul := Nat.mul_lt_mul_of_lt_of_lt (hS _ hm) (hS _ hn)
  rw [←he,pow_two] at hk
  omega

/-- The coefficient of k in the square of a finitely supported Dirichlet polynomial. -/
def factorPairWeight (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (S ×ˢ S).filter (fun p => p.1*p.2=k), a p.1 * a p.2

/-- Squaring coefficients of modulus at most one costs at most the ordinary divisor function. -/
theorem norm_factorPairWeight_le {S : Finset ℕ} {a : ℕ → ℂ} (ha : ∀ n∈S, ‖a n‖≤1)
    {k : ℕ} (hk : 0<k) : ‖factorPairWeight S a k‖ ≤ k.divisors.card := by
  apply (norm_sum_le _ _).trans
  apply le_trans (b:=∑ _p∈(S ×ˢ S).filter (fun p => p.1*p.2=k),(1:ℝ))
  · apply sum_le_sum; intro p hp
    obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hp).1
    rw [norm_mul];exact mul_le_one₀ (ha _ hi) (norm_nonneg _) (ha _ hj)
  · simpa only [sum_const,nsmul_eq_mul,mul_one,factorPairCount] using
      (Nat.cast_le.mpr (factorPairCount_le_divisors S hk) :
        (factorPairCount S k:ℝ) ≤ k.divisors.card)

/-- Squaring a twisted polynomial preserves the character and convolves the original coefficients. -/
theorem weighted_characterPolynomial_square {q M : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ→ℂ) (S : Finset ℕ) (hS : S⊆Finset.Icc 1 M) (s : ℂ) :
    (∑n∈S,a n*χ n*(n:ℂ)^(-s))^2=
      ∑k∈Finset.Icc 1 (M^2),factorPairWeight S a k*χ k*(k:ℂ)^(-s) := by
  let F (k : ℕ) := χ k*(k:ℂ)^(-s)
  have hmul (m n : ℕ) : F m*F n=F (m*n) := by
    simp only [F,Nat.cast_mul,map_mul,Complex.natCast_mul_natCast_cpow];ring
  have hmap (p : ℕ×ℕ) (hp : p∈S ×ˢ S) : p.1*p.2∈Finset.Icc 1 (M^2) := by
    obtain ⟨hm,hn⟩ := mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp (hS hm)).1 (mem_Icc.mp (hS hn)).1,
      by simpa [pow_two] using Nat.mul_le_mul (mem_Icc.mp (hS hm)).2 (mem_Icc.mp (hS hn)).2⟩
  simp only [mul_assoc]
  change (∑n∈S,a n*F n)^2=∑k∈Finset.Icc 1 (M^2),factorPairWeight S a k*F k
  rw [pow_two,sum_mul];simp_rw [mul_sum]
  rw [←sum_product',←sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl;intro k _
  rw [factorPairWeight,sum_mul]
  apply sum_congr rfl;intro p hp
  have he := (mem_filter.mp hp).2
  calc _ = (a p.1 * a p.2)*(F p.1*F p.2) := by ring
       _ = _ := by rw [hmul,he]

/-- The square of a finite character Dirichlet polynomial written at twice
the original length on a logarithmic scale. -/
theorem characterPolynomial_square {q M : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (hS : S⊆Finset.Icc 1 M) (s : ℂ) :
    (∑n∈S,χ n*(n:ℂ)^(-s))^2=
      ∑k∈Finset.Icc 1 (M^2),(factorPairCount S k:ℂ)*χ k*(k:ℂ)^(-s) := by
  simpa [factorPairWeight,factorPairCount] using
    weighted_characterPolynomial_square χ (fun _ => 1) S hS s

/-- The coefficient used after writing the real part as a positive real
weight and retaining only the imaginary frequency in the polynomial. -/
def characterSquareWeight (S : Finset ℕ) (σ : ℝ) (k : ℕ) : ℂ :=
  (factorPairCount S k:ℂ)*(((k:ℝ)^(-σ):ℝ):ℂ)

theorem characterSquareWeight_norm_sq (S : Finset ℕ) (σ : ℝ) (k : ℕ) :
    ‖characterSquareWeight S σ k‖^2=(factorPairCount S k:ℝ)^2*(k:ℝ)^(-2*σ) := by
  rw [characterSquareWeight,norm_mul,mul_pow,Complex.norm_real,Complex.norm_natCast,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),←Real.rpow_natCast ((k:ℝ)^(-σ)) 2,
    ←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 2;push_cast;ring

theorem characterPolynomial_norm_four {q M : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (hS : S⊆Finset.Icc 1 M) (σ t : ℝ) :
    ‖∑n∈S,χ n*(n:ℂ)^(-((σ:ℂ)+t*I))‖^4=
      ‖∑k∈Finset.Icc 1 (M^2),characterSquareWeight S σ k*χ k*(k:ℂ)^(-(I*(t:ℂ)))‖^2 := by
  rw [show (4:ℕ)=2*2 by decide,pow_mul,←norm_pow,characterPolynomial_square χ S hS]
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply sum_congr rfl;intro k hk
  have hp : 0<(k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk).1
  have H : (k:ℂ)^(-((σ:ℂ)+t*I))=(((k:ℝ)^(-σ):ℝ):ℂ)*(k:ℂ)^(-(I*(t:ℂ))) := by
    rw [show -((σ:ℂ)+t*I)=(-σ:ℂ)+(-(I*(t:ℂ))) by ring,Complex.cpow_add _ _ (by exact_mod_cast hp.ne')]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_neg,Complex.ofReal_cpow hp.le]
  rw [H];dsimp [characterSquareWeight];ring

end AnalyticNumberTheory.DirichletLFunctions
