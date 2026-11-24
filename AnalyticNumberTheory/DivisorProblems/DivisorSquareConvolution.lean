import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola

/-!
# A convolution identity for the square of the divisor function

Starting from the indicator of squarefree integers, three Dirichlet
convolutions with the constant-one function give the pointwise square
of the divisor function. On a prime power the successive differences of
the square are the odd integers.
-/
noncomputable section
open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.sigma
namespace AnalyticNumberTheory.DivisorProblems

/-- The indicator of the squarefree integers as a real arithmetic function. -/
def squarefreeIndicator : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ).pmul (μ : ArithmeticFunction ℝ)

@[simp] theorem squarefreeIndicator_apply (n : ℕ) : squarefreeIndicator n=(μ n:ℝ)^2 := by
  simp [squarefreeIndicator,pmul_apply,pow_two]

/-- Dirichlet convolution with the constant-one arithmetic function. -/
def divisorTransform (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f*(ζ : ArithmeticFunction ℝ)

theorem divisorTransform_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divisorTransform f n = ∑ d ∈ n.divisors,f d := coe_mul_zeta_apply

private theorem transform_prime_succ (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    divisorTransform f (p^(i+1)) = divisorTransform f (p^i)+f (p^(i+1)) := by
  simp only [divisorTransform_apply,Nat.sum_divisors_prime_pow hp,sum_range_succ _ (i+1)]

private theorem transform_one (f : ArithmeticFunction ℝ) : divisorTransform f 1=f 1 := by
  simp [divisorTransform_apply]

/-- The square of the divisor count is the third divisor transform of the
squarefree indicator. -/
theorem divisorTransform_three_squarefree (n : ℕ) :
    divisorTransform (divisorTransform (divisorTransform squarefreeIndicator)) n =
      (n.divisors.card:ℝ)^2 := by
  let Z := (ζ : ArithmeticFunction ℝ)
  let F := squarefreeIndicator
  let D := (σ 0 : ArithmeticFunction ℝ)
  have hZ : Z.IsMultiplicative := isMultiplicative_zeta.natCast
  have hF : F.IsMultiplicative := isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast
  have hD : D.IsMultiplicative := isMultiplicative_sigma.natCast
  have hid : divisorTransform (divisorTransform (divisorTransform F))=D.pmul D := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers _ (((hF.mul hZ).mul hZ).mul hZ) _ (hD.pmul hD)).mpr
    intro p i hp
    have h1 : F 1=1 := hF.map_one
    have h2 (j : ℕ) : divisorTransform F (p^(j+1))=2 := by
      induction j with
      | zero =>
        rw [transform_prime_succ _ hp,pow_zero,transform_one,h1,pow_one]
        norm_num [F,moebius_apply_prime hp]
      | succ j ih =>
        rw [transform_prime_succ _ hp,ih]
        simp [F,moebius_apply_prime_pow hp (show j+1+1≠0 by omega)]
    have h3 (j : ℕ) : divisorTransform (divisorTransform F) (p^j)=2*j+1 := by
      induction j with
      | zero => simp [transform_one,h1]
      | succ j ih => rw [transform_prime_succ _ hp,ih,h2]; push_cast; ring
    have h4 (j : ℕ) : divisorTransform (divisorTransform (divisorTransform F)) (p^j)=((j:ℝ)+1)^2 := by
      induction j with
      | zero => simp [transform_one,h1]
      | succ j ih => rw [transform_prime_succ _ hp,ih,h3]; push_cast; ring
    change divisorTransform (divisorTransform (divisorTransform F)) (p^i) = _
    rw [h4,pmul_apply]
    simp [D,sigma_zero_apply_prime_pow hp,pow_two]
  have hh := DFunLike.congr_fun hid n
  simpa [D,F,pmul_apply,sigma_zero_apply,pow_two] using hh

end AnalyticNumberTheory.DivisorProblems
