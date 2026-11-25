import AnalyticNumberTheory.AnalyticTools.ReciprocalLargeSieveWeights
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovSmallConductors
import AnalyticNumberTheory.SieveMethods.DirichletPolynomials

/-! # Primitive second moments of the twisted Chebyshev function -/
noncomputable section
open Finset Real Complex
open scoped ArithmeticFunction.vonMangoldt Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.PrimeDistribution

/-- The energy of the Chebyshev sums attached to primitive characters
of a single modulus. -/
def primitivePsiEnergy (x : ℝ) (d : ℕ) : ℝ :=
  ∑ χ∈univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),‖psiChar x χ‖^2

theorem primitivePsiEnergy_nonneg (x : ℝ) (d : ℕ) : 0≤primitivePsiEnergy x d :=
  sum_nonneg (fun _ _ => sq_nonneg _)

/-- The von Mangoldt coefficients have energy at most a constant times x log x. -/
theorem vonMangoldt_square_energy {x : ℝ} (hx : 1≤x) :
    (∑ n∈Icc 1 ⌊x⌋₊,(Λ n)^2)≤(Real.log 4+4)*x*Real.log x := by
  have hb (n) (hn : n∈Icc 1 ⌊x⌋₊) := ArithmeticFunction.vonMangoldt_le_log (n:=n) |>.trans
    (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1 : (0:ℝ)<n)
      ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le (zero_le_one.trans hx))))
  have h := sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hb n hn) (ArithmeticFunction.vonMangoldt_nonneg (n:=n)))
  simp only [←sq,←sum_mul] at h
  have he : (∑ n∈Icc 1 ⌊x⌋₊,Λ n)=Chebyshev.psi x := by
    rw [Chebyshev.psi,←Icc_add_one_left_eq_Ioc,zero_add]
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (zero_le_one.trans hx)) (Real.log_nonneg hx))

/-- Large-sieve control of the primitive character second moment summed up to U. -/
theorem primitivePsiEnergy_cumulative {x : ℝ} (hx : 1≤x) (U : ℕ) :
    (∑ d∈Icc 1 U,(d/d.totient:ℝ)*primitivePsiEnergy x d)≤
      (x+(U:ℝ)^2)*((Real.log 4+4)*x*Real.log x) := by
  have h := character_large_sieve_dirichlet_Icc (fun n => (Λ n:ℂ)) ⌊x⌋₊ U
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at h
  simp_rw [mul_comm (a:=((Λ _ :ℝ):ℂ))] at h
  apply h.trans
  exact mul_le_mul (by linarith only [Nat.floor_le (zero_le_one.trans hx)])
    (vonMangoldt_square_energy hx) (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- Above R, partial summation replaces the factor x in the large-sieve
constant by x/R, without a logarithmic loss at the upper endpoint. -/
theorem primitivePsiEnergy_large_conductors {x : ℝ} (hx : 1≤x) {R : ℕ} (hR : 1≤R) (U : ℕ) :
    (∑ d∈Ioc R U,(d.totient:ℝ)⁻¹*primitivePsiEnergy x d)≤
      (2*(U:ℝ)+x/R)*((Real.log 4+4)*x*Real.log x) := by
  have h := reciprocal_sum_of_quadratic_cumulative (fun d => (d/d.totient:ℝ)*primitivePsiEnergy x d)
    (fun d => mul_nonneg (by positivity) (primitivePsiEnergy_nonneg x d))
    (by positivity [Real.log_nonneg hx] : 0≤(Real.log 4+4)*x*Real.log x) (zero_le_one.trans hx) hR
    (primitivePsiEnergy_cumulative hx) (U:=U)
  apply le_trans _ h
  apply sum_le_sum;intro d hd
  have hi : (d:ℝ)≠0 := by exact_mod_cast (Nat.zero_lt_of_lt (mem_Ioc.mp hd).1).ne'
  exact le_of_eq (by field_simp [hi])

/-- For logarithmically small conductors the Siegel–Walfisz estimate supplies
an arbitrary logarithmic saving in the primitive second moment. -/
theorem primitivePsiEnergy_small_conductors (A : ℝ) {L : ℝ} (hL : 0≤L) :
    ∃ C : ℝ,0<C ∧ ∀ {x Q : ℝ},2≤x → 1≤Real.log x →
    (∑ d∈Icc 2 ⌊min Q ((Real.log x)^L)⌋₊,(d.totient:ℝ)⁻¹*primitivePsiEnergy x d)≤
      C*x^2/(Real.log x)^A := by
  obtain ⟨C,hC,H⟩ := sum_smallConductor_psiChar_le A hL
  let K := Real.log 4+4
  have hk : 0<K := by dsimp [K];positivity
  refine ⟨K*C,by positivity,?_⟩
  intro x Q hx hlog
  let F (d : ℕ) := univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)
  have hx₀ : 0≤x := by linarith
  have hb (d : ℕ) : primitivePsiEnergy x d≤K*x*∑ χ∈F d,‖psiChar x χ‖ := by
    rw [mul_sum];apply sum_le_sum;intro χ _
    simpa only [sq] using mul_le_mul_of_nonneg_right (norm_psiChar_le_const_mul_self hx₀ χ) (norm_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (H (Q:=Q) hx hlog) (mul_nonneg hk.le hx₀)
  rw [mul_sum] at hh
  apply le_trans _ (hh.trans_eq (by ring))
  apply sum_le_sum;intro d _
  exact (mul_le_mul_of_nonneg_left (hb d) (by positivity : 0≤(d.totient:ℝ)⁻¹)).trans_eq (by dsimp only [F];ring)

end AnalyticNumberTheory.PrimeDistribution
