import AnalyticNumberTheory.DirichletLFunctions.SmoothedFunctionalEquation
import AnalyticNumberTheory.AnalyticTools.Gamma.GaussianRatios

/-!
# Conductor-scaled Gaussian kernels on the critical line

With `X = sqrt(q(1+|t|))`, the kernel on displacement `c` is bounded by
`C(c) X^c exp(-v²/2)` for every conductor, parity, and real height.
-/

open Real Complex MeasureTheory
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Length of a balanced Dirichlet polynomial at critical height `t`. -/
noncomputable def conductorLength (q : ℕ) (t : ℝ) := Real.sqrt ((q:ℝ)*(1+|t|))

theorem one_le_conductorLength {q : ℕ} [NeZero q] (t : ℝ) : 1≤conductorLength q t := by
  apply Real.one_le_sqrt.mpr
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) (by linarith [abs_nonneg t])

theorem conductorLength_rpow (q : ℕ) (t c : ℝ) :
    (conductorLength q t)^c=(q:ℝ)^(c/2)*(1+|t|)^(c/2) := by
  rw [conductorLength,Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity),Real.mul_rpow (by positivity) (by positivity)]
  ring_nf

/-- The gamma and conductor weight normalized by its central gamma factor. -/
noncomputable def characterGaussianKernel {q : ℕ} (χ : DirichletCharacter ℂ q) (t c v : ℝ) :=
  let s := (1/2:ℂ)+t*I
  let w := (c:ℂ)+v*I
  (χ.gammaFactor (s+w)/χ.gammaFactor s*Complex.exp (w^2)/w)*conductorWeight q w

/-- Uniform Gaussian domination across the two possible archimedean parities. -/
theorem norm_characterGaussianKernel_le {c : ℝ} (hc : -(1/2:ℝ)<c) (hc₀ : c≠0) :
    ∃ C : ℝ,0<C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t v : ℝ),
      ‖characterGaussianKernel χ t c v‖≤C*(conductorLength q t)^c*Real.exp (-v^2/2) := by
  obtain ⟨C₀,hC₀,H₀⟩ := norm_GammaReal_gaussian_ratio (σ:=1/2) (by norm_num) (by linarith) hc₀
  obtain ⟨C₁,hC₁,H₁⟩ := norm_GammaReal_gaussian_ratio (σ:=3/2) (by norm_num) (by linarith) hc₀
  refine ⟨max C₀ C₁,lt_of_lt_of_le hC₀ (le_max_left ..),?_⟩
  intro q _ χ t v
  let s := (1/2:ℂ)+t*I
  let w := (c:ℂ)+v*I
  have h (b C : ℝ) (hb : (parityExp χ:ℝ)=b) (hC : C≤max C₀ C₁)
      (hh : ‖Complex.Gammaℝ (((1/2+b+c:ℝ):ℂ)+(t+v:ℝ)*I)/Complex.Gammaℝ (((1/2+b:ℝ):ℂ)+t*I)*
               Complex.exp (w^2)/w‖≤C*(1+|t|)^(c/2)*Real.exp (-v^2/2)) :
      ‖characterGaussianKernel χ t c v‖≤max C₀ C₁*(conductorLength q t)^c*Real.exp (-v^2/2) := by
    have hc₁ : (parityExp χ:ℂ)=(b:ℂ) := by exact_mod_cast hb
    change ‖(χ.gammaFactor (s+w)/χ.gammaFactor s*Complex.exp (w^2)/w)*conductorWeight q w‖≤_
    rw [norm_mul,norm_conductorWeight,gammaFactor_eq_Gammaℝ,gammaFactor_eq_Gammaℝ,hc₁,
      show s+w+(b:ℂ)=((1/2+b+c:ℝ):ℂ)+(t+v:ℝ)*I by dsimp [s,w]; push_cast; ring,
      show s+(b:ℂ)=((1/2+b:ℝ):ℂ)+t*I by dsimp [s]; push_cast; ring,
      show w.re=c by simp [w],conductorLength_rpow]
    apply (mul_le_mul_of_nonneg_right hh (by positivity)).trans
    calc _ = C*((q:ℝ)^(c/2)*(1+|t|)^(c/2))*Real.exp (-v^2/2) := by ring
         _ ≤ _ := by gcongr
  rcases χ.even_or_odd with he|ho
  · apply h 0 C₀ (by simp [parityExp_of_even he]) (le_max_left ..)
    simpa only [add_zero] using H₀ t v
  · apply h 1 C₁ (by simp [parityExp_of_odd ho]) (le_max_right ..)
    rw [show (1/2:ℝ)+1=3/2 by norm_num]
    exact H₁ t v

/-- The normalized kernel is continuous in the integration variable on
every admissible nonzero displacement. -/
theorem continuous_characterGaussianKernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {c : ℝ} (hc : -(1/2:ℝ)<c) (hc₀ : c≠0) : Continuous (characterGaussianKernel χ t c) := by
  let s := (1/2:ℂ)+t*I
  let w (v : ℝ) := (c:ℂ)+v*I
  have hcont : Continuous w := by dsimp [w]; fun_prop
  have hn (v) : w v≠0 := by intro h; apply hc₀; simpa [w] using congrArg Complex.re h
  have hG : Continuous (fun v => χ.gammaFactor (s+w v)) := by
    simp_rw [gammaFactor_eq_Gammaℝ]
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_GammaReal _).continuousAt.comp
    · dsimp [s,w]; fun_prop
    · simp [s,w]; linarith [Nat.cast_nonneg (α:=ℝ) (parityExp χ)]
  exact (((hG.div_const _).mul (Complex.continuous_exp.comp (hcont.pow 2))).div hcont hn).mul
    (differentiable_conductorWeight.continuous.comp hcont)

end AnalyticNumberTheory.DirichletLFunctions
