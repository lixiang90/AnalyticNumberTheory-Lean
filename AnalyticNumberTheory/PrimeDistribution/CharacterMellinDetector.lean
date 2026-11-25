import AnalyticNumberTheory.PrimeDistribution.CharacterRieszInversion
import AnalyticNumberTheory.PrimeDistribution.InghamDetectorPolynomial
import AnalyticNumberTheory.DirichletSeries.RieszZeroShift
import AnalyticNumberTheory.DirichletLFunctions.AbsolutePolynomialBounds
import AnalyticNumberTheory.DirichletLFunctions.ZeroFreeRegion

/-! # A Mellin zero detector for nonprincipal Dirichlet characters -/
noncomputable section
open Complex Real Finset MeasureTheory
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Move the sixth Riesz kernel to the critical line at any zero of a nonprincipal
character in the right half of the critical strip, including real zeros. -/
theorem character_riesz_shift {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1)
    (X : ℕ) {Y : ℝ} (hY : 1≤Y) {ρ : ℂ} (hβ : 1/2<ρ.re) (hβ' : ρ.re<1)
    (hz : χ.LFunction ρ=0) :
    (∫ t : ℝ, characterRieszKernel χ X 6 ρ Y (2+t*I)) =
      ∫ t : ℝ, characterRieszKernel χ X 6 ρ Y (((1/2-ρ.re:ℝ):ℂ)+t*I) := by
  let G (w : ℂ) := mollifiedLFunction χ X (ρ+w)
  have hshift : Differentiable ℂ (fun w : ℂ => ρ+w) := by fun_prop
  have hG : Differentiable ℂ G :=
    ((DirichletCharacter.differentiable_LFunction hχ).mul
      (differentiable_dirichletPoly _ X)).comp hshift
  have h₀ : G 0=0 := by simp [G,mollifiedLFunction,hz]
  let B := (q:ℝ)+48*(q:ℝ)^2+2
  have hB : 0≤B := by dsimp [B];positivity
  apply riesz_six_shift_at_zero (G:=G) (U:=|ρ.im|+2) (C:=4*B*(2*Real.sqrt X)) hG h₀
    (by linarith) (by linarith) hY (by positivity)
  intro x hx t ht
  let s := ρ+((x:ℂ)+t*I)
  have hs : 1/2≤s.re := by simp [s];linarith [hx.1]
  have hi : |s.im|+2≤2*|t| := by
    have him : s.im=ρ.im+t := by simp [s]
    rw [him];linarith [abs_add_le ρ.im t]
  have H := norm_LFunction_re_ge_half_le hχ hs
  have hP := norm_moebiusCharPoly_le (N:=X) χ hs
  change ‖χ.LFunction s*dirichletPoly _ X s‖ ≤ _
  rw [norm_mul]
  apply (mul_le_mul H hP (norm_nonneg _) (by positivity)).trans
  change B*(|s.im|+2)^2*(2*Real.sqrt X) ≤ _
  calc _ ≤ B*(2*|t|)^2*(2*Real.sqrt X) := by gcongr
       _ = _ := by ring

private theorem split_sum {q X : ℕ} (χ : DirichletCharacter ℂ q) (hX : 1≤X)
    {Y : ℝ} (hY : 1≤Y) (ρ : ℂ) :
    (∑ n∈Icc 1 ⌊Y⌋₊,(χ n*inghamDetectorCoeff X n)*(n:ℂ)^(-ρ)*(inghamRieszWeight 6 Y n:ℂ)) =
      (inghamRieszWeight 6 Y 1:ℂ) + ∑ n∈Ioc X ⌊Y⌋₊,
        inghamRieszCoeff X Y n*χ n*(n:ℂ)^(-ρ) := by
  have hN₁ := (Nat.one_le_floor_iff _).mpr hY
  by_cases hN : X≤⌊Y⌋₊
  · have hu : Icc 1 ⌊Y⌋₊=Icc 1 X ∪ Ioc X ⌊Y⌋₊ := by ext n;simp;omega
    have hd : Disjoint (Icc 1 X) (Ioc X ⌊Y⌋₊) := disjoint_left.mpr (by
      intro n hn hm;simp only [mem_Icc,mem_Ioc] at hn hm;omega)
    rw [hu,sum_union hd]
    congr 1
    · rw [sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hX⟩)]
      · simp [inghamDetectorCoeff_small hX]
      · intro n hn hn1;simp [inghamDetectorCoeff_small (mem_Icc.mp hn).2,hn1]
    · apply sum_congr rfl;intro n hn
      rw [inghamRieszCoeff,ite_eq_left (mem_Ioc.mp hn).2];ring
  · have hI : Ioc X ⌊Y⌋₊=∅ := by ext n;simp;omega
    rw [hI,sum_empty,add_zero,sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hN₁⟩)]
    · simp [inghamDetectorCoeff_small hX]
    · intro n hn hn₁
      have hnx : n≤X := by have h := (mem_Icc.mp hn).2;omega
      simp [inghamDetectorCoeff_small hnx,hn₁]

/-- Either a common finite Dirichlet polynomial is large or a Mellin integral
of the mollified L-function on the critical line is large. The cutoffs apply
uniformly to all nonprincipal characters and to zeros of either sign of ordinate. -/
theorem character_mellin_dichotomy {q X : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hX : 1≤X) {Y : ℝ} (hY : 16≤Y)
    {ρ : ℂ} (hβ : 1/2<ρ.re) (hβ' : ρ.re<1) (hz : χ.LFunction ρ=0) :
    1/4≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ n*(n:ℂ)^(-ρ)‖ ∨
    1/4≤‖(720/(2*π):ℂ)*(∫ t : ℝ, characterRieszKernel χ X 6 ρ Y (((1/2-ρ.re:ℝ):ℂ)+t*I))‖ := by
  obtain ⟨_,h⟩ := character_riesz_inversion χ X 6 (by decide) (ρ:=ρ) (by linarith) (Y:=Y) (by linarith)
  rw [character_riesz_shift hχ X (by linarith) hβ hβ' hz,split_sum χ hX (by linarith)] at h
  change (720/(2*π):ℂ)*_= _ at h
  rw [h]
  let w := inghamRieszWeight 6 Y 1
  have hw : 1/2≤w := by
    have hdiv : 1/Y≤1/16 := one_div_le_one_div_of_le (by norm_num) hY
    calc (1/2:ℝ) ≤ (15/16:ℝ)^6 := by norm_num
         _ ≤ w := pow_le_pow_left₀ (by norm_num) (by change 15/16≤1-(1:ℝ)/Y;linarith) _
  set S : ℂ := ∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*χ n*(n:ℂ)^(-ρ)
  change 1/4≤‖S‖ ∨ 1/4≤‖(w:ℂ)+S‖
  have hk := norm_sub_le ((w:ℂ)+S) S
  rw [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤w)] at hk
  by_cases hs : 1/4≤‖S‖
  · exact Or.inl hs
  · exact Or.inr (by linarith)

end AnalyticNumberTheory.PrimeDistribution
