import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovMaximal
import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradovDensityMethod

/-! # Primitive conductors and independent endpoints in arithmetic progressions -/
noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- The ordinary prime number theorem retains its logarithmic saving if the
endpoint is allowed to vary anywhere below x. -/
theorem abs_psi_sub_id_maximal_le_log_power (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ {x y : ℝ}, 4≤x → 0≤y → y≤x →
      |Chebyshev.psi y-y| ≤ C*x/(Real.log x)^k := by
  obtain ⟨K,hK,H⟩ := abs_psi_sub_id_le_log_power (k:ℝ)
  let B := Real.log 4+5
  have hB : 0<B := by dsimp [B];positivity
  let C := (B*(k.factorial:ℝ)+K)*(2:ℝ)^k
  have hfac : B*(k.factorial:ℝ)*(2:ℝ)^k≤C := by dsimp [C];gcongr;linarith
  have hK' : K*(2:ℝ)^k≤C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hB.le (Nat.cast_nonneg _))) (by positivity)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro x y hx hy hyx
  have hx₀ : 0<x := by linarith
  have hL : 0<Real.log x := Real.log_pos (by linarith)
  rw [le_div_iff₀ (pow_pos hL _)]
  by_cases hs : y≤Real.sqrt x
  · have hψ : |Chebyshev.psi y-y|≤B*Real.sqrt x := by
      have hn : 0≤Chebyshev.psi y := sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      have hh := Chebyshev.psi_le_const_mul_self hy
      apply le_trans _ (mul_le_mul_of_nonneg_left hs hB.le);dsimp [B];rw [abs_le];constructor <;> nlinarith [mul_nonneg hy (Real.log_nonneg (by norm_num : (1:ℝ)≤4))]
    have hlog := Real.pow_div_factorial_le_exp (Real.log x/2) (by positivity) k
    have he : Real.exp (Real.log x/2)=Real.sqrt x := by rw [←Real.log_sqrt hx₀.le,Real.exp_log (Real.sqrt_pos.mpr hx₀)]
    rw [he,div_le_iff₀ (by positivity),div_pow,div_le_iff₀ (by positivity)] at hlog
    apply (mul_le_mul hψ hlog (pow_nonneg hL.le k) (by positivity)).trans
    calc _ = (B*(k.factorial:ℝ)*2^k)*x := by linear_combination B*(k.factorial:ℝ)*2^k*Real.sq_sqrt hx₀.le
         _ ≤ _ := mul_le_mul_of_nonneg_right hfac hx₀.le
  have hy₂ : 2≤y := ((Real.le_sqrt (by norm_num) hx₀.le).mpr (by linarith : (2:ℝ)^2≤x)).trans (le_of_not_ge hs)
  have hyL := Real.log_le_log (Real.sqrt_pos.mpr hx₀) (le_of_not_ge hs)
  rw [Real.log_sqrt hx₀.le] at hyL
  have hpow := pow_le_pow_left₀ hL.le (by linarith : Real.log x≤2*Real.log y) k
  rw [mul_pow] at hpow
  have hh := H hy₂
  rw [Real.rpow_natCast,le_div_iff₀ (pow_pos (Real.log_pos (by linarith)) _)] at hh
  calc _ ≤ |Chebyshev.psi y-y| *(2^k*(Real.log y)^k) := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
       _ = (|Chebyshev.psi y-y| *(Real.log y)^k)*2^k := by ring
       _ ≤ (K*x)*2^k := mul_le_mul_of_nonneg_right (hh.trans (mul_le_mul_of_nonneg_left hyx hK.le)) (by positivity)
       _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hK' hx₀.le]

/-- For one modulus the supremum over both residue classes and endpoints is
bounded by the ordinary prime number theorem and the separate maximal
Chebyshev sums attached to primitive characters of divisors of the modulus. -/
theorem maximalPsiAPError_le_primitive_conductors {q : ℕ} (hq : 1≤q)
    {x E : ℝ} (hx : 1≤x) (hE : ∀y, 0≤y → y≤x → |Chebyshev.psi y-y|≤E) :
    maximalPsiAPError x q ≤ (q.totient:ℝ)⁻¹*E+(Real.log q/Real.log 2)*Real.log x+
      (q.totient:ℝ)⁻¹*(∑d∈q.divisors with 2≤d,∑χ : DirichletCharacter ℂ d with χ.IsPrimitive,maximalPsiCharNorm x χ) := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  let r := (Real.log q/Real.log 2)*Real.log x
  let f (d : ℕ) := ∑χ : DirichletCharacter ℂ d with χ.IsPrimitive,maximalPsiCharNorm x χ
  have hφ : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hx₀ : 0≤x := zero_le_one.trans hx
  have hlogq : 0≤Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hr : 0≤r := by dsimp [r];positivity [Real.log_nonneg hx]
  have hf (d : ℕ) : 0≤f d := sum_nonneg (fun χ _ => (norm_nonneg _).trans (norm_psiChar_le_maximalPsiCharNorm χ hx₀ le_rfl))
  have hF : 0≤(q.totient:ℝ)⁻¹*(∑d∈q.divisors with 2≤d,f d) := mul_nonneg (by positivity) (sum_nonneg (fun d _=>hf d))
  unfold maximalPsiAPError
  apply csSup_le ((Set.nonempty_Icc.mpr hx₀).image _)
  rintro u ⟨y,⟨hy,hyx⟩,rfl⟩
  change maxPsiAPError y q≤_
  rw [maxPsiAPError,dite_eq_left hq,sup'_le_iff]
  intro a ha
  by_cases hy₁ : 1≤y
  · have hab := abs_psiAP_sub_div_totient_le_sum_chars hy₁ hq (mem_filter.mp ha).2
    have hers : ({(1:DirichletCharacter ℂ q)}ᶜ : Finset _)=univ.erase 1 := by ext χ;simp
    rw [hers] at hab
    have hry : (Real.log q/Real.log 2)*Real.log y≤r :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hyx) (by positivity)
    have hχ (χ : DirichletCharacter ℂ q) : ‖psiChar y χ‖≤r+‖psiChar y χ.primitiveCharacter‖ := by
      have hg := norm_sub_le (psiChar y χ-psiChar y χ.primitiveCharacter) (-psiChar y χ.primitiveCharacter)
      simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hg
      have hdiff : ‖psiChar y χ-psiChar y χ.primitiveCharacter‖≤r :=
        (norm_psiChar_sub_primitive_le hy₁ hq χ).trans hry
      exact hg.trans (add_le_add hdiff (le_refl _))
    have hb := sum_le_sum (s:=univ.erase (1:DirichletCharacter ℂ q)) (fun χ _=>hχ χ)
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ _),card_univ] at hb
    have he : Fintype.card (DirichletCharacter ℂ q)=q.totient := by rw [Fintype.card_eq_nat_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    rw [he,Nat.cast_sub (Nat.totient_pos.mpr hq),Nat.cast_one] at hb
    have hprim := sum_erase_one_norm_psiChar_primitive_le (x:=y) hq
    have hmax : (∑d∈q.divisors with 2≤d,∑χ : DirichletCharacter ℂ d with χ.IsPrimitive,‖psiChar y χ‖)≤
        ∑d∈q.divisors with 2≤d,f d :=
      sum_le_sum (fun _ _=>sum_le_sum (fun χ _=>norm_psiChar_le_maximalPsiCharNorm χ hy hyx))
    change _≤(q.totient:ℝ)⁻¹*E+r+(q.totient:ℝ)⁻¹*_
    apply hab.trans
    calc _ ≤ (q.totient:ℝ)⁻¹*(E+(q.totient:ℝ)*r+∑d∈q.divisors with 2≤d,f d) := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           linarith only [hb,hprim,hmax,hry,hE y hy hyx]
         _ = _ := by field_simp <;> rfl
  · have hfl : ⌊y⌋₊=0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hy₁)
    have hψ : Chebyshev.psi y=0 := by simp [Chebyshev.psi,hfl]
    have hyE := hE y hy hyx
    rw [hψ,zero_sub,abs_neg,abs_of_nonneg hy] at hyE
    simp only [psiAP,hfl];simp
    rw [abs_of_nonneg (div_nonneg hy hφ.le),div_eq_inv_mul]
    linarith only [mul_le_mul_of_nonneg_left hyE (inv_nonneg.mpr hφ.le),hr,hF]

end AnalyticNumberTheory.PrimeDistribution
