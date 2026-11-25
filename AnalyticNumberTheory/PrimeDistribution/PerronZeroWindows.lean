import AnalyticNumberTheory.PrimeDistribution.SignedPerronWeights

/-! # Moving both the height and the endpoint in a character's Perron zero sum -/
noncomputable section
open Finset Real Complex AnalyticNumberTheory.DirichletLFunctions
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

theorem sum_characterZeroMultiplicity_eq_zeroCountL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∑z∈characterStripZeros χ T,(characterZeroMultiplicity χ z:ℝ)=(zeroCountL χ T:ℝ) := by
  simp [characterStripZeros,characterZeroMultiplicity,zeroCountL,NeZero.ne q,Nat.cast_sum]

/-- Moving the arithmetic endpoint costs at most its displacement times
the total number of zeros, with multiplicity. -/
theorem norm_characterPerronZeroSum_sub_endpoint {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x y : ℝ} (hx : 1≤x) (hy : 1≤y) (T : ℝ) :
    ‖characterPerronZeroSum χ x T-characterPerronZeroSum χ y T‖ ≤
      (zeroCountL χ T:ℝ)*|x-y| := by
  rw [←sum_characterZeroMultiplicity_eq_zeroCountL, sum_mul]
  unfold characterPerronZeroSum
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum;intro z hz
  obtain ⟨hβ,hβ',_⟩ := (mem_characterStripZeros _).mp hz
  rw [←mul_sub,norm_mul,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_perronDifferenceWeight_sub_le hx hy hβ hβ'.le) (Nat.cast_nonneg _)

/-- The regularized Perron sum vanishes at the arithmetic endpoint one. -/
@[simp] theorem characterPerronZeroSum_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    characterPerronZeroSum χ 1 T=0 := by
  unfold characterPerronZeroSum
  apply sum_eq_zero;intro z hz
  have hz' : z≠0 := by intro he;simpa [he] using ((mem_characterStripZeros _).mp hz).1
  simp [perronDifferenceWeight_eq (by norm_num : (0:ℝ)<1) hz']

/-- The height error for a symmetric window of width at most one. The
factor (x+1)/T estimates the weight at the freshly admitted ordinates. -/
theorem norm_characterPerronZeroSum_sub_height {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {x T U : ℝ} (hx : 1≤x) (hT : 0<T) (htu : T≤U) (hut : U≤T+1) :
    ‖characterPerronZeroSum χ x U-characterPerronZeroSum χ x T‖ ≤
      ((x+1)/T)*(3*jensenUnitZeroDensityConst*Real.log ((q:ℝ)*(T+2))) := by
  let S := characterStripZeros χ T
  let V := characterStripZeros χ U
  let m (z : ℂ) : ℝ := characterZeroMultiplicity χ z
  let f (z : ℂ) := (characterZeroMultiplicity χ z:ℂ)*perronDifferenceWeight x z
  have hsub : S⊆V := by
    intro z hz;obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := (mem_characterStripZeros _).mp hz
    exact (mem_characterStripZeros _).mpr ⟨h₁,h₂,by linarith,h₄.trans htu,h₅⟩
  have hhi := zeroCountL_add_one_sub_le hχ hT.le
  rw [abs_of_nonneg hT.le] at hhi
  have hmono : (zeroCountL χ U:ℝ)≤zeroCountL χ (T+1) := by exact_mod_cast zeroCountL_mono χ hut
  have hm : ∑z∈V\S,m z ≤ 3*jensenUnitZeroDensityConst*Real.log ((q:ℝ)*(T+2)) := by
    have he := sum_sdiff hsub (f:=m)
    change (∑z∈V\S,m z)+(∑z∈characterStripZeros χ T,(characterZeroMultiplicity χ z:ℝ))=
      (∑z∈characterStripZeros χ U,(characterZeroMultiplicity χ z:ℝ)) at he
    simp only [sum_characterZeroMultiplicity_eq_zeroCountL] at he
    linarith
  have hf (z : ℂ) (hz : z∈V\S) : ‖f z‖≤((x+1)/T)*m z := by
    obtain ⟨hzv,hzs⟩ := mem_sdiff.mp hz
    obtain ⟨h₁,h₂,_,_,h₅⟩ := (mem_characterStripZeros _).mp hzv
    have hi : T≤|z.im| := by
      by_contra! h
      exact hzs ((mem_characterStripZeros _).mpr ⟨h₁,h₂,(abs_lt.mp h).1.le,(abs_lt.mp h).2.le,h₅⟩)
    have hn : z≠0 := by intro he;simpa [he] using h₁
    have hr : x^z.re≤x := by simpa using Real.rpow_le_rpow_of_exponent_le hx h₂.le
    have hw : ‖perronDifferenceWeight x z‖ ≤(x+1)/T := by
      rw [perronDifferenceWeight_eq (by linarith) hn,norm_div]
      apply div_le_div₀ (by linarith)
      · have hh := norm_sub_le ((x:ℂ)^z) 1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<x),norm_one] at hh;linarith
      · exact hT
      · exact hi.trans (Complex.abs_im_le_norm z)
    change ‖(characterZeroMultiplicity χ z:ℂ)*perronDifferenceWeight x z‖≤_
    rw [norm_mul,Complex.norm_natCast,mul_comm ((x+1)/T)]
    exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
  have hs := sum_sdiff hsub (f:=f)
  change ‖(∑z∈V,f z)-(∑z∈S,f z)‖≤_
  rw [←hs,add_sub_cancel_right]
  calc _ ≤ ∑z∈V\S,‖f z‖ := norm_sum_le _ _
       _ ≤ ∑z∈V\S,((x+1)/T)*m z := sum_le_sum hf
       _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left hm (by positivity)

end AnalyticNumberTheory.PrimeDistribution
