import AnalyticNumberTheory.PrimeDistribution.CharacterTypeIMeans
import AnalyticNumberTheory.PrimeDistribution.InghamMomentBounds

/-! # Hybrid second moments of the Möbius mollifier on translated intervals -/
noncomputable section
open Real Complex Finset MeasureTheory
open scoped ArithmeticFunction.Moebius
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

/-- Möbius coefficients with the critical real weight and a common height translation. -/
def shiftedMobiusCoeff (v : ℝ) (n : ℕ) : ℂ := (μ n:ℂ)*(n:ℂ)^(-((1/2:ℂ)+v*I))

theorem shiftedMobiusCoeff_norm_sq {n : ℕ} (hn : 1≤n) (v : ℝ) :
    ‖shiftedMobiusCoeff v n‖^2 ≤ (n:ℝ)⁻¹ := by
  let s := (1/2:ℂ)+(v:ℂ)*I
  have hs : (-s).re=-(1/2:ℝ) := by simp [s]
  change ‖(μ n:ℂ)*(n:ℂ)^(-s)‖^2 ≤ _
  rw [norm_mul,mul_pow,Complex.norm_natCast_cpow_of_pos hn,hs,←Real.rpow_mul_natCast (Nat.cast_nonneg n),
    show -(1/2:ℝ)*(2:ℕ)=-1 by norm_num,Real.rpow_neg_one]
  exact mul_le_of_le_one_left (by positivity)
    ((pow_le_pow_left₀ (norm_nonneg _) (norm_moebius_complex_le n) 2).trans_eq (one_pow _))

theorem shiftedMobiusCoeff_sum (χ : ℕ→ℂ) (X : ℕ) (v t : ℝ) :
    (∑ n∈Icc 1 X,shiftedMobiusCoeff v n*χ n*(n:ℂ)^(-(I*(t:ℂ)))) =
      dirichletPoly (fun n => (μ n:ℂ)*χ n) X ((1/2:ℂ)+((v+t:ℝ):ℂ)*I) := by
  apply sum_congr rfl;intro n hn
  have hn₀ : (n:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hn).1
  rw [show -((1/2:ℂ)+((v+t:ℝ):ℂ)*I)=-((1/2:ℂ)+v*I)+(-(I*(t:ℂ))) by push_cast;ring,
    Complex.cpow_add _ _ hn₀]
  dsimp only [shiftedMobiusCoeff];ring

set_option maxHeartbeats 550000 in
/-- Translating the height origin changes only the phases of the shared
Möbius coefficients, so the hybrid mean value applies on every translate. -/
theorem character_mollifier_translated_mean {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ}
    {L X : ℕ} {H : ℝ} (hm : CharacterHybridMean F χ L H) (hH : 0≤H) (hX : 1≤X) (u : ℝ) :
    (∑ i∈F,∫ t in u..(u+L),‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖^2)
      ≤ π^3*((X:ℝ)+H)*(1+Real.log X) := by
  let a := shiftedMobiusCoeff u
  have h := hm X hX a
  have hrow (i : ι) :
      (∫ t in (0:ℝ)..L,‖∑ n∈Icc 1 X,a n*χ i n*(n:ℂ)^(-(I*(t:ℂ)))‖^2) =
        ∫ t in u..(u+L),‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖^2 := by
    let f (t : ℝ) := ‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖^2
    have ht := shiftedMobiusCoeff_sum (χ i) X u
    change (∫ t in (0:ℝ)..L,‖∑ n∈Icc 1 X,shiftedMobiusCoeff u n*χ i n*(n:ℂ)^(-(I*(t:ℂ)))‖^2)=_
    simp_rw [ht]
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a:=(0:ℝ)) (b:=(L:ℝ)) f u
  have he : (∑ n∈Icc 1 X,‖a n‖^2)≤1+Real.log X := by
    apply le_trans (b:=∑ n∈Icc 1 X,(n:ℝ)⁻¹)
    · apply sum_le_sum;intro n hn
      exact shiftedMobiusCoeff_norm_sq (mem_Icc.mp hn).1 u
    · simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log X
  simp_rw [hrow] at h
  exact h.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- Dyadic input to Ingham's integral estimate when the hybrid cost
of each window scales linearly with its height and the mollifier length. -/
theorem character_mollifier_dyadic_mean {ι : Type*} {F : Finset ι} {χ : ι→ℕ→ℂ}
    {L X : ℕ} (hm : ∀ m : ℕ, 1≤m → CharacterHybridMean F χ (m*L) ((m:ℝ)*X))
    (hX : 1≤X) (j : ℕ) :
    (∑ i∈F,∫ t in -(2^j*(L:ℝ))..2^j*L,‖dirichletPoly (fun n => (μ n:ℂ)*χ i n) X ((1/2:ℂ)+t*I)‖^2)
      ≤ (3*π^3*X*(1+Real.log X))*2^j*((j:ℝ)+1) := by
  let m := 2^(j+1)
  let T := (2:ℝ)^j*L
  have hn : 1≤m := Nat.one_le_pow _ _ (by decide)
  have hm' : (m:ℝ)=2^j*2 := by simp [m,pow_succ]
  have hx : (1:ℝ)≤X := by exact_mod_cast hX
  have h := character_mollifier_translated_mean (hm m hn) (by positivity) hX (-T)
  have hend : -T+((m*L:ℕ):ℝ)=T := by push_cast;rw [hm'];dsimp [T];ring
  rw [hend,hm'] at h
  apply h.trans
  have hp : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hL : 0≤1+Real.log X := by linarith [Real.log_nonneg hx]
  calc _ ≤ π^3*((2:ℝ)^j*X+2^j*2*X)*(1+Real.log X) := by
            gcongr
            exact le_mul_of_one_le_left (Nat.cast_nonneg _) hp
       _ = (3*π^3*X*(1+Real.log X))*2^j := by ring
       _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) j])

end AnalyticNumberTheory.PrimeDistribution
