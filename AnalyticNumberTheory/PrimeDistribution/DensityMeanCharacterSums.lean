import AnalyticNumberTheory.PrimeDistribution.PrimitiveConductorBlockSums
import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyZeroPowerSum

/-!
# The zero-density reduction of mean character sums

The reciprocal-height estimate follows unconditionally from Ingham's theorem.
The remaining analytic input is a single-character truncated explicit bound.
The resulting conductor-block estimate holds for the supremum of every
individual character, and the upper conductor endpoint can be shortened.
-/
noncomputable section
open Finset Real Complex
open scoped Classical
namespace AnalyticNumberTheory.PrimeDistribution

/-- Reciprocal-ordinate zero sum for every conductor cutoff and positive
height window, including zeros of small imaginary part. -/
theorem primitive_family_zero_reciprocal_sum :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ}{x T : ℝ},1≤Q → 2≤x → 1≤T →
      primitiveFamilyZeroWeight Q T (fun z => x^z.re/(1+|z.im|)) ≤
        C*(Real.sqrt x*(Q:ℝ)^2*(1+Real.log (T+1))+x*(Q:ℝ)^(2/3:ℝ))*
          Real.log x*(1+Real.log ((Q:ℝ)*(T+1)))^8 := by
  obtain ⟨D,hD,H⟩ := primitive_family_zero_power_sum
  exact ⟨6*D,by positivity,fun {Q x T} hQ hx hT =>
    primitive_zero_reciprocal_height_of_power_sum hQ hx hT hD (fun u hu => H hQ hu hx)⟩

private lemma log_ge_one_of_four_le {x : ℝ} (hx : 4≤x) : 1≤Real.log x := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<2*2) (show (2:ℝ)*2≤x by linarith)
  rw [Real.log_mul (by norm_num) (by norm_num)] at h
  linarith [Real.log_two_gt_d9]

/-- At the explicit-formula cutoff √x the term growing linearly in height
carries ten logarithms; the cube-root term carries nine. -/
theorem primitive_dyadic_zero_reciprocal_sum :
    ∃ C : ℝ,0<C ∧ ∀{Q : ℕ}{x : ℝ},1≤Q → 4≤x → (Q:ℝ)≤Real.sqrt x →
      primitiveFamilyZeroWeight (2*Q) (Real.sqrt x) (fun z => x^z.re/(1+|z.im|)) ≤
        C*(Real.sqrt x*(Q:ℝ)^2*(Real.log x)^10+x*(Q:ℝ)^(2/3:ℝ)*(Real.log x)^9) := by
  obtain ⟨D,hD,H⟩ := primitive_family_zero_reciprocal_sum
  refine ⟨8*D*3^8,by positivity,?_⟩
  intro Q x hQ hx hQx
  let L := Real.log x
  have hL : 1≤L := log_ge_one_of_four_le hx
  have hL₀ : 0≤L := by linarith
  have hs : 2≤Real.sqrt x := (Real.le_sqrt_of_sq_le (by nlinarith))
  have hsq := Real.sq_sqrt (show 0≤x by linarith)
  have hsx : Real.sqrt x+1≤x := by nlinarith only [hs,hsq,sq_nonneg (Real.sqrt x-2)]
  have h₁ : 1+Real.log (Real.sqrt x+1)≤2*L := by
    linarith only [hL,Real.log_le_log (by linarith : 0<Real.sqrt x+1) hsx]
  have hr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hqx : 2*(Q:ℝ)*(Real.sqrt x+1)≤4*x := by
    nlinarith only [mul_le_mul hQx (show Real.sqrt x+1≤2*Real.sqrt x by linarith) (by linarith) (Real.sqrt_nonneg x),hsq]
  have hp : 0<2*(Q:ℝ)*(Real.sqrt x+1) := by positivity
  have hlog := Real.log_le_log hp hqx
  rw [Real.log_mul (by norm_num) (by linarith : x≠0)] at hlog
  have h₂ : 1+Real.log (2*(Q:ℝ)*(Real.sqrt x+1))≤3*L := by
    dsimp only [L] at *;linarith only [hL,hlog,Real.log_le_log (by norm_num : (0:ℝ)<4) hx]
  have h₂₀ : 0≤1+Real.log (2*(Q:ℝ)*(Real.sqrt x+1)) := by
    have ha := one_le_mul_of_one_le_of_one_le (by linarith : 1≤2*(Q:ℝ)) (by linarith : 1≤Real.sqrt x+1)
    linarith [Real.log_nonneg ha]
  have hpow : (2*(Q:ℝ))^(2/3:ℝ)≤2*(Q:ℝ)^(2/3:ℝ) := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by norm_num : (2/3:ℝ)≤1)
    simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_right h (by positivity : 0≤(Q:ℝ)^(2/3:ℝ))
  have he := H (Q:=2*Q) (T:=Real.sqrt x) (by omega) (by linarith : 2≤x) (by linarith)
  push_cast at he
  apply he.trans
  have hm := add_le_add (mul_le_mul_of_nonneg_left h₁ (show 0≤Real.sqrt x*(2*(Q:ℝ))^2 by positivity))
    (mul_le_mul_of_nonneg_left hpow (by linarith : 0≤x))
  have hh := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hD.le) hL₀)
    (pow_le_pow_left₀ h₂₀ h₂ 8) (by positivity) (by positivity)
  apply hh.trans
  change _≤8*D*3^8*(Real.sqrt x*(Q:ℝ)^2*L^10+x*(Q:ℝ)^(2/3:ℝ)*L^9)
  nlinarith only [mul_nonneg (show 0≤D*x*(Q:ℝ)^(2/3:ℝ) by positivity) (pow_nonneg hL₀ 9)]

private theorem maximal_psi_block_with_zeros (H : PrimitivePsiExplicitBound) :
    ∃ C : ℝ,0<C ∧ ∀ {Q R : ℕ} {x : ℝ},1≤Q → R≤2*Q → 4≤x → (Q:ℝ)≤Real.sqrt x →
      (∑q∈Ioc Q R,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,maximalPsiCharNorm x χ) ≤
        C*((Q:ℝ)*Real.sqrt x*(1+Real.log (2*(Q:ℝ)*x))^2+
          (6*(1+Real.log (2*(Q:ℝ)))/Q)*primitiveFamilyZeroWeight (2*Q) (Real.sqrt x) (fun z => x^z.re/(1+|z.im|))) := by
  obtain ⟨C,hC,HC⟩ := H
  refine ⟨C,hC,?_⟩;intro Q R x hQ hR hx hQx
  let w (z : ℂ) := x^z.re/(1+|z.im|)
  let M := Real.sqrt x*(1+Real.log (2*(Q:ℝ)*x))^2
  have hM : 0≤M := by dsimp [M];positivity
  have hw (z) : 0≤w z := by dsimp [w];positivity
  have hf (q : ℕ) (hq : q∈Ioc Q R) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
      maximalPsiCharNorm x χ≤ C*M+C*characterZeroWeight χ (Real.sqrt x) w := by
    apply csSup_le ((Set.nonempty_Icc.mpr (show 0≤x by linarith)).image _)
    rintro _ ⟨y,hy,rfl⟩
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hq
    have hqle : (q:ℝ)≤2*(Q:ℝ) := by exact_mod_cast hhi.trans hR
    have hp : 1≤(q:ℝ)*x := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hQ.trans hlo.le) (by linarith)
    have hl := Real.log_le_log (by linarith : 0<(q:ℝ)*x) (mul_le_mul_of_nonneg_right hqle (by linarith : 0≤x))
    apply (HC hx hy.1 hy.2 (by omega : 2≤q) (by linarith) χ hχ).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hp]) (add_le_add_right hl 1) 2) (Real.sqrt_nonneg _)) _) hC.le).trans_eq
    dsimp [M,w];ring
  exact (primitive_conductor_block_sum hQ hR (mul_nonneg hC.le hM) hC.le w hw
    (fun _ χ => maximalPsiCharNorm x χ) hf).trans_eq (by dsimp [M,w];ring)

/-- Density-method estimate on an arbitrary dyadic block of primitive conductors.
The endpoints of the character sums are maximized independently. -/
theorem primitive_dyadic_mean_of_explicit_bound (H : PrimitivePsiExplicitBound) :
    ∃ C : ℝ,0<C ∧ ∀{Q R : ℕ}{x : ℝ},1≤Q → R≤2*Q → 4≤x → (Q:ℝ)≤Real.sqrt x →
      (∑q∈Ioc Q R,(q.totient:ℝ)⁻¹*∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,maximalPsiCharNorm x χ) ≤
        C*(Real.sqrt x*Q*(Real.log x)^11+x*(Q:ℝ)^(-(1/3:ℝ))*(Real.log x)^10) := by
  obtain ⟨K,hK,HK⟩ := maximal_psi_block_with_zeros H
  obtain ⟨D,hD,HD⟩ := primitive_dyadic_zero_reciprocal_sum
  refine ⟨K*(9+12*D),by positivity,?_⟩;intro Q R x hQ hR hx hQx
  let L := Real.log x
  let A := Real.sqrt x*(Q:ℝ)*L^11
  let B := x*(Q:ℝ)^(-(1/3:ℝ))*L^10
  let Z := primitiveFamilyZeroWeight (2*Q) (Real.sqrt x) (fun z => x^z.re/(1+|z.im|))
  have hL : 1≤L := log_ge_one_of_four_le hx
  have hL₀ : 0≤L := by linarith
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hq₀ := zero_lt_one.trans_le hqr
  have hs : 2≤Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2Q : 2*(Q:ℝ)≤x := by nlinarith only [hQx,hs,Real.sq_sqrt (show 0≤x by linarith),sq_nonneg (Real.sqrt x-2)]
  have hQ' : 1≤2*(Q:ℝ) := by linarith
  have hqlog := Real.log_le_log (by linarith : 0<2*(Q:ℝ)) h2Q
  have hq : 1+Real.log (2*(Q:ℝ))≤2*L := by dsimp [L] at *;linarith
  have hqx : 1+Real.log (2*(Q:ℝ)*x)≤3*L := by rw [Real.log_mul (by positivity) (by linarith)];dsimp [L] at *;linarith
  have hxp := one_le_mul_of_one_le_of_one_le hQ' (show 1≤x by linarith)
  have hm : (Q:ℝ)*Real.sqrt x*(1+Real.log (2*(Q:ℝ)*x))^2≤9*A := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Real.log_nonneg hxp]) hqx 2)
      (show 0≤(Q:ℝ)*Real.sqrt x by positivity)
    dsimp only [A]
    nlinarith only [h,mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 2≤11)) (mul_nonneg (Nat.cast_nonneg (α:=ℝ) Q) (Real.sqrt_nonneg x))]
  have hz := HD hQ hx hQx
  have hZ : 0≤Z := by
    dsimp [Z,primitiveFamilyZeroWeight];apply sum_nonneg;intro i hi;positivity
  have hcoef : 6*(1+Real.log (2*(Q:ℝ)))/Q≤12*L/Q := by
    exact div_le_div_of_nonneg_right (by linarith) hq₀.le
  have hpow : (Q:ℝ)^(2/3:ℝ)/(Q:ℝ)=(Q:ℝ)^(-(1/3:ℝ)) := by
    rw [show -(1/3:ℝ)=2/3-1 by ring,Real.rpow_sub hq₀,Real.rpow_one]
  have hZ' : (6*(1+Real.log (2*(Q:ℝ)))/Q)*Z≤12*D*(A+B) := by
    apply (mul_le_mul hcoef hz hZ (by positivity)).trans_eq
    dsimp only [A,B,L] at *
    rw [←hpow]
    field_simp <;> ring
  have hB : 0≤B := by dsimp only [B];positivity
  apply (HK hQ hR hx hQx).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add hm hZ') hK.le).trans
  change _ ≤ K*(9+12*D)*(A+B)
  nlinarith only [mul_nonneg hK.le hB]

end AnalyticNumberTheory.PrimeDistribution
