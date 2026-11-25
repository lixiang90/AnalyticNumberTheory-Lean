import AnalyticNumberTheory.RiemannZeta.FourthMomentContourIntegrand
import AnalyticNumberTheory.DirichletLFunctions.CriticalConductorBound
import AnalyticNumberTheory.RiemannZeta.FourthMomentFrequencies
import AnalyticNumberTheory.RiemannZeta.FourthMomentReflection
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleInterpolation

/-!
# The horizontal edges of the fourth-moment contour

Convexity for zeta and the divisor-polynomial bound control the critical
edge. A rectangle with larger height range then transfers bounds on the
two vertical lines to each of the two horizontal contour segments.
-/

open Complex Real Set Filter
open scoped ComplexConjugate
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.RiemannZeta

/-- The analytic cross term is complex differentiable off the real axis. -/
theorem differentiableAt_fourthMomentCrossTerm (N : ℕ) {s : ℂ} (ht : s.im≠0) :
    DifferentiableAt ℂ (fourthMomentCrossTerm N) s := by
  have hs : s≠1 := fun he => ht (by simp [he])
  have hP := differentiable_divisorPolynomial N
  have hD : DifferentiableAt ℂ (fun z => divisorPolynomial N (1-z)) s :=
    (hP _).comp s (by fun_prop)
  unfold fourthMomentCrossTerm fourthMomentError
  exact ((((differentiableAt_riemannZeta hs).pow 2).sub (hP s)).sub
    (((analyticAt_riemannDualGamma ht).differentiableAt.pow 2).mul hD)).mul hD

/-- Pointwise control on the left edge for every short divisor polynomial. -/
theorem fourthMomentCrossTerm_critical_edge :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ} {N : ℕ} {s : ℂ}, 4≤T → 1≤N → (N:ℝ)≤T →
      s.re=1/2 → s.im∈Icc (T/2) (3*T) →
      ‖fourthMomentCrossTerm N s‖≤C*T*(1+Real.log T)^3 := by
  obtain ⟨A,hA,H⟩ := AnalyticNumberTheory.DirichletLFunctions.norm_LFunction_critical_conductor_quarter
  refine ⟨2*A^4+10,by positivity,?_⟩
  intro T N s hT hN hNT hs ht
  have hT₁ : 1≤T := by linarith
  have hL := Real.log_nonneg hT₁
  have hN' : (1:ℝ)≤N := by exact_mod_cast hN
  have him : 0≤s.im := by linarith [ht.1]
  have hs' : (1/2:ℂ)+s.im*I=s := by rw [←Complex.re_add_im s]; simp [hs]
  have hz := H (1:DirichletCharacter ℂ 1) s.im
  simp only [DirichletCharacter.LFunction_modOne_eq,Nat.cast_one,one_mul,hs',abs_of_nonneg him] at hz
  have hz4 := pow_le_pow_left₀ (norm_nonneg _) hz 4
  rw [mul_pow,←Real.rpow_mul_natCast (by linarith : 0≤1+s.im),show (1/4:ℝ)*(4:ℕ)=1 by norm_num,Real.rpow_one] at hz4
  have hz4' : ‖riemannZeta s‖^4 ≤ 4*A^4*T := hz4.trans
    ((mul_le_mul_of_nonneg_left (by linarith [ht.2] : 1+s.im≤4*T) (by positivity : 0≤A^4)).trans_eq (by ring))
  have hp := norm_divisorPolynomial_critical_sq_le hN s.im
  rw [hs'] at hp
  have hlog := Real.log_le_log (by linarith : 0<(N:ℝ)) hNT
  have hp' : ‖divisorPolynomial N s‖^2 ≤ 4*T*(1+Real.log T)^3 := by
    apply hp.trans; gcongr
  have href : 1-s=conj s := by apply Complex.ext <;> simp [hs] ; ring
  have hnorm : ‖divisorPolynomial N (1-s)‖=‖divisorPolynomial N s‖ := by
    rw [href,divisorPolynomial_conj,Complex.norm_conj]
  have hr : ‖fourthMomentError N s‖≤‖riemannZeta s‖^2+2*‖divisorPolynomial N s‖ := by
    unfold fourthMomentError
    apply (norm_sub_le ..).trans
    have h := norm_sub_le (riemannZeta s^2) (divisorPolynomial N s)
    rw [norm_mul,norm_pow,norm_riemannDualGamma_critical hs,one_pow,one_mul,hnorm]
    rw [norm_pow] at h
    linarith
  have hbig : T≤T*(1+Real.log T)^3 := by
    simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith : 1≤1+Real.log T) (n:=3)) (by linarith : 0≤T)
  rw [fourthMomentCrossTerm,norm_mul,hnorm]
  apply (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
  nlinarith only [hz4',hp',sq_nonneg (‖riemannZeta s‖^2-‖divisorPolynomial N s‖),
    mul_le_mul_of_nonneg_left hbig (by positivity : 0≤2*A^4)]

/-- Vertical edge bounds imply bounds on the two horizontal edges, uniformly in the truncation. -/
theorem fourthMomentCrossTerm_horizontal_edges {M : ℝ} (hM : 0≤M) :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ} {N : ℕ},4≤T → 1≤N → (N:ℝ)≤T →
      (∀ t∈Icc (T/2) (3*T), ‖fourthMomentCrossTerm N (2+t*I)‖≤M*T*(1+Real.log T)^3) →
      ∀ x∈Icc (1/2:ℝ) 2, ∀ y∈({T,2*T}:Set ℝ),
        ‖fourthMomentCrossTerm N ((x:ℂ)+y*I)‖≤C*T*(1+Real.log T)^3 := by
  obtain ⟨A,hA,HA⟩ := fourthMomentCrossTerm_critical_edge
  obtain ⟨B,hB,HB⟩ := fourthMomentCrossTerm_crude
  let K := A+M+64*B
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K*(1+2-(1/2:ℝ))^6,by positivity,?_⟩
  intro T N hT hN hNT hright x hx y hy
  let W := T*(1+Real.log T)^3
  have hT₁ : 1≤T := by linarith
  have hW : 1≤W := one_le_mul_of_one_le_of_one_le hT₁
    (one_le_pow₀ (by linarith [Real.log_nonneg hT₁]) (n:=3))
  have hf : DifferentiableOn ℂ (fourthMomentCrossTerm N) (Icc (1/2:ℝ) 2 ×ℂ Icc (T/2) (3*T)) :=
    fun z hz => (differentiableAt_fourthMomentCrossTerm N (by linarith [hz.2.1])).differentiableWithinAt
  have hV (z : ℂ) (hz : z.re=1/2 ∨ z.re=2) (ht : z.im∈Icc (T/2) (3*T)) :
      ‖fourthMomentCrossTerm N z‖≤K*W := by
    rcases hz with h|h
    · apply (HA hT hN hNT h ht).trans
      change A*T*(1+Real.log T)^3≤K*W
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith : A≤K) (by linarith : 0≤W)
    · have hh := hright z.im ht
      have he : (2:ℂ)+z.im*I=z := by rw [←Complex.re_add_im z]; simp [h]
      rw [he] at hh
      apply hh.trans
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith : M≤K) (by linarith : 0≤W)
  have hH (z : ℂ) (hz : z.re∈Icc (1/2:ℝ) 2) (ht : z.im=T/2 ∨ z.im=3*T) :
      ‖fourthMomentCrossTerm N z‖≤K*W*(T/2)^6 := by
    have ht' : z.im∈Icc (T/2) (3*T) := by rcases ht with h|h <;> constructor <;> linarith
    apply (HB hT hNT hz ht').trans
    have hcoeff : 64*B≤K*W :=
      (show 64*B≤K by dsimp [K]; linarith).trans (by simpa using mul_le_mul_of_nonneg_left hW hK.le)
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff (by positivity : 0≤T^6)]
  have hmid : T/2+T/2≤y ∧ y+T/2≤3*T := by
    rcases hy with h|h <;> change _ at h <;> rcases h with rfl <;> constructor <;> linarith
  have hh := norm_le_on_horizontal_segment 6 (by norm_num : (1/2:ℝ)<2) (by linarith : 0<T/2)
    hmid.1 hmid.2 (mul_nonneg hK.le (by linarith : 0≤W)) hf hV hH hx
  exact hh.trans_eq (by dsimp [W]; ring)

/-- Both contour sides for the fourth-moment truncation, assuming the right-edge pointwise bound. -/
theorem eventually_fourthMomentCrossTerm_horizontal_edges {M : ℝ} (hM : 0≤M)
    (hRight : ∀ᶠ T : ℝ in atTop, ∀ t∈Icc (T/2) (3*T),
      ‖fourthMomentCrossTerm ⌊T/(4*Real.pi)⌋₊ (2+t*I)‖≤M*T*(1+Real.log T)^3) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop, ∀ x∈Icc (1/2:ℝ) 2, ∀ y∈({T,2*T}:Set ℝ),
      ‖fourthMomentCrossTerm ⌊T/(4*Real.pi)⌋₊ ((x:ℂ)+y*I)‖≤C*T*(1+Real.log T)^3 := by
  obtain ⟨C,hC,H⟩ := fourthMomentCrossTerm_horizontal_edges hM
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (4*Real.pi),hRight] with T hT hright
  have hT' : 4≤T := by linarith [Real.pi_gt_three]
  have hN : 1≤⌊T/(4*Real.pi)⌋₊ := (Nat.one_le_floor_iff _).mpr ((one_le_div (by positivity)).mpr hT)
  exact H hT' hN ((Nat.floor_le (by positivity)).trans (div_le_self (by linarith) (by linarith [Real.pi_gt_three]))) hright

end AnalyticNumberTheory.RiemannZeta
