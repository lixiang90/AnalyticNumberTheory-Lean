import AnalyticNumberTheory.RiemannZeta.HurwitzRiemannSiegel
import AnalyticNumberTheory.RiemannZeta.RiemannSiegelCosine

/-!
# The Riemann–Siegel formula with the first real correction

Hardy's unit rotates the two sharp polynomials into the real cosine sum.
At the saddle its leading gamma phase combines with the Mordell phase to
give the alternating sign of the first correction.
-/
noncomputable section
open Real Complex Finset Set
open scoped ComplexConjugate
namespace AnalyticNumberTheory.RiemannZeta

/-- The ordinary zeta correction in terms of the cutoff and its fractional part. -/
theorem hurwitzFirstCorrection_one (s : ℂ) {x : ℝ} (hx : 1≤x) :
    hurwitzFirstCorrection 1 x s=(x:ℂ)^(-s)*
      Complex.exp (((Real.pi*(x^2-(⌊x⌋₊:ℝ)^2-7/8):ℝ):ℂ)*I)*
      (riemannSiegelCorrection (2*(x-⌊x⌋₊)):ℂ) := by
  have hn : 1≤⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hx)
  have hl : hurwitzSaddleFraction 1 x=x-⌊x⌋₊ := by
    rw [hurwitzSaddleFraction,Nat.floor_sub_one,Nat.cast_sub hn,Nat.cast_one];ring
  simp only [hurwitzFirstCorrection, hl]
  rw [show x+(x-⌊x⌋₊)-(⌊x⌋₊:ℝ)=2*(x-⌊x⌋₊) by ring]
  rw [show 2*x*(x-(⌊x⌋₊:ℝ))+(x-⌊x⌋₊)^2-(2*(x-⌊x⌋₊))^2/2=x^2-(⌊x⌋₊:ℝ)^2 by ring]

private theorem phase_correction_one {x t : ℝ} (hx : 1≤x) (ht : t=2*Real.pi*x^2) :
    Complex.exp ((hardyPhase t:ℂ)*I)*hurwitzFirstCorrection 1 x ((1/2:ℂ)+(t:ℂ)*I) =
      (((-1:ℝ)^(⌊x⌋₊+1)*(Real.sqrt x)⁻¹*riemannSiegelCorrection (2*(x-⌊x⌋₊)):ℝ):ℂ) := by
  let q := ⌊x⌋₊
  have hx' : 0<x := by linarith
  have hlog : Real.log t=Real.log (2*Real.pi)+2*Real.log x := by
    rw [ht,Real.log_mul (by positivity) (by positivity),Real.log_pow];norm_num
  have hφ : hardyPhase t-t*Real.log x+Real.pi*(x^2-(q:ℝ)^2-7/8)= -Real.pi*((q^2+1:ℕ):ℝ) := by
    rw [hardyPhase,hlog];push_cast;linear_combination -ht/2
  have hsq : (-1:ℂ)^(q^2)=(-1)^q := neg_one_pow_congr (by simp [sq,Nat.even_mul])
  have hphase : Complex.exp ((hardyPhase t:ℂ)*I)*Complex.exp (I*((-Real.log x:ℝ):ℂ)*t)*
      Complex.exp (((Real.pi*(x^2-(q:ℝ)^2-7/8):ℝ):ℂ)*I)=(-1:ℂ)^(q+1) := by
    rw [←Complex.exp_add,←Complex.exp_add]
    have he : (hardyPhase t:ℂ)*I+I*((-Real.log x:ℝ):ℂ)*t+((Real.pi*(x^2-(q:ℝ)^2-7/8):ℝ):ℂ)*I=
        ((q^2+1:ℕ):ℂ)*(-((Real.pi:ℂ)*I)) := by
      have H := congrArg (fun v : ℝ => (v:ℂ)*I) hφ
      push_cast at H ⊢;linear_combination H
    rw [he,Complex.exp_nat_mul,Complex.exp_neg_pi_mul_I,pow_succ,hsq,pow_succ]
  rw [hurwitzFirstCorrection_one _ hx,critical_monomial_eq hx']
  push_cast
  change _=(-1:ℂ)^(q+1)*((Real.sqrt x:ℝ):ℂ)⁻¹*(riemannSiegelCorrection (2*(x-q)):ℂ)
  push_cast at hphase
  dsimp only [q] at hphase ⊢
  linear_combination ((Real.sqrt x:ℝ):ℂ)⁻¹*(riemannSiegelCorrection (2*(x-q)):ℂ)*hphase

private theorem hardy_first_balanced : ∃ C : ℝ,0<C ∧ ∀ {x t : ℝ},2≤x → t=2*Real.pi*x^2 →
    |hardyZ t-2*∑ m∈range ⌊x⌋₊,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)-
      (-1:ℝ)^(⌊x⌋₊+1)*(Real.sqrt x)⁻¹*riemannSiegelCorrection (2*(x-⌊x⌋₊))| ≤ C*x^(-(3/2:ℝ)) := by
  obtain ⟨A,hA,h⟩ := hurwitzZeta_first_correction_balanced
  obtain ⟨B,hB,hm⟩ := riemannSiegelCorrection_bounded
  refine ⟨A+4*B,by positivity,?_⟩
  intro x t hx ht
  let s := (1/2:ℂ)+(t:ℂ)*I
  let q := ⌊x⌋₊
  let U := hardyGammaUnit t
  let E := Complex.exp ((hardyPhase t:ℂ)*I)
  let F := hurwitzFirstCorrection 1 x s
  let R : ℝ := (-1:ℝ)^(q+1)*(Real.sqrt x)⁻¹*riemannSiegelCorrection (2*(x-q))
  let W : ℝ := hardyZ t-2*∑ m∈range q,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)
  let Z := riemannZeta s-(∑ m∈range q,((m:ℂ)+1)^(-s))-riemannDualGamma s*(∑ m∈range q,((m:ℂ)+1)^(s-1))
  have hx' : 0<x := by linarith
  have ht' : 2≤t := by nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg x)]
  have hcrit : s.re=1/2 := by simp [s]
  have H := h (s:=s) (a:=1) (by norm_num) hx hcrit (by simpa [s] using ht)
  rw [AddCircle.coe_period,HurwitzZeta.hurwitzZeta_zero,hurwitzDirectSum_one s (by linarith),hurwitzDualSum_one] at H
  change ‖Z-F‖≤_ at H
  have hrotate : (W:ℂ)=U*Z := hardyZ_sub_cosines_eq (by linarith) q
  have hsign : E*F=(R:ℂ) := phase_correction_one (by linarith) ht
  have hcorr : ‖F‖≤x^(-(1/2:ℝ))*B := by
    have h₀ := hurwitzSaddleFraction_mem (show 1≤x by linarith)
    have hfrac : x+hurwitzSaddleFraction 1 x-⌊x⌋₊∈Icc (0:ℝ) 2 :=
      ⟨by linarith [Nat.floor_le hx'.le,h₀.1],by linarith [Nat.lt_floor_add_one x,h₀.2]⟩
    rw [show F=hurwitzFirstCorrection 1 x s by rfl,norm_hurwitzFirstCorrection hx',hcrit]
    exact mul_le_mul_of_nonneg_left (hm _ hfrac) (Real.rpow_nonneg hx'.le _)
  have htX : x≤t := by nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg x)]
  have hphase := (norm_hardyGammaUnit_sub_exp_le ht').trans (div_le_div_of_nonneg_left (by norm_num) hx' htX)
  have H' : ‖U*(Z-F)+(U-E)*F‖≤(A+4*B)*x^(-(3/2:ℝ)) := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_hardyGammaUnit,one_mul]
    apply (add_le_add H (mul_le_mul hphase hcorr (norm_nonneg _) (by positivity))).trans_eq
    rw [show x^(-(3/2:ℝ))=x^(-(1/2:ℝ))/x by rw [←Real.rpow_sub_one hx'.ne'];norm_num];ring
  change |W-R|≤_
  rw [←Real.norm_eq_abs,←Complex.norm_real,Complex.ofReal_sub,hrotate,←hsign]
  exact (by ring_nf at H' ⊢;exact H')

/-- Hardy's real cosine sum with its signed first correction. Here x is
√(t/(2π)) and the length is floor(x). The remaining error is O(t^(-3/4)). -/
theorem hardyZ_riemannSiegel_first_correction : ∃ C : ℝ,0<C ∧ ∀ {t : ℝ},8*Real.pi≤t →
    let x := Real.sqrt (t/(2*Real.pi))
    let N := ⌊x⌋₊
    |hardyZ t-2*∑ m∈range N,Real.cos ((hardyGammaUnit t).arg-t*Real.log ((m:ℝ)+1))/Real.sqrt ((m:ℝ)+1)-
      (-1:ℝ)^(N+1)*(Real.sqrt x)⁻¹*riemannSiegelCorrection (2*(x-N))|≤C*t^(-(3/4:ℝ)) := by
  obtain ⟨C,hC,h⟩ := hardy_first_balanced
  refine ⟨C*(2*Real.pi)^(3/4:ℝ),by positivity,?_⟩
  intro t ht x N
  have hπ : 0<2*Real.pi := by positivity
  have ht' : 0<t := (by positivity : 0<8*Real.pi).trans_le ht
  have hx2 : x^2=t/(2*Real.pi) := Real.sq_sqrt (by positivity)
  have hx : 2≤x := by
    have h₄ : 4≤t/(2*Real.pi) := (le_div_iff₀ hπ).mpr (by linarith)
    nlinarith [Real.sqrt_nonneg (t/(2*Real.pi))]
  apply (h hx (show t=2*Real.pi*x^2 by rw [hx2];field_simp)).trans_eq
  dsimp only [x]
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul (div_nonneg ht'.le hπ.le),show (1/2:ℝ)*(-(3/2))= -(3/4) by norm_num,
    Real.div_rpow ht'.le hπ.le,Real.rpow_neg hπ.le,div_inv_eq_mul];ring

end AnalyticNumberTheory.RiemannZeta
