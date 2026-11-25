import AnalyticNumberTheory.RiemannZeta.RiemannSiegelFirstCorrection
import AnalyticNumberTheory.RiemannZeta.CriticalCorrectionWeights

/-!
# The shifted Riemann–Siegel correction on one pair of cutoff intervals

The Hardy rotation cancels the quadratic part of the exponential phase.
With the last direct and reciprocal frequencies fixed at `u` and `j`,
the remaining phase is affine in the saddle coordinate `x`.
-/

noncomputable section
open Real Complex Set
namespace AnalyticNumberTheory.RiemannZeta

/-- Amplitude of the rotated first correction with fixed last frequencies. -/
def hurwitzCorrectionAmplitude (j u x : ℝ) : ℂ :=
  ((x^(-(1/2:ℝ))*riemannSiegelCorrection (2*x-u-j):ℝ):ℂ)*
    Complex.exp (((Real.pi*(2*x*(j-u)+u^2-(u+j)^2/2-1):ℝ):ℂ)*I)

/-- Rotation removes the quadratic modulus-height oscillation, leaving an affine
phase on each pair of fixed cutoff intervals. -/
theorem rotated_hurwitzFirstCorrection {a x t : ℝ} (hx : 0<x) (ht : t=2*Real.pi*x^2) :
    Complex.exp ((hardyPhase t:ℂ)*I)*hurwitzFirstCorrection a x ((1/2:ℂ)+(t:ℂ)*I)=
      hurwitzCorrectionAmplitude ⌊x⌋₊ ((⌊x-a⌋₊:ℝ)+a) x := by
  let j : ℝ := ⌊x⌋₊
  let u : ℝ := (⌊x-a⌋₊:ℝ)+a
  have hl : hurwitzSaddleFraction a x=x-u := by unfold hurwitzSaddleFraction u;ring
  have hlog : Real.log t=Real.log (2*Real.pi)+2*Real.log x := by
    rw [ht,Real.log_mul (by positivity) (by positivity),Real.log_pow];norm_num
  have hφ : hardyPhase t-t*Real.log x+Real.pi*(2*x*(x-u)+(x-u)^2-(2*x-u-j)^2/2-7/8)=
      Real.pi*(2*x*(j-u)+u^2-(u+j)^2/2-1) := by
    rw [hardyPhase,hlog];linear_combination -ht/2
  have he : Complex.exp ((hardyPhase t:ℂ)*I)*Complex.exp (I*((-Real.log x:ℝ):ℂ)*t)*
      Complex.exp (((Real.pi*(2*x*(x-u)+(x-u)^2-(2*x-u-j)^2/2-7/8):ℝ):ℂ)*I)=
      Complex.exp (((Real.pi*(2*x*(j-u)+u^2-(u+j)^2/2-1):ℝ):ℂ)*I) := by
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    have H := congrArg (fun v : ℝ => (v:ℂ)*I) hφ
    push_cast at H ⊢;linear_combination H
  simp only [hurwitzFirstCorrection,hl,critical_monomial_eq hx]
  change _=hurwitzCorrectionAmplitude j u x
  rw [show (⌊x⌋₊:ℝ)=j from rfl]
  rw [show x+(x-u)-j=2*x-u-j by ring]
  unfold hurwitzCorrectionAmplitude
  rw [Real.rpow_neg hx.le,←Real.sqrt_eq_rpow,Complex.ofReal_mul,Complex.ofReal_inv]
  push_cast at he ⊢
  linear_combination ((Real.sqrt x:ℝ):ℂ)⁻¹*(riemannSiegelCorrection (2*x-u-j):ℂ)*he

private def correctionPhase (j u x : ℝ) := Real.pi*(2*x*(j-u)+u^2-(u+j)^2/2-1)

private theorem correctionPhase_hasDerivAt (j u x : ℝ) :
    HasDerivAt (correctionPhase j u) (2*Real.pi*(j-u)) x := by
  convert ((((((hasDerivAt_id x).const_mul 2).mul_const (j-u)).add_const (u^2)).sub_const
    ((u+j)^2/2)).sub_const 1).const_mul Real.pi using 1
  · rfl
  · ring

private theorem hurwitzCorrectionAmplitude_deriv {j u x : ℝ} (hx : 0<x) :
    let c := 2*x-u-j
    let E := Complex.exp ((correctionPhase j u x:ℂ)*I)
    HasDerivAt (hurwitzCorrectionAmplitude j u)
      (((-(1/2:ℝ)*x^(-(3/2:ℝ))*riemannSiegelCorrection c+
        x^(-(1/2:ℝ))*(2*deriv riemannSiegelCorrection c):ℝ):ℂ)*E+
        ((x^(-(1/2:ℝ))*riemannSiegelCorrection c:ℝ):ℂ)*
          (E*((2*Real.pi*(j-u):ℝ):ℂ)*I)) x := by
  intro c E
  have h₁ := Real.hasDerivAt_rpow_const (x:=x) (p:= -(1/2:ℝ)) (Or.inl hx.ne')
  have h₂ := (analyticAt_riemannSiegelCorrection c).differentiableAt.hasDerivAt.comp x
    ((((hasDerivAt_id x).const_mul 2).sub_const u).sub_const j)
  have hp := (((correctionPhase_hasDerivAt j u x).ofReal_comp).mul_const I).cexp
  convert (h₁.mul h₂).ofReal_comp.mul hp using 1
  · rfl
  · dsimp [c,E]
    rw [show -(1/2:ℝ)-1= -(3/2) by norm_num];push_cast;ring

/-- Differentiability on the positive saddle axis for any fixed cutoff pair. -/
theorem differentiableOn_hurwitzCorrectionAmplitude (j u : ℝ) :
    DifferentiableOn ℝ (hurwitzCorrectionAmplitude j u) (Ioi 0) :=
  fun _ hx => (hurwitzCorrectionAmplitude_deriv hx).differentiableAt.differentiableWithinAt

/-- Both the amplitude and its saddle-coordinate derivative are uniformly
bounded by a constant times the inverse square root of the saddle. -/
theorem hurwitzCorrectionAmplitude_bounds : ∃ C : ℝ,0<C ∧ ∀ {j u x : ℝ},
    1≤x → |j-u|≤1 → 2*x-u-j∈Icc (0:ℝ) 2 →
    ‖hurwitzCorrectionAmplitude j u x‖≤C*x^(-(1/2:ℝ)) ∧
    ‖deriv (hurwitzCorrectionAmplitude j u) x‖≤C*x^(-(1/2:ℝ)) := by
  obtain ⟨D,hD,H⟩ := riemannSiegelCorrection_C1_bound
  refine ⟨(3+2*Real.pi)*D,by positivity,?_⟩
  intro j u x hx hju hc
  let c := 2*x-u-j
  let E := Complex.exp ((correctionPhase j u x:ℂ)*I)
  let p := x^(-(1/2:ℝ))
  have hE : ‖E‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hp : 0≤p := by dsimp [p];positivity
  have hx' : 0<x := by linarith
  obtain ⟨hc₁,hc₂⟩ := H hc
  change |riemannSiegelCorrection c|≤D at hc₁
  change |deriv riemannSiegelCorrection c|≤D at hc₂
  have hsize : |p*riemannSiegelCorrection c|≤p*D := by
    rw [abs_mul,abs_of_nonneg hp];exact mul_le_mul_of_nonneg_left hc₁ hp
  have hsm : x^(-(3/2:ℝ))≤p := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hD' : 0≤p*D := mul_nonneg hp hD.le
  constructor
  · change ‖((p*riemannSiegelCorrection c:ℝ):ℂ)*E‖≤_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hE,mul_one]
    change _≤(3+2*Real.pi)*D*p
    nlinarith only [hsize,hD',mul_nonneg Real.pi_pos.le hD']
  · rw [(hurwitzCorrectionAmplitude_deriv (j:=j) (u:=u) hx').deriv]
    apply (norm_add_le ..).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    change |-(1/2:ℝ)*x^(-(3/2:ℝ))*riemannSiegelCorrection c+p*(2*deriv riemannSiegelCorrection c)| *‖E‖+|p| *|riemannSiegelCorrection c| *(‖E‖*(|2| *|Real.pi| *|j-u|))≤_
    rw [hE,mul_one,one_mul]
    have hd₁ : |-(1/2:ℝ)*x^(-(3/2:ℝ))*riemannSiegelCorrection c|≤p*D := by
      rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg hx'.le _)];norm_num
      nlinarith only [mul_le_mul hsm hc₁ (abs_nonneg _) hp,
        mul_nonneg (Real.rpow_nonneg hx'.le (-(3/2:ℝ))) (abs_nonneg (riemannSiegelCorrection c))]
    have hd₂ : |p*(2*deriv riemannSiegelCorrection c)|≤2*(p*D) := by
      rw [abs_mul,abs_of_nonneg hp,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith only [mul_le_mul_of_nonneg_left hc₂ hp]
    have hfreq : |2*Real.pi*(j-u)|≤2*Real.pi := by
      rw [abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
      nlinarith only [mul_le_mul_of_nonneg_left hju (by positivity : 0≤2*Real.pi)]
    rw [←abs_mul,←abs_mul,←abs_mul]
    calc _ ≤ (p*D+2*(p*D)) + (p*D)*(2*Real.pi) :=
              add_le_add ((abs_add_le ..).trans (add_le_add hd₁ hd₂))
                (mul_le_mul hsize hfreq (abs_nonneg _) hD')
         _ = _ := by dsimp only [p];ring

/-- In the height coordinate the extra derivative of the saddle root gives
a full additional power of decay. -/
theorem hurwitzCorrectionAmplitude_height_bounds : ∃ C : ℝ,0<C ∧ ∀ {j u t : ℝ},
    0<t → 1≤hardySaddleRoot t → |j-u|≤1 → 2*hardySaddleRoot t-u-j∈Icc (0:ℝ) 2 →
    ‖hurwitzCorrectionAmplitude j u (hardySaddleRoot t)‖≤C*(hardySaddleRoot t)^(-(1/2:ℝ)) ∧
    ‖deriv (fun v => hurwitzCorrectionAmplitude j u (hardySaddleRoot v)) t‖≤
      C*(hardySaddleRoot t)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,H⟩ := hurwitzCorrectionAmplitude_bounds
  refine ⟨C,hC,?_⟩
  intro j u t ht hx hju hc
  let x := hardySaddleRoot t
  have hx' : 0<x := hardySaddleRoot_pos ht
  obtain ⟨hs,hd⟩ := H hx hju hc
  refine ⟨hs,?_⟩
  have ha := (hurwitzCorrectionAmplitude_deriv (j:=j) (u:=u) hx').differentiableAt.hasDerivAt
  have hcomp := ha.scomp t (hardySaddleRoot_hasDerivAt ht)
  rw [show deriv (fun v => hurwitzCorrectionAmplitude j u (hardySaddleRoot v)) t=_ from hcomp.deriv]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(4*Real.pi*x)⁻¹)]
  have hden : (4*Real.pi*x)⁻¹≤x⁻¹ := inv_anti₀ hx' (by nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le hx'.le])
  apply (mul_le_mul hden hd (norm_nonneg _) (inv_nonneg.mpr hx'.le)).trans_eq
  change x⁻¹*(C*x^(-(1/2:ℝ)))=C*x^(-(3/2:ℝ))
  rw [show x⁻¹*(C*x^(-(1/2:ℝ)))=C*(x^(-(1/2:ℝ))/x) by ring,
    ←Real.rpow_sub_one hx'.ne'];norm_num

end AnalyticNumberTheory.RiemannZeta
