import AnalyticNumberTheory.RiemannZeta.StripSecondMoment
import AnalyticNumberTheory.RiemannZeta.DualGammaMeanSquare

/-!
# The second moment to the left of the critical line

Reflection contributes the weight (t/(2π))^(1−2σ). Partial integration
of the right-strip mean gives the leading coefficient
ζ(2−2σ)(2π)^(2σ−1)/(2−2σ). The remainder is Oσ(T).
-/
open Real Complex MeasureTheory Set Filter
open scoped Interval Asymptotics Topology ComplexConjugate
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

private theorem reflected_sq_pointwise {σ : ℝ} (hσ : 0<σ) (hhalf : σ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀{t : ℝ},1≤t →
      |‖riemannZeta ((σ:ℂ)+t*I)‖^2-(2*Real.pi)^(2*σ-1)*t^(1-2*σ)*
        ‖riemannZeta (((1-σ:ℝ):ℂ)+t*I)‖^2|≤C := by
  let k := 1-2*σ
  let c := (2*Real.pi)^(2*σ-1)
  let f := fun t : ℝ => ‖riemannZeta (((1-σ:ℝ):ℂ)+t*I)‖^2
  let g := fun t : ℝ => ‖riemannZeta ((σ:ℂ)+t*I)‖^2
  have hc : 0<c := Real.rpow_pos_of_pos (by positivity) _
  have hk : 0<k := by dsimp [k];linarith
  have hf : Continuous f := (continuous_vertical_zeta (by linarith : 1-σ≠1)).norm.pow 2
  have hg : Continuous g := (continuous_vertical_zeta (by linarith : σ≠1)).norm.pow 2
  obtain ⟨M,hM,hm⟩ := norm_sq_riemannDualGamma_error
  obtain ⟨D,hD,hd⟩ := norm_riemannZeta_strip_height (by linarith : 0<1-σ) (by linarith : 1-σ<1)
  let e := fun t : ℝ => |g t-c*t^k*f t|
  have he : Continuous e := (hg.sub ((continuous_const.mul (Real.continuous_rpow_const hk.le)).mul hf)).abs
  obtain ⟨v,hv,Hv⟩ := isCompact_Icc.exists_isMaxOn (f:=e) (by exact ⟨1,le_rfl,by norm_num⟩ : (Icc (1:ℝ) 2).Nonempty)
    he.continuousOn
  have hev : 0≤e v := abs_nonneg _
  refine ⟨e v+M*c*D^2,by positivity,?_⟩
  intro t ht
  change e t≤_
  rcases le_or_gt t 2 with ht₂|ht₂
  · exact (Hv ⟨ht,ht₂⟩).trans (le_add_of_nonneg_right (by positivity))
  let s := (σ:ℂ)+(t:ℂ)*I
  have hsr : s.re=σ := by simp [s]
  have hsi : s.im=t := by simp [s]
  have ht' : 0<t := by linarith
  have H := hm (s:=s) (hsr ▸ ⟨hσ.le,by linarith⟩) (by simpa [hsi,abs_of_pos ht'] using ht₂.le)
  have hpow : (t/(2*Real.pi))^(1-2*σ)=c*t^k := by
    dsimp [c,k];rw [Real.div_rpow ht'.le (by positivity),show 2*σ-1= -(1-2*σ) by ring,Real.rpow_neg (by positivity)]
    ring
  rw [hsr,hsi,abs_of_pos ht',hpow] at H
  have hconj : (1-s)=conj (((1-σ:ℝ):ℂ)+t*I) := by dsimp [s];push_cast;simp;ring
  have HG : g t=‖riemannDualGamma s‖^2*f t := by
    change ‖riemannZeta s‖^2=_
    rw [riemannZeta_dualGamma_functional_equation (hsi ▸ ht'.ne'),hconj,riemannZeta_conj,norm_mul,
      Complex.norm_conj,mul_pow]
  have hD' := hd ht
  rw [show 1-(1-σ)=σ by ring] at hD'
  have hf' : f t≤(D*t^σ)^2 := pow_le_pow_left₀ (norm_nonneg _) hD' 2
  have h := mul_le_mul H hf' (sq_nonneg _) (by positivity)
  have hcan : M/t*(c*t^k)*(D*t^σ)^2=M*c*D^2 := by
    have hp : (t^σ)^2*t^k=t := by
      rw [←Real.rpow_natCast (t^σ) 2,←Real.rpow_mul ht'.le,←Real.rpow_add ht']
      rw [show σ*(2:ℕ)+k=1 by dsimp [k];push_cast;ring,Real.rpow_one]
    calc _ = (M*c*D^2/t)*((t^σ)^2*t^k) := by ring
         _ = _ := by rw [hp];field_simp
  change |g t-c*t^k*f t|≤_
  rw [HG,←sub_mul,abs_mul,abs_of_nonneg (show 0≤f t by dsimp [f];positivity)]
  exact h.trans ((le_of_eq hcan).trans (by linarith))

/-- Second moment of ζ(σ+it) for every fixed 0<σ<1/2, with its explicit
main term and an error at most a constant times T for every T≥1. -/
theorem riemannZeta_left_strip_second_moment {σ : ℝ} (hσ : 0<σ) (hhalf : σ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀{T : ℝ},1≤T →
    |(∫ t in (1:ℝ)..T,‖riemannZeta ((σ:ℂ)+t*I)‖^2)-
      ((2*Real.pi)^(2*σ-1)*(riemannZeta ((2-2*σ:ℝ):ℂ)).re/(2-2*σ))*T^(2-2*σ)|≤C*T := by
  let k := 1-2*σ
  let c := (2*Real.pi)^(2*σ-1)
  let f := fun t : ℝ => ‖riemannZeta (((1-σ:ℝ):ℂ)+t*I)‖^2
  let g := fun t : ℝ => ‖riemannZeta ((σ:ℂ)+t*I)‖^2
  let d := (riemannZeta ((2-2*σ:ℝ):ℂ)).re
  have hk : 0<k := by dsimp [k];linarith
  have hc : 0<c := Real.rpow_pos_of_pos (by positivity) _
  have hf : Continuous f := (continuous_vertical_zeta (by linarith : 1-σ≠1)).norm.pow 2
  have hg : Continuous g := (continuous_vertical_zeta (by linarith : σ≠1)).norm.pow 2
  have hw := Real.continuous_rpow_const hk.le
  obtain ⟨A,hA,H⟩ := reflected_sq_pointwise hσ hhalf
  obtain ⟨B,hB,K⟩ := riemannZeta_right_strip_second_moment (by linarith : 1/2<1-σ) (by linarith : 1-σ<1)
  rw [show 2*(1-σ)=2-2*σ by ring,show 2-(2-2*σ)=2*σ by ring] at K
  let main := c*d/(k+1)
  refine ⟨A+c*(2*B)+|main|,by positivity,?_⟩
  intro T hT
  have ht : 0<T := by linarith
  have herr (t : ℝ) (ht' : t∈Icc 1 T) : |∫z in (1:ℝ)..t,f z-d|≤B*T^(2*σ) := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable ..) (continuous_const.intervalIntegrable ..),
      intervalIntegral.integral_const,smul_eq_mul]
    exact (K ht'.1).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith [ht'.1]) ht'.2 (by linarith)) hB.le)
  have Hf := abs_power_weighted_integral_le (f:=fun t => f t-d) (hf.sub continuous_const) zero_lt_one hT hk.le herr
  have hk' : k+1=2-2*σ := by dsimp [k];ring
  have he : 2*(B*T^(2*σ))*T^k=2*B*T := by
    rw [mul_assoc 2 B (T^(2*σ)) |>.symm,mul_assoc (2*B),←Real.rpow_add ht,
      show 2*σ+k=1 by dsimp [k];ring,Real.rpow_one]
  rw [he] at Hf
  have Hint : (∫t in (1:ℝ)..T,(f t-d)*t^k)=
      (∫t in (1:ℝ)..T,f t*t^k)-d*((T^(k+1)-1)/(k+1)) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (f:=fun t => f t*t^k) (g:=fun t => d*t^k) ((hf.mul hw).intervalIntegrable ..) ((continuous_const.mul hw).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith : -1<k)),Real.one_rpow]
  rw [Hint] at Hf
  have Hsg := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=T)
    (f:=fun t => g t-c*(f t*t^k)) (C:=A) (fun t ht' => by
       rw [uIoc_of_le hT] at ht'
       rw [Real.norm_eq_abs,show c*(f t*t^k)=c*t^k*f t by ring]
       exact H ht'.1.le)
  rw [intervalIntegral.integral_sub (f:=g) (g:=fun t => c*(f t*t^k)) (hg.intervalIntegrable ..) ((continuous_const.mul (hf.mul hw)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hT)] at Hsg
  let J := ∫t in (1:ℝ)..T,f t*t^k
  let G := ∫t in (1:ℝ)..T,g t
  change |G-c*J|≤A*(T-1) at Hsg
  change |J-d*((T^(k+1)-1)/(k+1))|≤2*B*T at Hf
  have hmain : G-main*T^(k+1)=(G-c*J)+c*(J-d*((T^(k+1)-1)/(k+1)))-main := by dsimp [main];ring
  change |G-c*d/(2-2*σ)*T^(2-2*σ)|≤_
  rw [←hk',hmain]
  have hh := abs_sub ((G-c*J)+c*(J-d*((T^(k+1)-1)/(k+1)))) main
  have hhh := abs_add_le (G-c*J) (c*(J-d*((T^(k+1)-1)/(k+1))))
  rw [abs_mul,abs_of_pos hc] at hhh
  linarith only [hh,hhh,Hsg,mul_le_mul_of_nonneg_left Hf hc.le,
    mul_le_mul_of_nonneg_left hT (abs_nonneg main),hA.le]

end AnalyticNumberTheory.RiemannZeta
