import AnalyticNumberTheory.ModularAndPartitions.EisensteinHankel
import AnalyticNumberTheory.AnalyticTools.RotatedBarnesHankel

/-!
# The complex-weight modular law on the full upper half-plane

A clockwise tilt makes both Barnes periods decay along a common ray.
The displayed contour therefore works on either side of the real
coordinate of the cusp, including its vertical line.
-/

open Complex Real Set Filter Finset
open scoped Topology UpperHalfPlane MatrixGroups
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.ModularAndPartitions

/-- A clockwise direction putting both `1` and `b` in a right
half-plane after multiplication. -/
noncomputable def eisensteinRay (b : ℂ) : ℂ := 1-(((1+|b.re|)/b.im:ℝ):ℂ)*I

private theorem eisensteinRay_re (b : ℂ) : (eisensteinRay b).re=1 := by simp [eisensteinRay]

private theorem eisensteinRay_im {b : ℂ} (hb : 0<b.im) : (eisensteinRay b).im<0 := by
  simp [eisensteinRay]; positivity

private theorem eisensteinRay_period_re {b : ℂ} (hb : 0<b.im) : 0<(b*eisensteinRay b).re := by
  simp only [Complex.mul_re,eisensteinRay_re,mul_one]
  have he : (eisensteinRay b).im= -((1+|b.re|)/b.im) := by simp [eisensteinRay]
  rw [he]; field_simp; nlinarith only [abs_nonneg b.re,neg_le_abs b.re,hb]

private theorem offset_tilt_re {c : ℕ} (hc : 0<c) (d : ℤ) (z : ℍ) {ω : ℂ} (hw : ω.re=1)
    (hp : 0<(((c:ℂ)*z+d)*ω).re) (j : Fin c) : 0<((eisensteinBarnesOffset c d z j)*ω).re := by
  have hc' : 0<(c:ℤ) := by exact_mod_cast hc
  have hcr : 0<(c:ℝ) := by exact_mod_cast hc
  have hr := Int.emod_lt_of_pos (d*(j:ℕ)) hc'
  have hdiv := Int.emod_add_mul_ediv (d*(j:ℕ)) (c:ℤ)
  rw [add_comm] at hdiv
  have h₁ : (c:ℝ)*(↑(d*(j:ℕ)/(c:ℤ):ℤ):ℝ)+↑(d*(j:ℕ)%(c:ℤ):ℤ)=(d:ℝ)*(j:ℕ) := by exact_mod_cast hdiv
  have h₂ : (↑(d*(j:ℕ)%(c:ℤ):ℤ):ℝ)<c := by exact_mod_cast hr
  simp only [eisensteinBarnesOffset,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.one_re,Complex.one_im,Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,Complex.intCast_im,
    hw,zero_mul,mul_one,add_zero,zero_add,sub_zero] at hp ⊢
  apply (mul_pos_iff_of_pos_left hcr).mp
  have hj : 0≤((j:ℕ):ℝ) := Nat.cast_nonneg _
  nlinarith only [h₁,h₂,mul_nonneg hj hp.le]

/-- An explicit Hankel formula for every upper-half-plane point and
every complex weight. The common ray is a function of the modular
denominator alone. -/
theorem eisensteinPeriod_eq_tiltedHankel_with_radius (γ : SL(2,ℤ)) (z : ℍ) (hcγ : 0<γ 1 0) :
    let c := (γ 1 0).toNat
    let b : ℂ := (c:ℂ)*z+γ 1 1
    let ω := eisensteinRay b
    ∃ X : ℝ, (∀ j : Fin c, TiltedBarnesRadius (eisensteinBarnesOffset c (γ 1 1) z j) b ω X) ∧
      (∀ j : Fin c, Differentiable ℂ (tiltedBarnesHankel (eisensteinBarnesOffset c (γ 1 1) z j) b ω X)) ∧
      ∀ s : ℂ, eisensteinPeriod γ z s=
      -Complex.exp (-π*I*s)*(Complex.Gamma s)⁻¹*ω^s*
        ∑ j : Fin c,tiltedBarnesHankel (eisensteinBarnesOffset c (γ 1 1) z j) b ω X s := by
  dsimp only
  let c := (γ 1 0).toNat
  let b : ℂ := (c:ℂ)*z+γ 1 1
  let ω := eisensteinRay b
  let a := eisensteinBarnesOffset c (γ 1 1) z
  have hγ : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hcγ.le
  have hc : 0<c := by dsimp [c]; omega
  have him : 0<b.im := by
    simp [b,Complex.mul_im]; exact mul_pos (Nat.cast_pos.mpr hc) z.im_pos
  have hw : ω.re=1 := eisensteinRay_re b
  have hn : ω≠0 := by intro h; rw [h] at hw; norm_num at hw
  have hω := eisensteinRay_im him
  have hb := eisensteinRay_period_re him
  have ha (j : Fin c) := offset_tilt_re hc (γ 1 1) z hw hb j
  have hai (j : Fin c) : 0≤(a j).im := by
    simp [a,eisensteinBarnesOffset,Complex.mul_im]; exact mul_nonneg (Nat.cast_nonneg _) z.im_pos.le
  choose R hR using (fun j : Fin c => exists_tiltedBarnesRadius (a j) (b:=b) (ω:=ω) (fun e => by rw [e] at him; simp at him) hn)
  obtain ⟨X,hX⟩ := (Set.finite_range R).bddBelow
  have hA (j : Fin c) : TiltedBarnesRadius (a j) b ω X := (hR j).mono (hX (mem_range_self j))
  let F (s : ℂ) := -Complex.exp (-π*I*s)*(Complex.Gamma s)⁻¹*ω^s*∑ j : Fin c,tiltedBarnesHankel (a j) b ω X s
  have hF : Differentiable ℂ F := by
    apply Differentiable.mul (((by fun_prop : Differentiable ℂ (fun s : ℂ => -Complex.exp (-π*I*s))).mul
      Complex.differentiable_one_div_Gamma).mul (differentiable_id.const_cpow (Or.inl hn)))
    exact Differentiable.fun_sum fun j _ => differentiable_tiltedBarnesHankel (ha j) hb (by rw [hw]; norm_num) (hA j)
  have H (s : ℂ) (hs : 2<s.re) : eisensteinPeriod γ z s=F s := by
    rw [eisensteinPeriod_eq_cone γ z hcγ hs,←hγ,eisensteinConeSum_eq_barnes_upperHalfPlane hc _ z hs]
    unfold F
    let J := Complex.exp (s*(2*π*I))-1
    have he (j : Fin c) : tiltedBarnesHankel (a j) b ω X s=(J*Complex.Gamma s*ω^(-s))*barnesDoubleZeta (a j) b s := by
      rw [tiltedBarnesHankel_eq (ha j) hb hw (hA j) hs,rotatedBarnes_tsum (hai j) him.le hω]
      dsimp only [J]; ring
    simp_rw [he]; rw [←Finset.mul_sum]
    have hgam : Complex.Gamma s≠0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hwS : ω^s≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
    have hphase : -Complex.exp (-π*I*s)*J=Complex.exp (-π*I*s)-Complex.exp (π*I*s) := by
      dsimp only [J]; rw [neg_mul,mul_sub,mul_one,←Complex.exp_add,show -↑π*I*s+s*(2*↑π*I)=↑π*I*s by ring]; ring
    rw [←hphase,Complex.cpow_neg]
    let U := -Complex.exp (-π*I*s)
    let Z := ∑ j : Fin c,barnesDoubleZeta (a j) b s
    change U*J*Z=U*(Complex.Gamma s)⁻¹*ω^s*(J*Complex.Gamma s*(ω^s)⁻¹*Z)
    field_simp
  have f₁ : AnalyticOnNhd ℂ (eisensteinPeriod γ z) univ := fun s _ => (differentiable_eisensteinPeriod γ z).analyticAt s
  have f₂ : AnalyticOnNhd ℂ F univ := fun s _ => hF.analyticAt s
  have heq : eisensteinPeriod γ z=F := f₁.eq_of_eventuallyEq f₂ (z₀:=(3:ℂ))
    ((Complex.continuous_re.continuousAt.eventually_const_lt (by norm_num : 2<(3:ℂ).re)).mono fun s hs => H s hs)
  exact ⟨X,hA,fun j => differentiable_tiltedBarnesHankel (ha j) hb (by rw [hw]; norm_num) (hA j),congrFun heq⟩


/-- The modular transformation on a common Hankel contour. -/
theorem eisensteinPeriod_eq_tiltedHankel (γ : SL(2,ℤ)) (z : ℍ) (hcγ : 0<γ 1 0) :
    let c := (γ 1 0).toNat
    let b : ℂ := (c:ℂ)*z+γ 1 1
    let ω := eisensteinRay b
    ∃ X : ℝ, ∀ s : ℂ, eisensteinPeriod γ z s=
      -Complex.exp (-π*I*s)*(Complex.Gamma s)⁻¹*ω^s*
        ∑ j : Fin c,tiltedBarnesHankel (eisensteinBarnesOffset c (γ 1 1) z j) b ω X s := by
  obtain ⟨X,_,_,H⟩ := eisensteinPeriod_eq_tiltedHankel_with_radius γ z hcγ
  exact ⟨X,H⟩

end AnalyticNumberTheory.ModularAndPartitions
