import AnalyticNumberTheory.RiemannZeta.HurwitzDerivativeStrips

/-!
# Uniform derivative strips at bounded height and near the zeta pole

The finite-order strip bounds extend to zero real part by continuity.
At bounded height an explicit pole term controls the loss near one.
All constants are independent of the shift and differentiation order.
-/

open Real Complex Finset Filter
open scoped Topology
namespace AnalyticNumberTheory.RiemannZeta

private theorem pole_distance_pos {s : ℂ} (hs : s≠1) : 0 < |1-s.re|+|s.im| := by
  by_contra h
  have h₁ : |1-s.re|=0 := by linarith [abs_nonneg (1-s.re),abs_nonneg s.im]
  have h₂ : |s.im|=0 := by linarith [abs_nonneg s.im]
  apply hs; apply Complex.ext <;> simp only [Complex.one_re,Complex.one_im]
  · linarith only [abs_eq_zero.mp h₁]
  · exact abs_eq_zero.mp h₂

private theorem hurwitz_regular_bounded_pole :
    ∃ A : ℝ,0<A ∧ ∀ {a : ℝ} {s : ℂ},a∈Set.Ioc (0:ℝ) 1 → 0<s.re →
      |s.im|≤2 → s≠1 →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        A+16*(2+|s.im|)^(1-s.re)/(|1-s.re|+|s.im|) := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_approx_dirichletPoly (c:=2) (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨K+2,by positivity,?_⟩
  intro a s ha hσ ht hs
  let M := 1+a
  have hM : 1≤M := by dsimp [M]; linarith [ha.1]
  have hm := zero_lt_one.trans_le hM
  have hm' : M≤2 := by dsimp [M]; linarith [ha.2]
  let T := 2+|s.im|
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg s.im]
  have hT₀ := zero_lt_one.trans_le hT
  let Q := |1-s.re|+|s.im|
  have hQ : 0<Q := pole_distance_pos hs
  have hd : Q≤2*‖1-s‖ := by
    have h1 := Complex.abs_re_le_norm (1-s)
    have h2 := Complex.abs_im_le_norm (1-s)
    simp only [Complex.sub_re,Complex.one_re] at h1
    simp only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg] at h2
    dsimp [Q]; linarith only [h1,h2]
  have hd₀ : 0<‖1-s‖ := by linarith only [hQ,hd]
  let Z := HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)
  let R := (M:ℂ)^(1-s)/(1-s)
  let P := (M:ℂ)^(-s)
  have h := H ha (N:=1) (σ:=s.re) (t:=s.im) hσ (by rwa [Complex.re_add_im]) (by
    norm_num; linarith only [ht,ha.1])
  rw [Complex.re_add_im] at h
  have he : Icc 0 1=({0,1}:Finset ℕ) := by decide
  simp only [he,sum_insert (by decide : (0:ℕ)∉{1}),sum_singleton,Nat.cast_zero,zero_add,Nat.cast_one] at h
  have hP : ‖P‖≤1 := by
    dsimp [P]; rw [Complex.norm_cpow_eq_rpow_re_of_pos hm,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hM (neg_nonpos.mpr hσ.le)
  have herr : ‖Z-(P-R)‖≤K*M^(-s.re) := by
    have H' : ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-((a:ℂ)^(-s)+P-R)‖≤K*M^(-s.re) := by
      simpa [P,R,M] using h
    convert H' using 2; dsimp [Z]; ring
  have hK' := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hM (neg_nonpos.mpr hσ.le)) hK.le
  have htri := norm_add_le (Z-(P-R)) (P-R)
  rw [sub_add_cancel] at htri
  have htri' := norm_sub_le P R
  rw [show ‖R‖=M^(1-s.re)/‖1-s‖ by dsimp [R]; rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hm,Complex.sub_re,Complex.one_re]] at htri'
  change ‖Z‖≤K+2+16*T^(1-s.re)/Q
  by_cases h2 : s.re≤2
  · have hE : 1/4≤T^(1-s.re) := by
      have hT' : T≤4 := by dsimp [T]; linarith
      have hh := Real.rpow_le_rpow_of_exponent_le hT (by linarith : -1≤1-s.re)
      rw [Real.rpow_neg_one] at hh
      exact ((one_div_le_one_div_of_le hT₀ hT').trans (by simpa using hh))
    have hNum := Real.rpow_le_rpow_of_exponent_le hM (by linarith : 1-s.re≤1)
    rw [Real.rpow_one] at hNum
    have hquot : M^(1-s.re)/‖1-s‖≤16*T^(1-s.re)/Q := by
      apply (div_le_div_iff₀ hd₀ hQ).mpr
      calc _ ≤ 2*Q := mul_le_mul_of_nonneg_right (hNum.trans hm') hQ.le
           _ ≤ 4*‖1-s‖ := by linarith
           _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hd₀.le
    linarith only [htri,htri',herr,hP,hK',hquot]
  · have hnorm : 1≤‖1-s‖ := by
      have hh := Complex.abs_re_le_norm (1-s)
      rw [Complex.sub_re,Complex.one_re,abs_of_nonpos (by linarith)] at hh; linarith
    have hquot : M^(1-s.re)/‖1-s‖≤1 := (div_le_one hd₀).mpr ((Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)).trans hnorm)
    linarith only [htri,htri',herr,hP,hK',hquot,show 0≤16*T^(1-s.re)/Q by positivity]

/-- Finite-order estimates uniform in the shift, order, height and real
part, with the pole contribution displayed. This includes `Re s=0`
for order two. -/
theorem hurwitzZeta_sub_initial_derivative_strips_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {k : ℕ} {a : ℝ} {s : ℂ},2≤k → a∈Set.Ioc (0:ℝ) 1 →
      0≤s.re → 1-k/((2:ℝ)^k-2)≤s.re → s≠1 →
      let T := 2+|s.im|
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-(a:ℂ)^(-s)‖≤
        C*T^(1/((2:ℝ)^k-2))*(1+Real.log T)+16*T^(1-s.re)/(|1-s.re|+|s.im|) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_derivative_strips
  obtain ⟨A,hA,HA⟩ := hurwitz_regular_bounded_pole
  refine ⟨C+A,by positivity,?_⟩
  intro k a s hk ha hσ hline hs
  let α := 1/((2:ℝ)^k-2)
  have hp : 4≤(2:ℝ)^k := (by norm_num : (4:ℝ)=2^2).le.trans (pow_le_pow_right₀ (by norm_num) hk)
  have hα : 0≤α := one_div_nonneg.mpr (by linarith)
  let T := 2+|s.im|
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg s.im]
  have ht := zero_lt_one.trans_le hT
  let f (u : ℝ) := ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) (s+u)-(a:ℂ)^(-(s+u))‖
  let g (u : ℝ) := (C+A)*T^α*(1+Real.log T)+16*T^(1-(s+u).re)/(|1-(s+u).re|+|s.im|)
  have hf : ContinuousAt f 0 := by
    dsimp only [f]; apply ContinuousAt.norm; apply ContinuousAt.sub
    · apply ContinuousAt.comp (f:=fun u : ℝ => s+(u:ℂ)) (HurwitzZeta.differentiableAt_hurwitzZeta _ (by simpa using hs)).continuousAt
      fun_prop
    · simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.1.ne')]; fun_prop
  have hg : ContinuousAt g 0 := by
    dsimp only [g]; simp_rw [Real.rpow_def_of_pos ht]
    fun_prop (disch := simpa using (pole_distance_pos hs).ne')
  have he : ∀ᶠ u : ℝ in 𝓝[>] 0,f u≤g u := by
    have hpath : ContinuousAt (fun u : ℝ => s+(u:ℂ)) 0 := by fun_prop
    have hp' := hpath.eventually_ne (by simpa using hs : s+(0:ℝ)≠(1:ℂ))
    filter_upwards [self_mem_nhdsWithin,hp'.filter_mono nhdsWithin_le_nhds] with u hu hne
    have hu' : 0<u := hu
    have hz : (s+u).im=s.im := by simp
    have hσ' : 0<(s+u).re := by simp; linarith
    have hline' : 1-k/((2:ℝ)^k-2)≤(s+u).re := by simp; linarith
    change s+(u:ℂ)≠1 at hne
    have hE := Real.one_le_rpow hT hα
    have hlog := Real.log_nonneg hT
    by_cases hb : 2≤|s.im|
    · have hh := H hk ha hσ' hline' (by rwa [hz])
      rw [hz] at hh
      apply hh.trans
      apply le_add_of_le_of_nonneg _ (by positivity)
      have hpos : 0 < |s.im| := by linarith
      change C*|s.im|^α*(1+Real.log |s.im|)≤(C+A)*T^α*(1+Real.log T)
      have hlog₀ := Real.log_nonneg (by linarith : 1≤|s.im|)
      have hcomp : |s.im|≤T := by dsimp [T]; linarith
      gcongr <;> linarith
    · have hh := HA ha hσ' (by rw [hz]; linarith) hne
      rw [hz] at hh
      apply hh.trans; apply add_le_add _ le_rfl
      change A≤(C+A)*T^α*(1+Real.log T)
      have hdom := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hE (by linarith : 1≤1+Real.log T)) hA.le
      nlinarith only [hdom,show 0≤C*T^α*(1+Real.log T) by positivity]
  have hh := le_of_tendsto_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds) (hg.tendsto.mono_left nhdsWithin_le_nhds) he
  simpa [f,g,T,α] using hh

/-- Finite-order estimates at all heights for Riemann zeta, including the
imaginary axis and the explicit principal-pole contribution. -/
theorem riemannZeta_derivative_strips_all_heights :
    ∃ C : ℝ,0<C ∧ ∀ {k : ℕ} {s : ℂ},2≤k → 0≤s.re →
      1-k/((2:ℝ)^k-2)≤s.re → s≠1 →
      let T := 2+|s.im|
      ‖riemannZeta s‖≤C*T^(1/((2:ℝ)^k-2))*(1+Real.log T)+16*T^(1-s.re)/(|1-s.re|+|s.im|) := by
  obtain ⟨C,hC,H⟩ := hurwitzZeta_sub_initial_derivative_strips_all_heights
  refine ⟨C+1,by positivity,?_⟩
  intro k s hk hσ hline hs
  have he := H (a:=1) hk ⟨zero_lt_one,le_rfl⟩ hσ hline hs
  simp only [Complex.ofReal_one,Complex.one_cpow,AddCircle.coe_period,HurwitzZeta.hurwitzZeta_zero] at he
  let T := 2+|s.im|
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg s.im]
  have h₂ : 4≤(2:ℝ)^k := (by norm_num : (4:ℝ)=2^2).le.trans (pow_le_pow_right₀ (by norm_num) hk)
  let α := 1/((2:ℝ)^k-2)
  have hα : 0≤α := one_div_nonneg.mpr (by linarith)
  have hh := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT hα) (by linarith [Real.log_nonneg hT] : 1≤1+Real.log T)
  have htri := norm_add_le (riemannZeta s-1) 1
  rw [sub_add_cancel,norm_one] at htri
  dsimp only at he ⊢
  change ‖riemannZeta s-1‖≤C*T^α*(1+Real.log T)+_ at he
  change ‖riemannZeta s‖≤(C+1)*T^α*(1+Real.log T)+_
  linarith only [he,htri,hh]

end AnalyticNumberTheory.RiemannZeta
