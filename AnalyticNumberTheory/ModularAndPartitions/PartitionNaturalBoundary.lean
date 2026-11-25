import AnalyticNumberTheory.ModularAndPartitions.PartitionRationalCusps

/-!
# The unit circle as the natural boundary of the partition generating function

At a reduced rational cusp, modular inversion gives exponential radial
growth. Rational angles are dense, so the generating function is
unbounded on the intersection of the unit disk with every neighborhood
of any point of its boundary.
-/

open Complex Real Set Filter
open scoped Topology
namespace AnalyticNumberTheory.ModularAndPartitions

private theorem rational_negative_inverse (q : ℚ) :
    ∃ a : ℤ,q.num*a ≡ -1 [ZMOD (q.den:ℤ)] := by
  have h : IsCoprime q.num (q.den:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using q.reduced.gcd_eq_one)
  obtain ⟨a,b,hab⟩ := h
  exact ⟨-a,Int.modEq_iff_dvd.mpr ⟨-b,by linarith only [hab]⟩⟩

private theorem cuspNome_at_boundary (q : ℚ) :
    partitionCuspNome q.num q.den 0=Complex.exp (2*(π:ℂ)*I*(q:ℂ)) := by
  rw [partitionCuspNome,partitionNome,Rat.cast_def]
  congr 1
  ring

private theorem tends_cuspNome (q : ℚ) :
    Tendsto (fun t : ℝ => partitionCuspNome q.num q.den ((t⁻¹:ℝ):ℂ)) atTop
      (𝓝 (Complex.exp (2*(π:ℂ)*I*(q:ℂ)))) := by
  rw [←cuspNome_at_boundary]
  have h : Continuous (partitionCuspNome q.num q.den) := by unfold partitionCuspNome partitionNome; fun_prop
  exact h.continuousAt.tendsto.comp (by simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero)

/-- Along the inward radius to any root of unity, the norm of the partition
generating function tends to infinity. -/
theorem tendsto_norm_partitionGenFun_at_rat (q : ℚ) :
    Tendsto (fun t : ℝ => ‖partitionGenFun (partitionCuspNome q.num q.den ((t⁻¹:ℝ):ℂ))‖)
      atTop atTop := by
  obtain ⟨a,ha⟩ := rational_negative_inverse q
  let b : ℝ := π/(12*q.den)
  have hb : 0<b := div_pos Real.pi_pos (by positivity)
  have hdual : Tendsto (fun t : ℝ => partitionGenFun (partitionCuspNome a q.den t)) atTop (𝓝 1) := by
    apply tendsto_partitionGenFun_zero.comp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [norm_partitionCuspNome, Complex.ofReal_re]
    have h : -2*π/(q.den:ℝ)<0 := div_neg_of_neg_of_pos (by linarith [Real.pi_pos]) (by exact_mod_cast q.den_pos)
    apply (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg h)).congr
    intro t; change Real.exp ((-2*π/q.den)*t)=Real.exp (-2*π*t/q.den); congr 1; ring
  have hnorm : Tendsto (fun t : ℝ => ‖partitionGenFun (partitionCuspNome a q.den t)‖) atTop (𝓝 1) := by
    simpa using hdual.norm
  have he : Tendsto (fun t : ℝ => Real.exp (-b*t⁻¹)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds (x:= -b) |>.mul tendsto_inv_atTop_zero)
  have H := ((tendsto_exp_mul_div_rpow_atTop (1/2:ℝ) b hb).atTop_mul_pos zero_lt_one he).atTop_mul_pos zero_lt_one hnorm
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [partitionGenFun_cusp_inversion q.den_pos ha (show 0<((t⁻¹:ℝ):ℂ).re from inv_pos.mpr ht)]
  have hphase : (π:ℂ)*I*(dedekindSum q.num q.den)=((π*dedekindSum q.num q.den:ℝ):ℂ)*I := by push_cast; ring
  simp only [norm_mul,hphase,Complex.norm_exp_ofReal_mul_I,one_mul,←Complex.ofReal_inv,inv_inv]
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,Complex.norm_cpow_real,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),Real.inv_rpow ht.le,Complex.norm_exp]
  have hR : ((π:ℂ)/(12*q.den)*((t:ℂ)-(t⁻¹:ℝ))).re=b*(t-t⁻¹) := by
    change ((π:ℂ)/(12*q.den)*((t:ℂ)-((t⁻¹:ℝ):ℂ))).re=_
    rw [show (π:ℂ)/(12*q.den)*((t:ℂ)-((t⁻¹:ℝ):ℂ))=((b*(t-t⁻¹):ℝ):ℂ) by dsimp [b]; push_cast; rfl]
    rfl
  rw [hR,show b*(t-t⁻¹)=b*t+(-b*t⁻¹) by ring,Real.exp_add]
  ring

private theorem cuspNome_inside (q : ℚ) {t : ℝ} (ht : 0<t) :
    ‖partitionCuspNome q.num q.den ((t⁻¹:ℝ):ℂ)‖<1 := by
  rw [norm_partitionCuspNome,Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) (inv_pos.mpr ht))
    (by exact_mod_cast q.den_pos)

/-- The generating function is unbounded inside every neighborhood of every
point on the unit circle. -/
theorem partitionGenFun_unbounded_at_unitCircle {ξ : ℂ} (hξ : ‖ξ‖=1) (B : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ z : ℂ, ‖z‖<1 ∧ dist z ξ<ε ∧ B<‖partitionGenFun z‖ := by
  let e (r : ℝ) := Complex.exp (2*(π:ℂ)*I*(r:ℂ))
  have he : Continuous e := by dsimp [e]; fun_prop
  have harg : e (ξ.arg/(2*π))=ξ := by
    have H := Complex.norm_mul_exp_arg_mul_I ξ
    rw [hξ] at H
    simpa [e,Complex.ofReal_div,Complex.ofReal_mul,show (2:ℂ)*π*I*(ξ.arg/(2*π))=ξ.arg*I by
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]] using H
  obtain ⟨q,hq⟩ := (Rat.denseRange_cast (𝕜:=ℝ)).exists_mem_open ((Metric.isOpen_ball (x:=ξ) (ε:=ε)).preimage he)
    (show (e ⁻¹' Metric.ball ξ ε).Nonempty from ⟨ξ.arg/(2*π), by change e (ξ.arg/(2*π))∈Metric.ball ξ ε; rw [harg]; exact Metric.mem_ball_self hε⟩)
  have hq' : Complex.exp (2*(π:ℂ)*I*(q:ℂ))∈Metric.ball ξ ε := by simpa [e] using hq
  obtain ⟨t,ht,hz,hB⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (((tends_cuspNome q).eventually (Metric.isOpen_ball.mem_nhds hq')).and
    ((tendsto_norm_partitionGenFun_at_rat q).eventually_gt_atTop B))).exists
  exact ⟨_,cuspNome_inside q ht,hz,hB⟩

/-- The partition generating function has no continuous extension from the
open unit disk to any point of its boundary. -/
theorem partitionGenFun_no_boundary_limit {ξ : ℂ} (hξ : ‖ξ‖=1) (L : ℂ) :
    ¬Tendsto partitionGenFun (𝓝[Metric.ball 0 1] ξ) (𝓝 L) := by
  intro h
  have H := (h.norm.eventually (eventually_lt_nhds (lt_add_one ‖L‖)))
  obtain ⟨ε,hε,hb⟩ := Metric.mem_nhdsWithin_iff.mp H
  obtain ⟨z,hz,hξz,hL⟩ := partitionGenFun_unbounded_at_unitCircle hξ (‖L‖+1) hε
  have Hz := hb ⟨hξz,show z∈Metric.ball 0 1 by simpa using hz⟩
  exact (not_lt_of_ge hL.le) Hz

end AnalyticNumberTheory.ModularAndPartitions
