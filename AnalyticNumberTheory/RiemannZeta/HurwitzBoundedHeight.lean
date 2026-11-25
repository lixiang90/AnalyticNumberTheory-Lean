import AnalyticNumberTheory.RiemannZeta.HurwitzLogFreeApproximation

/-!
# The sharp Hurwitz equation at bounded height

Replacing the height by max(B,|t|) allows the cutoffs to stay positive
all the way down to the real axis. The error constant then depends on
the distance to the pole at s=1.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.Summation
namespace AnalyticNumberTheory.RiemannZeta

private theorem uniform_direct_error {a x : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hx : 2≤x)
    {s : ℂ} (hσ : s.re∈Icc (0:ℝ) 1) {ε B : ℝ} (hε : 0<ε) (hp : ε≤‖1-s‖) (hB : x≤B) (ht : |s.im|≤B) :
    ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s‖ ≤
      B/ε+1+(B+1)+(B+1)*(B+2) := by
  have hx' : 1≤x := by linarith
  have hr : 1≤x-a := by linarith [ha.2]
  have hs' : s≠1 := by intro he;rw [he,sub_self,norm_zero] at hp;linarith
  have hb : 0≤B := by linarith
  have hs : ‖s‖≤B+1 := by
    apply (Complex.norm_le_abs_re_add_abs_im s).trans
    rw [abs_of_nonneg hσ.1];linarith [hσ.2]
  have hs1 : ‖s+1‖≤B+2 := (norm_add_le _ _).trans (by simp;linarith)
  let V := ∫ u in Ioi (x-a),(bernoulliKernel 2 u:ℂ)*((u+a:ℝ):ℂ)^(-s-2)
  have hV : ‖V‖≤1 := by
    have hp : 0<x-a := by linarith
    have hi := integrableOn_bernoulliKernel_two_shift_cpow_Ioi hp.le ha.1 (by linarith [hσ.1] : -1<s.re)
    have hdom := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hp
    apply (norm_integral_le_integral_norm _).trans
    apply le_trans _ (show (∫ u in Ioi (x-a),u^(-2:ℝ))≤1 from ?_)
    · apply setIntegral_mono_on hi.norm hdom measurableSet_Ioi
      intro u hu
      have hu' : 1≤u := hr.trans (mem_Ioi.mp hu).le
      have hua : u≤u+a := by linarith [ha.1]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),sub_re,neg_re]
      norm_num only [re_ofNat]
      have hbern : |bernoulliKernel 2 u|≤1 := by linarith [bernoulliKernel_two_abs_le u]
      apply (mul_le_mul_of_nonneg_right hbern (Real.rpow_nonneg (by linarith : 0≤u+a) _)).trans
      rw [one_mul]
      exact (Real.rpow_le_rpow_of_exponent_le (hu'.trans hua) (by linarith [hσ.1])).trans
        (Real.rpow_le_rpow_of_nonpos (by linarith) hua (by norm_num))
    · rw [integral_Ioi_rpow_of_lt (by norm_num) hp];norm_num
      simpa only [Real.rpow_neg_one] using inv_le_one_of_one_le₀ hr
  let P := (x:ℂ)^(1-s)/(1-s)
  let W := (sawtooth (x-a):ℂ)*(x:ℂ)^(-s)
  let E := (bernoulliKernel 2 (x-a):ℂ)*s*(x:ℂ)^(-s-1)
  have hP : ‖P‖≤B/ε := by
    dsimp [P];rw [norm_div,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),sub_re,one_re]
    apply div_le_div₀ (by positivity) _ hε hp
    have H := Real.rpow_le_rpow_of_exponent_le hx' (by linarith [hσ.1] : 1-s.re≤1)
    rw [Real.rpow_one] at H
    exact H.trans hB
  have hW : ‖W‖≤1 := by
    dsimp [W];rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),neg_re]
    exact (mul_le_mul (show |sawtooth (x-a)|≤1 by linarith [sawtooth_abs_le (x-a)])
      (Real.rpow_le_one_of_one_le_of_nonpos hx' (by linarith [hσ.1])) (by positivity) zero_le_one).trans_eq (one_mul _)
  have hE : ‖E‖≤B+1 := by
    dsimp [E];rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),sub_re,neg_re,one_re]
    apply (mul_le_mul (mul_le_mul (show |bernoulliKernel 2 (x-a)|≤1 by linarith [bernoulliKernel_two_abs_le (x-a)]) hs
      (norm_nonneg _) zero_le_one) (Real.rpow_le_one_of_one_le_of_nonpos hx' (by linarith [hσ.1])) (by positivity) (by positivity)).trans_eq
    ring
  have H := hurwitzZeta_eq_real_cutoff ha (by linarith [ha.2] : a≤x) (by linarith [hσ.1] : -1<s.re) hs'
  have he : HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s= -P+W+E-s*(s+1)*V := by
    dsimp only [P,W,E,V];linear_combination H
  rw [he]
  have hT : ‖s*(s+1)*V‖≤(B+1)*(B+2) := by
    rw [norm_mul,norm_mul]
    exact (mul_le_mul (mul_le_mul hs hs1 (norm_nonneg _) (by positivity)) hV (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  apply (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (by simpa using hP) hW)) hE)) hT)

private theorem bounded_dual (B ε : ℝ) (hε : 0<ε) : ∃ C : ℝ,∀ a y : ℝ,y≤B → ∀ s : ℂ,
    s.re∈Icc (0:ℝ) 1 → |s.im|≤B → ε≤‖1-s‖ → ‖hurwitzDualSum a y s‖≤C := by
  let S := Metric.closedBall (0:ℂ) (B+1) ∩ Complex.re ⁻¹' Icc (0:ℝ) 1 ∩ {z : ℂ | ε≤‖1-z‖}
  have hS : IsCompact S := ((isCompact_closedBall _ _).inter_right (isClosed_Icc.preimage Complex.continuous_re)).inter_right
    (isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
  let F (s : ℂ) := ∑ m∈range ⌊B⌋₊,(‖hurwitzDualMode s (hurwitzOmega m)‖+‖hurwitzDualMode s (-hurwitzOmega m)‖)
  have hg (s : ℂ) (hs : s∈S) : ContinuousAt (fun z => Complex.Gamma (1-z)) s := by
    apply (Complex.continuousAt_Gamma _ ?_).comp (continuous_const.sub continuous_id).continuousAt
    intro n hn
    change 1-s = -(n:ℂ) at hn
    have hre := congrArg Complex.re hn
    have hs1 : s.re≤1 := hs.1.2.2
    simp only [sub_re,one_re,neg_re,natCast_re] at hre
    have hn0 : n=0 := by exact_mod_cast (show (n:ℝ)=0 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    subst n;simp at hn
    have hh : ε≤‖1-s‖ := hs.2
    rw [hn,norm_zero] at hh
    linarith
  have hc : ContinuousOn F S := by
    apply continuousOn_finsetSum
    intro m hm
    have H (ω : ℝ) (hw : ω≠0) : ContinuousOn (fun s => hurwitzDualMode s ω) S :=
      (((continuous_const_cpow' (hurwitzFrequency_ne hw)).comp (continuous_id.sub continuous_const)).continuousOn).mul
        (fun s hs => (hg s hs).continuousWithinAt)
    exact (H _ (hurwitzOmega_pos m).ne').norm.add (H _ (neg_ne_zero.mpr (hurwitzOmega_pos m).ne')).norm
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨C,?_⟩
  intro a y hy s hσ ht hdist
  have hs : s∈S := by
    constructor
    · constructor
      · rw [Metric.mem_closedBall,dist_zero_right]
        apply (Complex.norm_le_abs_re_add_abs_im s).trans
        rw [abs_of_nonneg hσ.1];linarith [hσ.2]
      · exact hσ
    · exact hdist
  apply le_trans _ ((Real.le_norm_self _).trans (hC s hs))
  unfold hurwitzDualSum
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (g:=fun m => ‖hurwitzDualMode s (hurwitzOmega m)‖+‖hurwitzDualMode s (-hurwitzOmega m)‖)
    (fun m hm => (norm_add_le _ _).trans_eq (by simp))).trans
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.floor_mono hy)) (fun _ _ _ => by positivity)

/-- The logarithm-free bound with clipped height. The only excluded
neighborhood is the stated ε-neighborhood of the pole. -/
theorem hurwitzZeta_clipped_sharp_afe {B ε : ℝ} (hB : 1≤B) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {a x y : ℝ},a∈Ioc (0:ℝ) 1 → 2≤x → x≤y → ∀ {s : ℂ},s.re∈Icc (0:ℝ) 1 →
      ε≤‖1-s‖ → max B |s.im|=2*Real.pi*x*y →
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s-hurwitzDirectSum a x s-hurwitzDualSum a y s‖≤C*x^(-s.re) := by
  obtain ⟨D,hD⟩ := bounded_dual B ε hε
  let M := B/ε+1+(B+1)+(B+1)*(B+2)+|D|
  have hM : 0≤M := by dsimp [M];positivity
  refine ⟨604+B*M,by positivity,?_⟩
  intro a x y ha hx hxy s hσ hp hbal
  have hx' : 0<x := by linarith
  have hy' := hx'.trans_le hxy
  have hA := Real.rpow_nonneg hx'.le (-s.re)
  rcases le_total B |s.im| with ht|ht
  · rw [max_eq_right ht] at hbal
    exact (hurwitzZeta_logFree_sharp_afe ha hx hxy hσ hbal).trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (by linarith : 0≤B) hM]) hA)
  · rw [max_eq_left ht] at hbal
    have hyB : y≤B := by rw [hbal];nlinarith [Real.pi_gt_three,mul_nonneg (show 0≤2*Real.pi-1 by linarith [Real.pi_gt_three]) (mul_nonneg hx'.le hy'.le),mul_nonneg (show 0≤x-1 by linarith) hy'.le]
    apply (norm_sub_le _ _).trans ((add_le_add (uniform_direct_error ha hx hσ hε hp (hxy.trans hyB) ht) (hD a y hyB s hσ ht hp)).trans ?_)
    have hxA : 1≤B*x^(-s.re) := by
      have hxpow : x^s.re≤B := (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤x) hσ.2).trans (by rw [Real.rpow_one];exact hxy.trans hyB)
      rw [Real.rpow_neg hx'.le,←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hx' _)];simpa using hxpow
    calc
      _ ≤ M := by dsimp [M];linarith [le_abs_self D]
      _ ≤ _ := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hxA)]

end AnalyticNumberTheory.RiemannZeta
