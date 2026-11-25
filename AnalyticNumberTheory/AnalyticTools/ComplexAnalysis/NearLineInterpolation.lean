import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.RectangleInterpolation

/-!
# Interpolation near a vertical line

A power bound throughout a finite rectangle and a sharper bound on its
central vertical line transfer to a logarithmically narrow strip. A real
exponential weight normalizes the far vertical edge, and rational
interpolation absorbs the two horizontal edges.
-/

open Complex Real Set Metric
namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- The loss at distance `h` from the middle line is at most a constant
times `exp ((m/w) h log T)` if the rectangle has half-width `w` and
the coarse bound is larger by a factor of `T^m`. -/
theorem norm_le_near_vertical_line {f : ℂ → ℂ} {c w T M : ℝ} (m : ℕ)
    (hw : 0<w) (hT : 1≤T) (hM : 0≤M)
    (hf : DifferentiableOn ℂ f (Icc (c-w) (c+w) ×ℂ Icc (-T) T))
    (hcenter : ∀ z : ℂ, z.re=c → |z.im|≤T → ‖f z‖≤M)
    (hrect : ∀ z : ℂ, |z.re-c|≤w → |z.im|≤T → ‖f z‖≤M*T^m)
    {x : ℝ} (hx : |x-c|≤w) :
    ‖f (x:ℂ)‖ ≤ M*(1+w)^m*Real.exp ((m/w)*|x-c| *Real.log T) := by
  let e : ℝ := if c≤x then 1 else -1
  have he : |e|=1 := by dsimp [e]; split <;> norm_num
  have heh : e*|x-c|=x-c := by
    dsimp [e]; split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h),one_mul]
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]; ring
  let p (z : ℂ) := (c:ℂ)+(e:ℂ)*z
  let K := (m:ℝ)/w*Real.log T
  let g (z : ℂ) := f (p z)*Complex.exp (-(K:ℂ)*z)
  have hK : 0≤K := mul_nonneg (by positivity) (Real.log_nonneg hT)
  have hre (z : ℂ) : (p z).re=c+e*z.re := by simp [p,Complex.mul_re]
  have him (z : ℂ) : |(p z).im|=|z.im| := by simp [p,Complex.mul_im,abs_mul,he]
  have hd (z : ℂ) : |(p z).re-c|=|z.re| := by rw [hre,add_sub_cancel_left,abs_mul,he,one_mul]
  have norm_g (z : ℂ) : ‖g z‖=‖f (p z)‖*Real.exp (-K*z.re) := by simp [g,Complex.norm_exp,Complex.mul_re]
  have hdiff : DifferentiableOn ℂ g (Icc 0 w ×ℂ Icc (-T) T) := by
    apply DifferentiableOn.mul (hf.comp (by dsimp [p]; fun_prop) ?_) (by fun_prop)
    intro z hz
    have hh := (hd z).trans (abs_of_nonneg hz.1.1)
    have hs := abs_le.mp (hh.le.trans hz.1.2)
    exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,abs_le.mp ((him z).le.trans (abs_le.mpr hz.2))⟩
  have hV (z : ℂ) (hz : z.re=0 ∨ z.re=w) (ht : z.im∈Icc (-T) T) : ‖g z‖≤M := by
    have hi : |(p z).im|≤T := (him z).le.trans (abs_le.mpr ht)
    rw [norm_g]
    rcases hz with h|h
    · simpa [h] using hcenter (p z) (by simp [hre,h]) hi
    · have hh := hrect (p z) (by rw [hd,h,abs_of_pos hw]) hi
      rw [h,show -K*w = -((m:ℝ)*Real.log T) by dsimp [K]; field_simp,Real.exp_neg,Real.exp_nat_mul,
        Real.exp_log (zero_lt_one.trans_le hT)]
      exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq (by field_simp [(zero_lt_one.trans_le hT).ne'])
  have hH (z : ℂ) (hz : z.re∈Icc 0 w) (ht : z.im= -T ∨ z.im=T) : ‖g z‖≤M*T^m := by
    have hh := hrect (p z) (by rw [hd,abs_of_nonneg hz.1]; exact hz.2)
      (by rw [him];rcases ht with h|h <;> simp [h,abs_of_nonneg (zero_le_one.trans hT)])
    rw [norm_g]; exact (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hK hz.1]))).trans hh
  have H := norm_le_on_horizontal_segment (f:=g) (a:=0) (b:=w) (l:=-T) (u:=T) (y:=0) (d:=T) m hw
    (zero_lt_one.trans_le hT) (by linarith) (by linarith) hM hdiff hV hH ⟨abs_nonneg _,hx⟩
  have hpx : p ((|x-c|:ℝ):ℂ)=(x:ℂ) := by
    dsimp [p]; rw [←Complex.ofReal_mul,←Complex.ofReal_add]; congr 1; linarith
  simp only [Complex.ofReal_zero,zero_mul,add_zero,norm_g,hpx,Complex.ofReal_re,sub_zero] at H
  have h := mul_le_mul_of_nonneg_right H (Real.exp_pos (K*|x-c|)).le
  rw [mul_assoc,←Real.exp_add,show -K*|x-c| +K*|x-c|=0 by ring,Real.exp_zero,mul_one] at h
  exact h.trans_eq (by dsimp [K]; ring_nf)

/-- A coarse power bound with an independent scale `X` transfers to the
central horizontal segment. Only the geometric condition `w≤T` is needed.
The quadratic holomorphic weight suppresses all three distant edges. -/
theorem norm_le_near_vertical_line_of_power_bound {f : ℂ → ℂ} {c w T X M : ℝ}
    (m : ℕ) (hw : 0<w) (hwT : w≤T) (hX : 1≤X) (hM : 0≤M)
    (hf : DifferentiableOn ℂ f (Icc (c-w) (c+w) ×ℂ Icc (-T) T))
    (hcenter : ∀ z : ℂ,z.re=c → |z.im|≤T → ‖f z‖≤M)
    (hrect : ∀ z : ℂ,|z.re-c|≤w → |z.im|≤T → ‖f z‖≤M*X^m)
    {x : ℝ} (hx : |x-c|≤w) :
    ‖f (x:ℂ)‖≤M*Real.exp ((2*m/w)*|x-c| *Real.log X) := by
  let e : ℝ := if c≤x then 1 else -1
  have he : |e|=1 := by dsimp [e]; split <;> norm_num
  have heh : e*|x-c|=x-c := by
    dsimp [e]; split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h),one_mul]
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]; ring
  let p (z : ℂ) := (c:ℂ)+(e:ℂ)*z
  let K := (m:ℝ)*Real.log X
  let b (z : ℂ) := 2*z/(w:ℂ)-(z/(w:ℂ))^2
  let g (z : ℂ) := f (p z)*Complex.exp (-(K:ℂ)*b z)
  let U := Ioo (0:ℝ) w ×ℂ Ioo (-T) T
  have hT := hw.trans_le hwT
  have hK : 0≤K := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hX)
  have hre (z : ℂ) : (p z).re=c+e*z.re := by simp [p,Complex.mul_re]
  have him (z : ℂ) : |(p z).im|=|z.im| := by simp [p,Complex.mul_im,abs_mul,he]
  have hd (z : ℂ) : |(p z).re-c|=|z.re| := by rw [hre,add_sub_cancel_left,abs_mul,he,one_mul]
  have hb (z : ℂ) : (b z).re=2*(z.re/w)-(z.re/w)^2+(z.im/w)^2 := by
    simp [b,pow_two,Complex.mul_re,Complex.div_ofReal_re,Complex.div_ofReal_im];ring
  have norm_g (z : ℂ) : ‖g z‖=‖f (p z)‖*Real.exp (-K*(b z).re) := by simp [g,Complex.norm_exp,Complex.mul_re]
  have hcl : closure U=Icc (0:ℝ) w ×ℂ Icc (-T) T := by
    rw [show U=Ioo (0:ℝ) w ×ℂ Ioo (-T) T by rfl,closure_reProdIm,closure_Ioo hw.ne,closure_Ioo (by linarith : -T≠T)]
  have hg : DiffContOnCl ℂ g U := by
    apply DifferentiableOn.diffContOnCl;rw [hcl]
    apply DifferentiableOn.mul (hf.comp (by dsimp [p];fun_prop) ?_) (by dsimp [b];fun_prop)
    intro z hz
    have hh := (hd z).trans (abs_of_nonneg hz.1.1)
    have hh' := abs_le.mp (hh.le.trans hz.1.2)
    exact ⟨⟨by linarith [hh'.1],by linarith [hh'.2]⟩,abs_le.mp ((him z).le.trans (abs_le.mpr hz.2))⟩
  have coarse (z : ℂ) (hr : z.re∈Icc 0 w) (hi : |z.im|≤T) (hbar : 1≤(b z).re) : ‖g z‖≤M := by
    have H := hrect (p z) (by rw [hd,abs_of_nonneg hr.1];exact hr.2) ((him z).le.trans hi)
    rw [norm_g];apply (mul_le_mul H (Real.exp_le_exp.mpr (show -K*(b z).re≤ -K by nlinarith only [mul_le_mul_of_nonneg_left hbar hK]))
      (Real.exp_pos _).le (by positivity)).trans_eq
    rw [Real.exp_neg,show Real.exp K=X^m by dsimp [K];rw [Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hX)]]
    field_simp [(zero_lt_one.trans_le hX).ne']
  have Hfront (z : ℂ) (hz : z∈frontier U) : ‖g z‖≤M := by
    rw [show U=Ioo (0:ℝ) w ×ℂ Ioo (-T) T by rfl,frontier_reProdIm,closure_Ioo hw.ne,
      closure_Ioo (by linarith : -T≠T),frontier_Ioo hw,frontier_Ioo (by linarith : -T<T)] at hz
    rcases hz with h|h
    · have hr : z.re∈Icc 0 w := h.1
      have hh : z.im= -T ∨ z.im=T := h.2
      have hx' : 0≤z.re/w := div_nonneg hr.1 hw.le
      have hx'' : z.re/w≤1 := (div_le_one hw).mpr hr.2
      have hy : 1≤T/w := (one_le_div hw).mpr hwT
      apply coarse z hr
      · rcases hh with H|H <;> simp [H,abs_of_pos hT]
      · rw [hb]
        rcases hh with H|H <;> rw [H] <;>
          nlinarith only [mul_nonneg hx' (sub_nonneg.mpr hx''),hx',sq_nonneg (T/w-1),hy,
            show (-T)/w= -(T/w) by ring]
    · have hr : z.re=0 ∨ z.re=w := h.1
      have hi : |z.im|≤T := abs_le.mpr h.2
      rcases hr with H|H
      · rw [norm_g]
        apply (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)).trans
          (hcenter _ (by simp [hre,H]) ((him z).le.trans hi))
        rw [hb,H];simp;exact mul_nonneg hK (sq_nonneg _)
      · exact coarse z ⟨by linarith,by linarith⟩ hi (by rw [hb,H,div_self hw.ne'];nlinarith only [sq_nonneg (z.im/w)])
  have hmem : ((|x-c|:ℝ):ℂ)∈closure U := by
    rw [hcl];exact ⟨⟨abs_nonneg _,hx⟩,show -T≤(0:ℝ) ∧ 0≤T by constructor <;> linarith⟩
  have H := Complex.norm_le_of_forall_mem_frontier_norm_le ((isBounded_Ioo 0 w).reProdIm (isBounded_Ioo (-T) T)) hg Hfront hmem
  have hpx : p ((|x-c|:ℝ):ℂ)=(x:ℂ) := by
    dsimp [p];rw [←Complex.ofReal_mul,←Complex.ofReal_add];congr 1;linarith
  rw [norm_g,hpx] at H
  have H' := mul_le_mul_of_nonneg_right H (Real.exp_pos (K*(b (|x-c|:ℝ)).re)).le
  rw [mul_assoc,←Real.exp_add,show -K*(b (|x-c|:ℝ)).re+K*(b (|x-c|:ℝ)).re=0 by ring,Real.exp_zero,mul_one] at H'
  apply H'.trans;apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
  rw [hb];simp only [Complex.ofReal_re,Complex.ofReal_im,zero_div,zero_pow (by norm_num : 2≠0),add_zero]
  have hh := mul_le_mul_of_nonneg_left (show 2*(|x-c|/w)-(|x-c|/w)^2≤2*(|x-c|/w) by linarith [sq_nonneg (|x-c|/w)]) hK
  exact hh.trans_eq (by dsimp [K];ring)

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
