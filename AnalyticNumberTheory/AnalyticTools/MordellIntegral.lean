import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import AnalyticNumberTheory.AnalyticTools.MordellGaussian
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.VerticalCauchy

/-!
# Mordell's Gaussian contour integral

The two parallel diagonals through ±πi enclose the pole at the origin.
The coordinate w=(1−i)z turns them into vertical lines of real part ∓π/2.
-/
noncomputable section
open Real Complex Set MeasureTheory
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.AnalyticTools

/-- The meromorphic kernel in Mordell's Gaussian integral. -/
def mordellKernel (c : ℝ) (w : ℂ) := mordellGaussian c w/(Complex.exp w-1)

/-- The oriented diagonal integral, including the line element 1+i. -/
def mordellIntegral (c d : ℝ) := (1+I)*∫ t : ℝ,mordellKernel c (mordellLine d t)

private def diagonal (z : ℂ) : ℂ := (1-I)*z
private def diagonalExp (z : ℂ) : ℂ := Complex.exp (diagonal z)
private def regularMordell (c : ℝ) (z : ℂ) : ℂ :=
  mordellGaussian c (diagonal z)/dslope diagonalExp 0 z

private theorem diagonal_slope_zero : dslope diagonalExp 0 0=1-I := by
  rw [dslope_same]
  have h := ((hasDerivAt_id (0:ℂ)).const_mul (1-I)).cexp.deriv
  change deriv (fun x : ℂ => Complex.exp ((1-I)*x)) 0=1-I
  simpa using h

private theorem diagonal_slope_ne {z : ℂ} (hz : z.re∈Icc (-Real.pi/2) (Real.pi/2)) :
    dslope diagonalExp 0 z≠0 := by
  by_cases he : z=0
  · rw [he,diagonal_slope_zero];intro h;have := congrArg Complex.re h;norm_num at this
  rw [dslope_of_ne _ he,slope_def_field]
  apply div_ne_zero _ (by simpa using he)
  intro h
  have he' : Complex.exp (diagonal z)=1 := by simpa [diagonalExp,diagonal] using sub_eq_zero.mp h
  obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp he'
  have hr := congrArg Complex.re hn
  have hi := congrArg Complex.im hn
  simp [diagonal,mul_re,mul_im] at hr hi
  have hn0 : n=0 := by
    by_contra hn'
    rcases lt_or_gt_of_ne hn' with h|h
    · have h' : (n:ℝ)≤-1 := by exact_mod_cast (show n≤-1 by omega)
      nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right h' Real.pi_pos.le,hz.2]
    · have h' : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
      nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right h' Real.pi_pos.le,hz.1]
  subst n;simp at hn
  exact he ((mul_eq_zero.mp hn).resolve_left (by intro h;have := congrArg Complex.re h;norm_num at this))

private theorem regularMordell_analytic (c : ℝ) {z : ℂ} (hz : z.re∈Icc (-Real.pi/2) (Real.pi/2)) :
    AnalyticAt ℂ (regularMordell c) z := by
  have h : AnalyticAt ℂ diagonalExp z := by unfold diagonalExp diagonal;fun_prop
  apply AnalyticAt.div _ (h.dslope 0) (diagonal_slope_ne hz)
  unfold mordellGaussian diagonal
  fun_prop

private theorem regularMordell_off (c : ℝ) {z : ℂ} (hz : z≠0) :
    regularMordell c z=z*mordellKernel c (diagonal z) := by
  rw [regularMordell,dslope_of_ne _ hz,slope_def_field]
  simp [diagonalExp,diagonal,mordellKernel,div_div_eq_mul_div];ring

private theorem diagonal_coordinates (x t : ℝ) :
    diagonal ((x:ℂ)+t*I)=⟨x+t,t-x⟩ := by
  apply Complex.ext <;> simp [diagonal,mul_re,mul_im] <;> ring

private theorem norm_mordellGaussian_diagonal (c x t : ℝ) :
    ‖mordellGaussian c (diagonal ((x:ℂ)+t*I))‖=
      Real.exp ((x^2-t^2)/(2*Real.pi)+c*(x+t)) := by
  rw [mordellGaussian,diagonal_coordinates,Complex.norm_exp]
  congr 1
  simp [div_re,mul_re,mul_im,pow_two,Complex.normSq_apply]
  field_simp;ring

private theorem denom_bound {w : ℂ} (hw : 1≤|w.re|) : 1/2≤‖Complex.exp w-1‖ := by
  rcases le_or_gt 0 w.re with h|h
  · rw [abs_of_nonneg h] at hw
    have H := norm_sub_norm_le (Complex.exp w) 1
    rw [Complex.norm_exp,norm_one] at H
    linarith [Real.exp_le_exp.mpr hw,Real.exp_one_gt_two]
  · rw [abs_of_neg h] at hw
    have H := norm_sub_norm_le (1:ℂ) (Complex.exp w)
    rw [Complex.norm_exp,norm_one,norm_sub_rev] at H
    have he : Real.exp w.re≤1/2 := by
      rw [← neg_neg w.re,Real.exp_neg,inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.exp_le_exp.mpr hw,Real.exp_one_gt_two]
    linarith

private theorem regularMordell_tail (c x t : ℝ) (hx : x∈Icc (-Real.pi/2) (Real.pi/2))
    (ht : 8*Real.pi*(|c|+2)+4 ≤ |t|) :
    ‖regularMordell c ((x:ℂ)+t*I)‖ ≤ 48/(1+t^2) := by
  have hp := Real.pi_pos
  have hπ := Real.pi_lt_four
  let u := |t|
  have hu : 4≤u := by dsimp [u];nlinarith [mul_nonneg hp.le (abs_nonneg c)]
  have hx' : |x|≤2 := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hA : |x+t|≤2*u := (abs_add_le _ _).trans (by dsimp [u] at *;linarith)
  have hB : 1≤|x+t| := by
    have hb := abs_add_le (x+t) (-x)
    rw [show x+t+ -x=t by ring,abs_neg] at hb
    dsimp [u] at hu;linarith
  have hc : c*(x+t)≤2*|c| *u := (le_abs_self _).trans (by rw [abs_mul];nlinarith [mul_le_mul_of_nonneg_left hA (abs_nonneg c)])
  have hu2 : u^2=t^2 := sq_abs t
  have hx2 : x^2≤4 := by nlinarith [sq_le_sq' (abs_le.mp hx').1 (abs_le.mp hx').2]
  have hg : (x^2-t^2)/(2*Real.pi)+c*(x+t)≤ -u := by
    apply le_sub_iff_add_le.mp
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    have H : 2*Real.pi*(2*|c|+2)≤u := by dsimp [u];nlinarith [mul_nonneg hp.le (abs_nonneg c)]
    nlinarith [mul_nonneg (sub_nonneg.mpr H) (show 0≤u by linarith),
      mul_nonneg hp.le (sub_nonneg.mpr hc),mul_le_mul_of_nonneg_right (show 1≤Real.pi by linarith [Real.pi_gt_three]) (show 0≤u by linarith)]
  have hz : (x:ℂ)+t*I≠0 := by
    intro h;have H := congrArg Complex.im h;simp at H;subst t;norm_num [u] at hu
  have hh := denom_bound (w:=diagonal ((x:ℂ)+t*I)) (by rw [diagonal_coordinates];exact hB)
  have hz' : ‖(x:ℂ)+t*I‖≤2*u := (Complex.norm_le_abs_re_add_abs_im _).trans (by simp;dsimp [u] at *;linarith)
  have hden : ‖mordellKernel c (diagonal ((x:ℂ)+t*I))‖≤2*Real.exp (-u) := by
    rw [mordellKernel,norm_div,norm_mordellGaussian_diagonal,div_le_iff₀ (show 0<‖Complex.exp (diagonal ((x:ℂ)+t*I))-1‖ by linarith)]
    exact (Real.exp_le_exp.mpr hg).trans (by nlinarith [mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (-u))])
  rw [regularMordell_off c hz,norm_mul]
  apply (mul_le_mul hz' hden (norm_nonneg _) (by dsimp [u];positivity)).trans
  rw [Real.exp_neg]
  apply (le_div_iff₀ (by positivity)).mpr
  field_simp
  have hh' := Real.pow_div_factorial_le_exp u (abs_nonneg t) 3
  norm_num at hh'
  nlinarith [hu2,show u≤u^3 by nlinarith [mul_nonneg (show 0≤u by linarith) (show 0≤u^2-1 by nlinarith)],show u^3/6≤Real.exp u from hh']

private theorem regularMordell_bound (c : ℝ) : ∃ D : ℝ, 0≤D ∧
    ∀ x ∈ Icc (-Real.pi/2) (Real.pi/2), ∀ t : ℝ,
      ‖regularMordell c ((x:ℂ)+t*I)‖≤D/(1+t^2) := by
  let T := 8*Real.pi*(|c|+2)+4
  let K := Icc (-Real.pi/2) (Real.pi/2) ×ˢ Icc (-T) T
  let Z (p : ℝ×ℝ) := (p.1:ℂ)+(p.2:ℂ)*I
  have hc : ContinuousOn (regularMordell c) {z : ℂ | z.re∈Icc (-Real.pi/2) (Real.pi/2)} :=
    fun z hz => (regularMordell_analytic c hz).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (fun p : ℝ×ℝ => ‖regularMordell c (Z p)‖*(1+p.2^2)) K :=
    ((hc.comp (by dsimp [Z];fun_prop) (fun p hp => by simpa [Z] using hp.1)).norm).mul (by fun_prop)
  obtain ⟨L,hL⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc'
  refine ⟨max 48 L,le_trans (by norm_num) (le_max_left _ _),?_⟩
  intro x hx t
  by_cases ht : T≤|t|
  · exact (regularMordell_tail c x t hx ht).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · apply (le_div_iff₀ (by positivity)).mpr
    exact (hL ⟨(x,t),⟨hx,abs_le.mp (not_le.mp ht).le⟩,rfl⟩).trans (le_max_right _ _)

private theorem normal_line (x t : ℝ) : diagonal ((x:ℂ)+t*I)=mordellLine (-2*x) (t+x) := by
  unfold diagonal mordellLine;push_cast;ring_nf;simp [I_sq];ring

private theorem boundary_integrable (c x : ℝ) (hx : |x|=Real.pi/2) :
    Integrable (fun t : ℝ => mordellKernel c (diagonal ((x:ℂ)+t*I))) := by
  obtain ⟨D,hD,hbound⟩ := regularMordell_bound c
  have hx' : x∈Icc (-Real.pi/2) (Real.pi/2) := by simpa only [mem_Icc,neg_div] using abs_le.mp hx.le
  have hne (t : ℝ) : Real.pi/2≤‖(x:ℂ)+t*I‖ := by simpa [hx] using Complex.abs_re_le_norm ((x:ℂ)+t*I)
  have he (t : ℝ) : (x:ℂ)+t*I≠0 := norm_pos_iff.mp ((by positivity : 0<Real.pi/2).trans_le (hne t))
  have heq (t : ℝ) : mordellKernel c (diagonal ((x:ℂ)+t*I))=regularMordell c ((x:ℂ)+t*I)/((x:ℂ)+t*I) := by
    rw [regularMordell_off c (he t)];field_simp [he t]
  simp_rw [heq]
  have hcont : Continuous (fun t : ℝ => regularMordell c ((x:ℂ)+t*I)) :=
    continuous_iff_continuousAt.mpr fun t => (regularMordell_analytic c (by simpa using hx')).continuousAt.comp
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const) : Continuous (fun t : ℝ => (x:ℂ)+t*I)).continuousAt)
  apply (integrable_inv_one_add_sq.const_mul (D/(Real.pi/2))).mono' ((hcont.div (by fun_prop) he).aestronglyMeasurable)
  filter_upwards with t
  simp only [Pi.div_apply,norm_div]
  exact (div_le_div₀ (by positivity) (hbound x hx' t) (by positivity : 0<Real.pi/2) (hne t)).trans_eq (by ring)

private theorem cauchy_to_diag (c x : ℝ) (hx : x≠0) :
    (1+I)*verticalCauchyIntegral (regularMordell c) x = mordellIntegral c (-2*x) := by
  unfold verticalCauchyIntegral mordellIntegral
  congr 1
  have he (t : ℝ) : (x:ℂ)+t*I≠0 := by intro h;have hr := congrArg Complex.re h;simpa using hx (by simpa using hr)
  have H (t : ℝ) : regularMordell c ((x:ℂ)+t*I)/((x:ℂ)+t*I)=mordellKernel c (mordellLine (-2*x) (t+x)) := by
    rw [regularMordell_off c (he t),←normal_line];field_simp [he t]
  simp_rw [H]
  exact integral_add_right_eq_self (fun s : ℝ => mordellKernel c (mordellLine (-2*x) s)) x

/-- The pole of residue one accounts for the jump between the two diagonals. -/
theorem mordellIntegral_sub (c : ℝ) :
    mordellIntegral c (-Real.pi) - mordellIntegral c Real.pi=2*Real.pi*I := by
  obtain ⟨D,hD,hbound⟩ := regularMordell_bound c
  have h := verticalCauchyIntegral_sub_neg (c:=Real.pi/2) (F:=regularMordell c)
    (fun z hz => regularMordell_analytic c (by simpa only [neg_div] using hz)) (by positivity) hD
    (fun x hx t => hbound x (by simpa only [neg_div] using hx) t)
  have hr := cauchy_to_diag c (Real.pi/2) (by positivity)
  have hl := cauchy_to_diag c (-(Real.pi/2)) (by apply neg_ne_zero.mpr;positivity)
  rw [show -2*(Real.pi/2)= -Real.pi by ring] at hr
  rw [show -2* -(Real.pi/2)=Real.pi by ring] at hl
  rw [←hr,←hl,←mul_sub,h,regularMordell,diagonal_slope_zero]
  simp [diagonal,mordellGaussian]
  have hh : (1:ℂ)-I≠0 := by intro he;have := congrArg Complex.re he;norm_num at this
  field_simp;ring_nf;simp [I_sq] <;> ring

/-- Translation by one imaginary period converts the second contour to
a linear combination of the first contour and an entire Gaussian. -/
private theorem kernel_add_period (c : ℝ) (w : ℂ) (hw : Complex.exp w≠1) :
    mordellKernel c (w+2*Real.pi*I) = Complex.exp (2*Real.pi*I*c)*
      (mordellGaussian (c-1) w-mordellKernel c w) := by
  have he : Complex.exp (w+2*Real.pi*I)=Complex.exp w := by rw [Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  have hE : mordellGaussian c (w+2*Real.pi*I)=
      -Complex.exp (2*Real.pi*I*c)*mordellGaussian (c-1) w := by
    have hh : I*(w+2*Real.pi*I)^2/(4*Real.pi)+(c:ℂ)*(w+2*Real.pi*I) =
      (Real.pi*I)+(2*Real.pi*I*c)+(I*w^2/(4*Real.pi)+((c-1:ℝ):ℂ)*w)-2*Real.pi*I := by
      push_cast;field_simp;ring_nf;simp [I_sq,I_pow_three] <;> ring
    rw [mordellGaussian,hh,Complex.exp_sub,Complex.exp_two_pi_mul_I,div_one,Complex.exp_add,Complex.exp_add,Complex.exp_pi_mul_I]
    unfold mordellGaussian;ring
  have he' : mordellGaussian (c-1) w*Complex.exp w=mordellGaussian c w := by
    unfold mordellGaussian;rw [←Complex.exp_add];congr 1;push_cast;ring
  rw [mordellKernel,hE,he,mordellKernel]
  field_simp [sub_ne_zero.mpr hw]
  rw [←he'];ring

/-- The Mordell integral evaluated as a difference of two elementary
exponentials, with no division at a half-integral parameter. -/
theorem mordellIntegral_equation (c : ℝ) :
    (1+Complex.exp (2*Real.pi*I*c))*mordellIntegral c Real.pi =
      Complex.exp (2*Real.pi*I*c)*
        (2*Real.pi*Complex.exp (I*Real.pi/4+I*Real.pi*((c-1:ℝ):ℂ)^2)-2*Real.pi*I) := by
  let x := Real.pi/2
  have hx : |x|=Real.pi/2 := abs_of_pos (by dsimp [x];positivity)
  have hk := (boundary_integrable c x hx).comp_add_right (-x)
  have hline (t : ℝ) : diagonal ((x:ℂ)+((t+ -x:ℝ):ℂ)*I)=mordellLine (-Real.pi) t := by
    rw [normal_line,show -2*x= -Real.pi by dsimp [x];ring];congr 1;ring
  simp_rw [hline] at hk
  have he (t : ℝ) : Complex.exp (mordellLine (-Real.pi) t)≠1 := by
    intro h
    obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp h
    have hr := congrArg Complex.re hn
    simp [mordellLine,mul_re,mul_im] at hr
    subst t
    simp only [mordellLine,ofReal_zero,mul_zero,zero_add,ofReal_neg,mul_neg,Complex.exp_neg,
      mul_comm I (Real.pi:ℂ),Complex.exp_pi_mul_I] at h
    norm_num at h
  have H : mordellIntegral c Real.pi = Complex.exp (2*Real.pi*I*c)*
      ((1+I)*(∫ t : ℝ,mordellGaussian (c-1) (mordellLine (-Real.pi) t))-mordellIntegral c (-Real.pi)) := by
    unfold mordellIntegral
    have hper (t : ℝ) : mordellLine Real.pi t=mordellLine (-Real.pi) t+2*Real.pi*I := by
      unfold mordellLine;push_cast;ring
    simp_rw [hper,kernel_add_period c _ (he _)]
    rw [integral_const_mul,integral_sub (integrable_mordellGaussian _ _) hk]
    ring
  rw [integral_mordellGaussian] at H
  linear_combination H - Complex.exp (2*Real.pi*I*c)*mordellIntegral_sub c


/-- The upper diagonal integral converges absolutely for every real parameter. -/
theorem integrable_mordellKernel_upper (c : ℝ) :
    Integrable (fun t : ℝ => mordellKernel c (mordellLine Real.pi t)) := by
  let x := -(Real.pi/2)
  have hx : |x|=Real.pi/2 := by dsimp [x];rw [abs_neg,abs_of_pos (by positivity)]
  have h := (boundary_integrable c x hx).comp_add_right (-x)
  have he (t : ℝ) : diagonal ((x:ℂ)+((t+ -x:ℝ):ℂ)*I)=mordellLine Real.pi t := by
    rw [normal_line,show -2*x=Real.pi by dsimp [x];ring];congr 1;ring
  simpa only [he] using h

/-- Continuity in the real parameter, including the two removable singularities
of the trigonometric expression on [0,2]. -/
theorem continuous_mordellIntegral_upper : Continuous (fun c : ℝ => mordellIntegral c Real.pi) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (continuousAt_const.mul _)
  apply continuousAt_of_dominated (bound:=fun t => ‖mordellKernel (c-1) (mordellLine Real.pi t)‖+
    ‖mordellKernel (c+1) (mordellLine Real.pi t)‖)
  · exact Filter.Eventually.of_forall fun a => (integrable_mordellKernel_upper a).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (show c-1<c by linarith) (show c<c+1 by linarith)] with a ha
    filter_upwards with t
    let w := mordellLine Real.pi t
    have hr (d : ℝ) : ‖mordellKernel d w‖=Real.exp ((I*w^2/(4*Real.pi)).re+d*w.re)/‖Complex.exp w-1‖ := by
      rw [mordellKernel,mordellGaussian,norm_div,Complex.norm_exp,add_re,Complex.re_ofReal_mul]
    rcases le_or_gt 0 w.re with h|h
    · apply le_trans _ (le_add_of_nonneg_left (norm_nonneg _))
      change ‖mordellKernel a w‖≤‖mordellKernel (c+1) w‖
      rw [hr,hr];gcongr;exact ha.2.le
    · apply le_trans _ (le_add_of_nonneg_right (norm_nonneg _))
      change ‖mordellKernel a w‖≤‖mordellKernel (c-1) w‖
      rw [hr,hr];apply div_le_div_of_nonneg_right _ (norm_nonneg _);apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonpos_right ha.1.le h.le]
  · exact (integrable_mordellKernel_upper _).norm.add (integrable_mordellKernel_upper _).norm
  · filter_upwards with t
    unfold mordellKernel mordellGaussian
    fun_prop

end AnalyticNumberTheory.AnalyticTools
