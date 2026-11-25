import AnalyticNumberTheory.DirichletLFunctions.ReducedHarmonicSum
import AnalyticNumberTheory.DirichletLFunctions.PrimitiveMovingWaves

/-!
# The diagonal and linear term of the primitive-character moment

Squaring the two polynomial amplitudes gives the reduced harmonic sum
twice. Its integrated secondary term contains the conductor correction.
-/
noncomputable section
open Real Finset Set MeasureTheory Filter
open scoped Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The linear coefficient after the term (φ(q)/q) T log(T/(2π)). -/
def primitiveMomentLinearTerm (q : ℕ) [NeZero q] :=
  2*reducedHarmonicConstant q-(q.totient/q:ℝ)*(Real.log q+1)

private theorem value_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 8*Real.pi*q≤t) :
    let k := (q.totient/q:ℝ)
    |primitiveCriticalDiagonal χ t-(k*Real.log (t/(2*Real.pi))+primitiveMomentLinearTerm q+k)|≤
      8*k*Real.sqrt (2*Real.pi*q)/Real.sqrt t := by
  intro k
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hπ : 0<2*Real.pi := by positivity
  have ht' : 0<t := (by positivity : 0<8*Real.pi*q).trans_le ht
  let x := Real.sqrt (t/(2*Real.pi*q))
  have hx : 2≤x := Real.le_sqrt_of_sq_le ((le_div_iff₀ (by positivity : 0<2*Real.pi*q)).mpr (by linarith))
  have ht₂ : x^2=t/(2*Real.pi*q) := Real.sq_sqrt (by positivity)
  have hl : primitiveCriticalLength q t=⌊(q:ℝ)*x⌋₊ := by
    unfold primitiveCriticalLength;congr 1
    rw [←Real.sqrt_sq (mul_nonneg hq.le (Real.sqrt_nonneg _))];congr 1;rw [mul_pow,ht₂];field_simp
  have h := mul_le_mul_of_nonneg_left (reduced_harmonic_sum_error χ hx) (by norm_num : (0:ℝ)≤2)
  rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_mul] at h
  have hlog : 2*Real.log x=Real.log (t/(2*Real.pi))-Real.log q := by
    dsimp [x];rw [Real.log_sqrt (by positivity),Real.log_div ht'.ne' (mul_ne_zero hπ.ne' hq.ne'),
      Real.log_div ht'.ne' hπ.ne',Real.log_mul hπ.ne' hq.ne'];ring
  have hxs : 1/x=Real.sqrt (2*Real.pi*q)/Real.sqrt t := by
    dsimp [x];rw [Real.sqrt_div ht'.le];field_simp
  simp only [abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  unfold primitiveCriticalDiagonal;rw [hl]
  change |2*_-(k*_+primitiveMomentLinearTerm q+k)|≤_
  apply le_trans (b:=2*(4*k/x))
  · convert h using 1
    congr 1;dsimp only [primitiveMomentLinearTerm,k];linear_combination ((q.totient/q:ℝ))*hlog
  · exact le_of_eq (calc 2*(4*k/x)=8*k*(1/x) := by ring
                         _ = 8*k*(Real.sqrt (2*Real.pi*q)/Real.sqrt t) := by rw [hxs]
                         _ = _ := by ring)

theorem primitiveCriticalDiagonal_monotone {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Monotone (primitiveCriticalDiagonal χ) := by
  intro t u h;apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right ?_) (fun _ _ _ => by positivity)
  apply Nat.floor_mono;apply Real.sqrt_le_sqrt;exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q)) (by positivity)

/-- Integrated primitive-character harmonic diagonal, with square-root
error for each fixed positive modulus. -/
theorem primitive_critical_diagonal_expansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi*q≤T →
    |(∫t in (8*Real.pi*q)..T,primitiveCriticalDiagonal χ t)-
      ((q.totient/q:ℝ)*(T*Real.log (T/(2*Real.pi)))+primitiveMomentLinearTerm q*T)|≤C*Real.sqrt T := by
  let a := 8*Real.pi*q
  let k := (q.totient/q:ℝ)
  let c := primitiveMomentLinearTerm q
  let f := fun t => k*Real.log (t/(2*Real.pi))+c+k
  let F := fun t => k*(t*Real.log (t/(2*Real.pi)))+c*t
  let m := 8*k*Real.sqrt (2*Real.pi*q)
  let g := fun t : ℝ => m/Real.sqrt t
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have ha : 1≤a := by dsimp [a];nlinarith [Real.pi_gt_three,mul_le_mul_of_nonneg_left hq₁ (show 0≤8*Real.pi by positivity)]
  have ha' := zero_lt_one.trans_le ha
  have hm : 0≤m := by dsimp [m,k];positivity
  refine ⟨2*m+|F a|+1,by positivity,?_⟩
  intro T hT
  have hp {t : ℝ} (ht : t∈uIcc a T) : 0<t := by rw [uIcc_of_le (show a≤T from hT)] at ht;exact ha'.trans_le ht.1
  have hf : ContinuousOn f (uIcc a T) := by intro t ht;dsimp [f];fun_prop (disch := positivity [hp ht])
  have hg : ContinuousOn g (uIcc a T) := by intro t ht;dsimp [g];fun_prop (disch := positivity [hp ht])
  have hmain : (∫t in a..T,f t)=F T-F a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hf.intervalIntegrable
    intro t ht
    have h := ((hasDerivAt_id' t).div_const (2*Real.pi)).log (div_pos (hp ht) (by positivity)).ne'
    convert (((hasDerivAt_id' t).mul h).const_mul k).add ((hasDerivAt_id' t).const_mul c) using 1
    dsimp [f];field_simp [(hp ht).ne',Real.pi_ne_zero] <;>ring
  have hmaj : (∫t in a..T,g t)=2*m*Real.sqrt T-2*m*Real.sqrt a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t=>2*m*Real.sqrt t) _ hg.intervalIntegrable
    intro t ht
    convert (Real.hasDerivAt_sqrt (hp ht).ne').const_mul (2*m) using 1;dsimp [g];ring
  have H := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) (f:=fun t=>primitiveCriticalDiagonal χ t-f t) (g:=g)
    (show a≤T from hT) (Eventually.of_forall (fun t ht => by rw [Real.norm_eq_abs];exact value_error χ ht.1.le)) hg.intervalIntegrable
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub (primitiveCriticalDiagonal_monotone χ).intervalIntegrable hf.intervalIntegrable,
    hmain,hmaj] at H
  have hT₁ : 1≤Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  let I := ∫t in a..T,primitiveCriticalDiagonal χ t
  change |I-(F T-F a)|≤_ at H
  change |I-F T|≤_
  rw [show I-F T=(I-(F T-F a))-F a by ring]
  linarith only [abs_sub (I-(F T-F a)) (F a),H,le_mul_of_one_le_right (abs_nonneg (F a)) hT₁,
    mul_nonneg hm (Real.sqrt_nonneg a),Real.sqrt_nonneg T]

end AnalyticNumberTheory.DirichletLFunctions
