import AnalyticNumberTheory.DirichletLFunctions.PeriodicCriticalPolynomial
import AnalyticNumberTheory.DirichletLFunctions.PeriodicHarmonicConstant

/-!
# The two harmonic diagonals of a periodic critical-line moment

The original and reciprocal coefficient functions give distinct digamma
constants. Parseval equates the coefficients of their logarithms.
-/
noncomputable section
open Real Finset Set MeasureTheory Filter
open scoped Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- Coefficient of the linear term after subtracting the scaled
`T log(T/(2π))` main term. -/
def periodicMomentLinearTerm {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) :=
  periodicHarmonicConstant Φ+periodicHarmonicConstant (periodicDualWeight Φ)-
    periodicNormMean Φ*(Real.log q+1)

private theorem value_error {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) {t : ℝ} (ht : 8*Real.pi*q≤t) :
    let k := periodicNormMean Φ
    |periodicCriticalDiagonal Φ t-(k*Real.log (t/(2*Real.pi))+periodicMomentLinearTerm Φ+k)|≤
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
  have h₁ := periodic_harmonic_constant_error Φ hx
  have h₂ := periodic_harmonic_constant_error (periodicDualWeight Φ) hx
  rw [periodicNormMean_dualWeight] at h₂
  have hlog : 2*Real.log x=Real.log (t/(2*Real.pi))-Real.log q := by
    dsimp [x];rw [Real.log_sqrt (by positivity),Real.log_div ht'.ne' (mul_ne_zero hπ.ne' hq.ne'),
      Real.log_div ht'.ne' hπ.ne',Real.log_mul hπ.ne' hq.ne'];ring
  have hxs : 1/x=Real.sqrt (2*Real.pi*q)/Real.sqrt t := by dsimp [x];rw [Real.sqrt_div ht'.le];field_simp
  let L := fun (Ψ : ZMod q→ℂ) => ∑n∈Finset.Icc 1 ⌊(q:ℝ)*x⌋₊,‖Ψ n‖^2/(n:ℝ)
  change |L Φ-(k*Real.log x+periodicHarmonicConstant Φ)|≤4*k/x at h₁
  change |L (periodicDualWeight Φ)-(k*Real.log x+periodicHarmonicConstant (periodicDualWeight Φ))|≤4*k/x at h₂
  have he : periodicCriticalDiagonal Φ t=L Φ+L (periodicDualWeight Φ) := by simp only [periodicCriticalDiagonal,hl,add_div,sum_add_distrib,L]
  rw [he,show L Φ+L (periodicDualWeight Φ)-(k*Real.log (t/(2*Real.pi))+periodicMomentLinearTerm Φ+k)=
    (L Φ-(k*Real.log x+periodicHarmonicConstant Φ))+(L (periodicDualWeight Φ)-(k*Real.log x+periodicHarmonicConstant (periodicDualWeight Φ))) by
      dsimp only [periodicMomentLinearTerm,k];linear_combination (periodicNormMean Φ)*hlog]
  apply ((abs_add_le ..).trans (add_le_add h₁ h₂)).trans_eq
  calc 4*k/x+4*k/x = 8*k*(1/x) := by ring
       _ = _ := by rw [hxs];ring

theorem periodicCriticalDiagonal_monotone {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) : Monotone (periodicCriticalDiagonal Φ) := by
  intro t u h;apply sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right ?_) (fun _ _ _ => by positivity)
  apply Nat.floor_mono;apply Real.sqrt_le_sqrt;exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q)) (by positivity)

/-- Integral of the periodic diagonal with its explicit secondary term. -/
theorem periodic_critical_diagonal_expansion {q : ℕ} [NeZero q] (Φ : ZMod q→ℂ) :
    ∃ C : ℝ,0<C ∧ ∀{T : ℝ},8*Real.pi*q≤T →
    |(∫t in (8*Real.pi*q)..T,periodicCriticalDiagonal Φ t)-
      (periodicNormMean Φ*(T*Real.log (T/(2*Real.pi)))+periodicMomentLinearTerm Φ*T)|≤C*Real.sqrt T := by
  let a := 8*Real.pi*q
  let k := periodicNormMean Φ
  let c := periodicMomentLinearTerm Φ
  let f := fun t => k*Real.log (t/(2*Real.pi))+c+k
  let F := fun t => k*(t*Real.log (t/(2*Real.pi)))+c*t
  let m := 8*k*Real.sqrt (2*Real.pi*q)
  let g := fun t : ℝ => m/Real.sqrt t
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have ha : 1≤a := by dsimp [a];nlinarith [Real.pi_gt_three,mul_le_mul_of_nonneg_left hq₁ (show 0≤8*Real.pi by positivity)]
  have ha' := zero_lt_one.trans_le ha
  have hm : 0≤m := by dsimp [m,k,periodicNormMean];positivity
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
  have H := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) (f:=fun t=>periodicCriticalDiagonal Φ t-f t) (g:=g)
    (show a≤T from hT) (Eventually.of_forall (fun t ht => by rw [Real.norm_eq_abs];exact value_error Φ ht.1.le)) hg.intervalIntegrable
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub (periodicCriticalDiagonal_monotone Φ).intervalIntegrable hf.intervalIntegrable,
    hmain,hmaj] at H
  have hT₁ : 1≤Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  let I := ∫t in a..T,periodicCriticalDiagonal Φ t
  change |I-(F T-F a)|≤_ at H
  change |I-F T|≤_
  rw [show I-F T=(I-(F T-F a))-F a by ring]
  linarith only [abs_sub (I-(F T-F a)) (F a),H,le_mul_of_one_le_right (abs_nonneg (F a)) hT₁,
    mul_nonneg hm (Real.sqrt_nonneg a),Real.sqrt_nonneg T]

end AnalyticNumberTheory.DirichletLFunctions
