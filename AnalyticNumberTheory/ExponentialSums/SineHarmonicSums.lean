import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Uniform cancellation in sine harmonic sums

Radially damp the harmonic polynomial at radius 1−1/(N+1). Replacing
the finite sum by the Taylor series for the complex logarithm costs at
most two in norm. The imaginary part of the logarithm is uniformly bounded.
-/
noncomputable section
open Real Complex Finset Filter
open scoped ComplexConjugate
namespace AnalyticNumberTheory.ExponentialSums

private theorem radial_power (r : ℝ) (hr : 0≤r) (hr' : r≤1) (n : ℕ) :
    1-r^n≤n*(1-r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hr hr' (n:=n))) (sub_nonneg.mpr hr')]

/-- Approximation of a harmonic polynomial on the unit circle by a
radially regularized logarithm, uniformly in its length. -/
theorem norm_harmonic_sum_add_log_le (N : ℕ) {z : ℂ} (hz : ‖z‖=1) :
    ‖(∑ j∈range N,z^(j+1)/((j:ℂ)+1))+Complex.log (1-(1-1/((N:ℝ)+1):ℝ)*z)‖ ≤ 2 := by
  let d : ℝ := 1/((N:ℝ)+1)
  let r : ℝ := 1-d
  let f (j : ℕ) := ((r:ℂ)*z)^(j+1)/((j:ℂ)+1)
  let g (j : ℕ) := z^(j+1)/((j:ℂ)+1)
  have hd : 0<d := by dsimp [d]; positivity
  have hd' : d≤1 := by dsimp [d]; rw [div_le_one (by positivity)];linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hr : 0≤r := sub_nonneg.mpr hd'
  have hr' : r<1 := by dsimp [r]; linarith
  have hs : HasSum f (-Complex.log (1-(r:ℂ)*z)) := Complex.hasSum_taylorSeries_neg_log' (by simpa [hz,abs_of_nonneg hr] using hr')
  have H₁ : ‖∑ j∈range N,(g j-f j)‖≤1 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j∈range N,d := by
        apply sum_le_sum
        intro j hj
        have ht : g j-f j=(((1-r^(j+1):ℝ):ℂ)*z^(j+1))/((j:ℂ)+1) := by dsimp [g,f];push_cast;rw [mul_pow];ring
        rw [ht,norm_div,norm_mul,norm_pow,hz,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hr hr'.le)),
          ←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (by positivity),div_le_iff₀ (by positivity)]
        have hh := radial_power r hr hr'.le (j+1)
        simpa [r,mul_comm] using hh
      _ ≤ 1 := by simp [d]; rw [←div_eq_mul_inv,div_le_one (by positivity)];linarith
  have hmajor := (hasSum_geometric_of_lt_one hr hr').mul_left d
  have H₂ : ‖∑' j : ℕ, f (j+N)‖≤1 := by
    apply (norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hs.summable).norm).trans
    refine (Summable.tsum_le_tsum ?_ ?_ hmajor.summable).trans ?_
    · intro j
      dsimp only [f]
      rw [norm_div,norm_pow,norm_mul,hz,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,
        ←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hpow : r^(j+N+1)≤r^j := pow_le_pow_of_le_one hr hr'.le (by omega)
      dsimp [d]
      calc
        _ ≤ r^j/((N:ℝ)+1) := by
          apply div_le_div₀ (by positivity) hpow (by positivity)
          push_cast;linarith [Nat.cast_nonneg (α:=ℝ) j]
        _ = _ := by ring
    · exact ((summable_nat_add_iff N).mpr hs.summable).norm
    · rw [hmajor.tsum_eq]; dsimp [r,d];field_simp;linarith
  have He := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at He
  change ‖(∑ j∈range N,g j)+Complex.log (1-(r:ℂ)*z)‖≤2
  rw [show (∑ j∈range N,g j)+Complex.log (1-(r:ℂ)*z)=
      (∑ j∈range N,(g j-f j))-(∑' j : ℕ,f (j+N)) by rw [sum_sub_distrib];linear_combination He]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Uniform boundedness of the imaginary part of the truncated logarithm. -/
theorem abs_im_harmonic_sum_le (N : ℕ) {z : ℂ} (hz : ‖z‖=1) :
    |(∑ j∈range N,z^(j+1)/((j:ℂ)+1)).im| ≤ Real.pi+2 := by
  have H := norm_harmonic_sum_add_log_le N hz
  let w := 1-((1-1/((N:ℝ)+1):ℝ):ℂ)*z
  let S := ∑ j∈range N,z^(j+1)/((j:ℂ)+1)
  have H₁ := (Complex.abs_im_le_norm (S+Complex.log w)).trans H
  have H₂ : |(Complex.log w).im|≤Real.pi := by rw [Complex.log_im];exact Complex.abs_arg_le_pi _
  change |S.im|≤_
  rw [show S.im=(S+Complex.log w).im-(Complex.log w).im by simp]
  exact (abs_sub _ _).trans (by linarith)

/-- Symmetric truncated discrete Hilbert kernel, including arbitrarily
small angles and integral multiples of a full turn. -/
theorem norm_symmetric_harmonic_sum_le (N : ℕ) {z : ℂ} (hz : ‖z‖=1) :
    ‖∑ j∈range N,(z^(j+1)-(conj z)^(j+1))/((j:ℂ)+1)‖≤2*(Real.pi+2) := by
  let S := ∑ j∈range N,z^(j+1)/((j:ℂ)+1)
  have he : (∑ j∈range N,(z^(j+1)-(conj z)^(j+1))/((j:ℂ)+1))=S-conj S := by
    dsimp [S];rw [map_sum,←sum_sub_distrib];congr 1;funext j
    simp [map_div₀,Complex.conj_natCast,Complex.conj_ofNat,sub_div]
  rw [he,Complex.sub_conj,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs]
  simpa [abs_mul,S] using mul_le_mul_of_nonneg_left (abs_im_harmonic_sum_le N hz) (show (0:ℝ)≤2 by norm_num)

end AnalyticNumberTheory.ExponentialSums
