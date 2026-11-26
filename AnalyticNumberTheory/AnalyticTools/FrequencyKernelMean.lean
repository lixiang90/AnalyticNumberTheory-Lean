import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # A mean-square estimate for exponential sums with arbitrary real frequencies -/

noncomputable section

open Complex Real Finset Set MeasureTheory
open scoped ComplexConjugate

namespace AnalyticNumberTheory.AnalyticTools

/-- A finite exponential polynomial with phases exp(iωt). Repeated frequencies are allowed. -/
def frequencyPolynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i*Complex.exp ((ω i*t:ℝ)*I)

private def gaussPair (d t : ℝ) : ℂ :=
  Complex.exp (-(t:ℂ)^2+((d*t:ℝ):ℂ)*I)

private theorem gaussPair_integrable (d : ℝ) : Integrable (gaussPair d) := by
  apply (integrable_cexp_quadratic (b := (1:ℂ)) (by norm_num) ((d:ℂ)*I) 0).congr
  filter_upwards with t
  dsimp only [gaussPair]
  congr 1
  push_cast
  ring

private theorem gaussPair_norm_integral (d : ℝ) :
    ‖∫ t, gaussPair d t‖ = ‖(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (-d^2/4) := by
  have he : gaussPair d = fun t : ℝ => Complex.exp ((-1:ℂ)*t^2+((d:ℂ)*I)*t+0) := by
    funext t
    dsimp only [gaussPair]
    congr 1
    push_cast
    ring
  rw [he,integral_cexp_quadratic (b := (-1:ℂ)) (by norm_num),norm_mul,Complex.norm_exp]
  simp [mul_pow,Complex.I_sq]
  <;> ring_nf
  <;> simp [←Complex.ofReal_pow]

private theorem gaussian_mean_le {ι : Type*} (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) (L : ℝ) :
    (∫ t : ℝ, Real.exp (-t^2)*‖frequencyPolynomial S c ω (L*t)‖^2) ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖c i‖*‖c j‖*(‖(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (-(L*(ω i-ω j))^2/4)) := by
  let G (t : ℝ) := Real.exp (-t^2)*‖frequencyPolynomial S c ω (L*t)‖^2
  let f (i j : ι) (t : ℝ) := (c i*conj (c j))*gaussPair (L*(ω i-ω j)) t
  have hi (i j : ι) : Integrable (f i j) := (gaussPair_integrable _).const_mul _
  have he (t : ℝ) : ((G t:ℝ):ℂ) = ∑ i ∈ S, ∑ j ∈ S, f i j t := by
    let P := frequencyPolynomial S c ω (L*t)
    have hp : ((‖P‖^2:ℝ):ℂ) = P*conj P := by
      rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
    change (((Real.exp (-t^2)*‖P‖^2:ℝ):ℂ)) = _
    rw [Complex.ofReal_mul,hp]
    dsimp only [P,frequencyPolynomial]
    rw [map_sum,Finset.sum_mul,Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    dsimp only [f,gaussPair]
    rw [map_mul,←Complex.exp_conj,Complex.ofReal_exp]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,Complex.ofReal_pow]
    rw [show Complex.exp (-(t:ℂ)^2) *
      (c i*Complex.exp ((ω i*(L*t):ℝ)*I) * (conj (c j)*Complex.exp (((ω j*(L*t):ℝ):ℂ)* -I))) =
      (c i*conj (c j))*(Complex.exp (-(t:ℂ)^2)*Complex.exp ((ω i*(L*t):ℝ)*I)*
        Complex.exp (((ω j*(L*t):ℝ):ℂ)* -I)) by ring]
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hh : ((∫ t, G t : ℝ):ℂ) = ∑ i ∈ S, ∑ j ∈ S, (c i*conj (c j))*
      ∫ t, gaussPair (L*(ω i-ω j)) t := by
    rw [←integral_complex_ofReal (f := G)]
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    apply sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    exact sum_congr rfl fun j _ => integral_const_mul _ _
  calc
    _ ≤ ‖((∫ t, G t : ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ _ := by
      rw [hh]
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro i _
      apply (norm_sum_le ..).trans_eq
      apply sum_congr rfl
      intro j _
      rw [norm_mul,norm_mul,Complex.norm_conj,gaussPair_norm_integral]

/-- A Gaussian majorant bounds the mean square on [0,L] by the pair correlation
kernel 1/(1+(ωᵢ−ωⱼ)²). The bound is uniform for L ≥ 1 and requires no spacing. -/
theorem frequencyPolynomial_mean_square_kernel :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type} (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) {L : ℝ}, 1 ≤ L →
      (∫ u in (0:ℝ)..L, ‖frequencyPolynomial S c ω u‖^2) ≤
        K*L*∑ i ∈ S, ∑ j ∈ S, ‖c i‖*‖c j‖/(1+(ω i-ω j)^2) := by
  let A := ‖(Real.pi:ℂ)^(1/2:ℂ)‖
  have hA : 0 ≤ A := norm_nonneg _
  refine ⟨Real.exp 1*(4*(A+1)),by positivity [Real.exp_pos 1],?_⟩
  intro ι S c ω L hL
  let F (t : ℝ) := ‖frequencyPolynomial S c ω (L*t)‖^2
  let G (t : ℝ) := Real.exp (-t^2)*F t
  have hc : Continuous F := by unfold F frequencyPolynomial; fun_prop
  have hG : Integrable G := by
    apply ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1)).mul_const ((∑ i ∈ S, ‖c i‖)^2)).mono'
      (show Continuous G by dsimp [G]; fun_prop).aestronglyMeasurable
    filter_upwards with t
    change ‖Real.exp (-t^2)*F t‖ ≤ Real.exp (-1*t^2)*(∑ i ∈ S, ‖c i‖)^2
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)),neg_one_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [frequencyPolynomial,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one] using
      (norm_sum_le S (fun i => c i*Complex.exp ((ω i*(L*t):ℝ)*I)))
  have hunit : (∫ t in (0:ℝ)..1, F t) ≤ Real.exp 1*∫ t, G t := by
    rw [intervalIntegral.integral_of_le zero_le_one,←integral_const_mul]
    apply (setIntegral_mono_on (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((hG.const_mul _).integrableOn) measurableSet_Ioc ?_).trans
    · exact setIntegral_le_integral (hG.const_mul _) (ae_of_all _ fun t => by
        dsimp [G,F]; positivity)
    · intro t ht
      change F t ≤ Real.exp 1*(Real.exp (-t^2)*F t)
      rw [←mul_assoc,←Real.exp_add]
      exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_exp_iff.mpr (by
        nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]))
  have hpair (d : ℝ) : A*Real.exp (-(L*d)^2/4) ≤ 4*(A+1)/(1+d^2) := by
    let u := (L*d)^2/4
    have hsq : d^2 ≤ (L*d)^2 := by
      rw [mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (by nlinarith [sq_nonneg (L-1)])
    have hu : 1+d^2 ≤ 4*Real.exp u := by dsimp [u]; nlinarith [Real.add_one_le_exp ((L*d)^2/4)]
    rw [show -(L*d)^2/4 = -u by dsimp [u]; ring,Real.exp_neg]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (A*(Real.exp u)⁻¹)*(4*Real.exp u) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = 4*A := by field_simp
      _ ≤ _ := by linarith
  have hsum := gaussian_mean_le S c ω L
  have hbound : (∫ t, G t) ≤ (4*(A+1))*∑ i ∈ S, ∑ j ∈ S, ‖c i‖*‖c j‖/(1+(ω i-ω j)^2) := by
    apply hsum.trans
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro j _
    simpa only [A,div_eq_mul_inv,mul_left_comm,mul_assoc,mul_comm] using
      mul_le_mul_of_nonneg_left (hpair (ω i-ω j)) (mul_nonneg (norm_nonneg (c i)) (norm_nonneg (c j)))
  have hscale := intervalIntegral.smul_integral_comp_mul_left (fun u => ‖frequencyPolynomial S c ω u‖^2)
    (a := (0:ℝ)) (b := 1) L
  simp only [smul_eq_mul,mul_zero,mul_one] at hscale
  rw [←hscale]
  exact (mul_le_mul_of_nonneg_left (hunit.trans (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le))
    (zero_le_one.trans hL)).trans_eq (by ring)

/-- The elementary estimate 2ab ≤ a²+b² for a nonnegative symmetric kernel.
The row on the right carries the same multiplicity weights as the quadratic form. -/
theorem weighted_kernel_quadratic_le {ι : Type*} (S : Finset ι) (m b : ι → ℝ) (k : ι → ι → ℝ)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hk : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ k i j)
    (hs : ∀ i ∈ S, ∀ j ∈ S, k i j = k j i) :
    (∑ i ∈ S, ∑ j ∈ S, (m i*b i)*(m j*b j)*k i j) ≤
      ∑ i ∈ S, (m i*(b i)^2)*(∑ j ∈ S,m j*k i j) := by
  let E (i j : ι) := (m i*(b i)^2)*(m j*k i j)
  have he (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (m i*b i)*(m j*b j)*k i j ≤ (E i j+E j i)/2 := by
    dsimp only [E]
    rw [←hs i hi j hj]
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg (hm i hi) (hm j hj)) (hk i hi j hj))
      (sq_nonneg (b i-b j))]
  apply (sum_le_sum fun i hi => sum_le_sum (he i hi)).trans_eq
  simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [show (∑ i ∈ S, ∑ j ∈ S,E j i) = ∑ i ∈ S, ∑ j ∈ S,E i j from Finset.sum_comm]
  rw [show ∀ y : ℝ, (y+y)/2 = y by intro y; ring]
  apply sum_congr rfl
  intro i _
  exact (Finset.mul_sum ..).symm

end AnalyticNumberTheory.AnalyticTools
