import AnalyticNumberTheory.DirichletSeries.RamachandraPolar
import Mathlib.Analysis.Complex.Liouville

/-!
# Rapid decay of the polar term

A fixed disk around the pole bounds the pole-cleared original function.
For a center varying vertically the Gamma factor decays rapidly throughout
the translated disk. Cauchy's estimate transfers this decay to every
derivative in the polar contribution, allowing polynomial smoothing lengths.
-/

open Complex Real Set Filter MeasureTheory Metric
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletSeries

/-- For a fixed finite-order pole at `q`, the residue is smaller than any
inverse power of the height, uniformly for polynomially growing smoothing lengths.
Here `s` is the evaluation point and `q-s` the pole of the shifted integrand. -/
theorem gammaSmoothingResidue_rapid_decay (W : ℂ → ℂ) (q : ℂ) (k A m : ℕ)
    {a b R : ℝ} (hR : 0<R) (ha : R<a) (hab : a≤b)
    (hW : AnalyticOnNhd ℂ W (closedBall q R)) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : ℂ) (X : ℝ), (q-s).re∈Icc a b → 1≤X →
      X≤(1+|(q-s).im|)^A →
      ‖gammaSmoothingResidue (fun w => W (s+w)) X (q-s) k‖ ≤ C/(1+|(q-s).im|)^m := by
  obtain ⟨v,_,hmax⟩ := (isCompact_closedBall q R).exists_isMaxOn
    (nonempty_closedBall.mpr hR.le) hW.continuousOn.norm
  let B := ‖W v‖+1
  have hB : 0<B := by dsimp [B]; positivity
  let d := ⌈b+R⌉₊
  let L := m+A*d
  obtain ⟨C,hC,hΓ⟩ := norm_Gamma_positive_strip_weight (a:=a-R) (b:=b+R)
    (sub_pos.mpr ha) (by linarith) L
  let D := B*((1+R)^L*C)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D/R^k,by positivity,?_⟩
  intro s X hs hX hXT
  let p := q-s
  let T := 1+|p.im|
  let J (w : ℂ) := W (s+w)*Complex.Gamma w*(X:ℂ)^w
  have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg p.im]
  have hT0 : 0<T := zero_lt_one.trans_le hT
  have hX0 := zero_lt_one.trans_le hX
  have hloc (w : ℂ) (hw : w∈closedBall p R) :
      w.re∈Icc (a-R) (b+R) ∧ s+w∈closedBall q R ∧ T≤(1+R)*(1+|w.im|) := by
    have hu : ‖w-p‖≤R := by simpa [mem_closedBall,dist_eq_norm] using hw
    have hr := abs_le.mp ((Complex.abs_re_le_norm (w-p)).trans hu)
    have hi := abs_le.mp ((Complex.abs_im_le_norm (w-p)).trans hu)
    have hσ : p.re∈Icc a b := hs
    simp only [Complex.sub_re] at hr
    refine ⟨⟨by linarith [hr.1,hσ.1],by linarith [hr.2,hσ.2]⟩,?_,?_⟩
    · rw [mem_closedBall,dist_eq_norm,show s+w-q=w-p by dsimp [p];ring]; exact hu
    · have htri : |p.im| ≤ |w.im|+R := by
        calc |p.im| = |w.im-(w-p).im| := by simp
             _ ≤ |w.im|+|(w-p).im| := abs_sub _ _
             _ ≤ _ := add_le_add_right ((Complex.abs_im_le_norm _).trans hu) _
      dsimp [T]
      nlinarith only [htri,mul_nonneg hR.le (abs_nonneg w.im)]
  have han : DifferentiableOn ℂ J (closedBall p R) := by
    intro w hw
    obtain ⟨hwre,hws,_⟩ := hloc w hw
    have hga := Gamma.analyticOnNhd_gamma w (Gamma.mem_nonPoleSet_of_re_pos ((sub_pos.mpr ha).trans_le hwre.1))
    have hpw : DifferentiableAt ℂ (fun w : ℂ => (X:ℂ)^w) w :=
      (differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hX0.ne'))).differentiableAt
    exact ((((hW _ hws).comp (analyticAt_const.add analyticAt_id)).differentiableAt.mul hga.differentiableAt).mul hpw).differentiableWithinAt
  have hcircle (w : ℂ) (hw : w∈sphere p R) : ‖J w‖≤D/T^m := by
    obtain ⟨hσ,hws,ht⟩ := hloc w (sphere_subset_closedBall hw)
    have hG : T^L*‖Complex.Gamma w‖ ≤ (1+R)^L*C := by
      calc _ ≤ ((1+R)*(1+|w.im|))^L*‖Complex.Gamma w‖ := by gcongr
           _ = (1+R)^L*((1+|w.im|)^L*‖Complex.Gamma w‖) := by rw [mul_pow];ring
           _ ≤ _ := by gcongr; exact hΓ w hσ
    have hxw : ‖(X:ℂ)^w‖ ≤ T^(A*d) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0,pow_mul]
      calc X^w.re ≤ X^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (hσ.2.trans (Nat.le_ceil _))
           _ = X^d := Real.rpow_natCast _ _
           _ ≤ _ := pow_le_pow_left₀ hX0.le hXT _
    have hwB : ‖W (s+w)‖≤B := (hmax hws).trans (by dsimp [B];linarith)
    rw [le_div_iff₀ (pow_pos hT0 _)]
    dsimp [J]; rw [norm_mul,norm_mul]
    calc _ ≤ B*‖Complex.Gamma w‖*T^(A*d)*T^m := by gcongr
         _ = B*(T^L*‖Complex.Gamma w‖) := by dsimp [L];rw [pow_add];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hG hB.le
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
    (han.diffContOnCl_ball (fun _ h => h)) hcircle
  change ‖iteratedDeriv k J p/(k.factorial:ℂ)‖ ≤ D/R^k/T^m
  rw [norm_div,Complex.norm_natCast]
  have hf : 0<(k.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  apply (div_le_div_of_nonneg_right hh hf.le).trans_eq
  field_simp

/-- Ramachandra's uniform approximation with power-saving polar error. The
same constant works for every admissible center, smoothing length and dual cutoff. -/
theorem ramachandra_smoothed_functional_equation_error {a b : ℕ → ℂ} {F ψ W : ℂ → ℂ}
    (q : ℂ) (k A m : ℕ) {u v R l r d : ℝ} (hR : 0<R) (hu : R<u) (huv : u≤v)
    (hvr : v<r) (hl : -1<l) (hl0 : l<0) (hd : 0<d)
    (hW : AnalyticOnNhd ℂ W (closedBall q R))
    (hrep : ∀ z : ℂ, z≠q → F z=W z/(z-q)^(k+1)) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : ℂ) (X : ℝ) (N : ℕ), (q-s).re∈Icc u v →
      1≤X → X≤(1+|(q-s).im|)^A →
      (∀ t : ℝ, LSeriesHasSum a (s+((r:ℂ)+t*I)) (F (s+((r:ℂ)+t*I)))) →
      (∀ t : ℝ, let z := s+((l:ℂ)+t*I)
        ∃ D : ℂ, LSeriesHasSum b (1-z) D ∧ F z=ψ z*D) →
      PolynomialGrowthOnStrip (fun w => W (s+w)) l r →
      PolynomialGrowthOnStrip (fun w => ψ (s+w)) l d →
      ‖F s - ((∑' n : ℕ, LSeries.term a s n*(Real.exp (-(n:ℝ)/X):ℂ)) +
        ψ s*dirichletPartialSum b (1-s) N -
        gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletTail b (1-(s+w)) N) X l -
        gammaSmoothingIntegral (fun w => ψ (s+w)*dirichletPartialSum b (1-(s+w)) N) X d)‖
        ≤ C/(1+|(q-s).im|)^m := by
  obtain ⟨C,hC,H⟩ := gammaSmoothingResidue_rapid_decay W q k A m hR hu huv hW
  refine ⟨C,hC,?_⟩
  intro s X N hs hX hXT hF hFE hg hψ
  have hrepr (w : ℂ) (hw : w≠q-s) : F (s+w)=W (s+w)/(w-(q-s))^(k+1) := by
    have hz : s+w≠q := by intro he; apply hw; linear_combination he
    rw [hrep _ hz,show s+w-q=w-(q-s) by ring]
  have he := ramachandra_smoothed_functional_equation_with_pole s N k hl hl0
    ((hR.trans hu).trans_le hs.1) (hs.2.trans_lt hvr) hd (zero_lt_one.trans_le hX)
    hF hFE hg hrepr hψ
  rw [he,show ∀ x y : ℂ, x-y-x = -y by intro x y; abel,norm_neg]
  exact H s X hs hX hXT

end AnalyticNumberTheory.DirichletSeries
