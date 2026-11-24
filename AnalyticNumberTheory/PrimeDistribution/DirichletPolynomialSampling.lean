import AnalyticNumberTheory.SieveMethods.DirichletPolynomials
import AnalyticNumberTheory.PrimeDistribution.ExplicitFormula

/-!
# Sampling Dirichlet polynomials in a strip

The evaluation points may have different real parts. A unit-interval Sobolev
inequality is applied first horizontally and then vertically. A local bound on
the number of ordinates in each unit interval becomes the multiplicity factor.
-/

noncomputable section

open Finset MeasureTheory Complex
open scoped Classical Topology
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods

namespace AnalyticNumberTheory.PrimeDistribution

private theorem sobolev_square_unit {f g : ℝ → ℂ} {a x : ℝ} (hx : x ∈ Set.Icc a (a+1))
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : Continuous g) :
    ‖f x‖^2 ≤ ∫ t in a..a+1, (2*‖f t‖^2 + ‖g t‖^2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  let F (t : ℝ) := (f t)^2
  let G (t : ℝ) := 2 * f t * g t
  have hFG (t : ℝ) : HasDerivAt F (G t) t := by
    change HasDerivAt (fun u => f u ^ 2) (2*f t*g t) t
    convert (hf t).mul (hf t) using 1
    · ext u; simp [pow_two]
    · ring
  have hG : Continuous G := (continuous_const.mul hfc).mul hg
  have hh := gallagher_sobolev_pointwise (by linarith : a<a+1) hx (fun t _ => hFG t) hG.continuousOn
  simp only [F,G,norm_pow,add_sub_cancel_left,inv_one,one_mul,norm_mul,Complex.norm_ofNat] at hh
  apply hh.trans
  rw [← intervalIntegral.integral_add (f:=fun t => ‖f t‖^2) (g:=fun t => 2*‖f t‖*‖g t‖) ((hfc.norm.pow 2).intervalIntegrable ..)
    (((continuous_const.mul hfc.norm).mul hg.norm).intervalIntegrable ..)]
  apply intervalIntegral.integral_mono_on (by linarith)
    (((hfc.norm.pow 2).add ((continuous_const.mul hfc.norm).mul hg.norm)).intervalIntegrable ..)
    (((continuous_const.mul (hfc.norm.pow 2)).add (hg.norm.pow 2)).intervalIntegrable ..)
  intro t _
  change ‖f t‖^2 + 2*‖f t‖*‖g t‖ ≤ 2*‖f t‖^2+‖g t‖^2
  nlinarith [sq_nonneg (‖f t‖-‖g t‖)]

private def logTwist (a : ℕ → ℂ) (k n : ℕ) : ℂ := a n * (-Complex.log n)^k

private def poly (a : ℕ → ℂ) (N k : ℕ) (u t : ℝ) : ℂ :=
  dirichletPoly (logTwist a k) N ((u:ℂ)+(t:ℂ)*I)

private lemma poly_hasDeriv {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (hg : HasDerivAt g g' x)
    (a : ℕ → ℂ) (N k : ℕ) :
    HasDerivAt (fun t => dirichletPoly (logTwist a k) N (g t))
      (g' * dirichletPoly (logTwist a (k+1)) N (g x)) x := by
  unfold dirichletPoly
  rw [mul_sum]
  apply HasDerivAt.fun_sum
  intro n hn
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
  simp_rw [Complex.cpow_def_of_ne_zero hn0]
  have he := ((hg.neg.const_mul (Complex.log n)).cexp).const_mul (logTwist a k n)
  convert he using 1; dsimp [logTwist]; ring

private lemma poly_dr (a : ℕ → ℂ) (N k : ℕ) (u t : ℝ) :
    HasDerivAt (fun r => poly a N k r t) (poly a N (k+1) u t) u := by
  have h := poly_hasDeriv ((Complex.ofRealCLM.hasDerivAt (x:=u)).add_const ((t:ℂ)*I)) a N k
  simpa [poly] using h

private lemma poly_dt (a : ℕ → ℂ) (N k : ℕ) (u t : ℝ) :
    HasDerivAt (fun v => poly a N k u v) (I*poly a N (k+1) u t) t := by
  have h := poly_hasDeriv ((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const I |>.const_add (u:ℂ)) a N k
  simpa [poly] using h

private lemma continuous_poly_r (a : ℕ → ℂ) (N k : ℕ) (t : ℝ) : Continuous fun u => poly a N k u t :=
  continuous_iff_continuousAt.mpr fun _ => (poly_dr ..).continuousAt

private lemma continuous_poly_t (a : ℕ → ℂ) (N k : ℕ) (u : ℝ) : Continuous (poly a N k u) :=
  continuous_iff_continuousAt.mpr fun _ => (poly_dt ..).continuousAt

/-- The square sum of the coefficients on the vertical line of real part `σ`. -/
def dirichletPolyEnergy (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ‖a n‖^2*(n:ℝ)^(-2*σ)

private lemma energy_nonneg' (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : 0 ≤ dirichletPolyEnergy a N σ :=
  sum_nonneg fun n _ => by positivity

/-- Cost in square mean of inserting up to two logarithmic weights on a vertical line. -/
lemma dirichletPoly_logTwist_energy (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N)
    {σ u : ℝ} (hu : σ ≤ u) {k : ℕ} (hk : k ≤ 2) :
    dirichletPolyEnergy (fun n => a n * (-Complex.log n)^k) N u ≤ (1+Real.log N)^4 * dirichletPolyEnergy a N σ := by
  simp only [dirichletPolyEnergy, mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn₀ : 0 < (n:ℝ) := by linarith
  have hlog := Real.log_le_log hn₀ (by exact_mod_cast (mem_Icc.mp hn).2 : (n:ℝ) ≤ N)
  have hlog0 := Real.log_nonneg hn₁
  have hL₁ := Real.log_nonneg hN₁
  have hw : (n:ℝ)^(-2*u) ≤ (n:ℝ)^(-2*σ) := Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith)
  have hln : ‖Complex.log n‖ = Real.log n := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn₀.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
  simp only [norm_mul,norm_pow,norm_neg,hln,mul_pow,← pow_mul]
  have hklog : (Real.log n)^(k*2) ≤ (1+Real.log N)^4 :=
    (pow_le_pow_left₀ hlog0 (by linarith : Real.log n ≤ 1+Real.log N) _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  calc
    _ ≤ (‖a n‖^2*(1+Real.log N)^4) * (n:ℝ)^(-2*σ) := by gcongr
    _ = _ := by ring

private lemma poly_vertical_integral (a : ℕ → ℂ) {N L : ℕ} (hN : 1 ≤ N)
    {σ u : ℝ} (hu : σ ≤ u) {k : ℕ} (hk : k ≤ 2) :
    ∫ t in (0:ℝ)..L, ‖poly a N k u t‖^2 ≤
      (2*(L:ℝ)+2*Real.pi*N) * (1+Real.log N)^4 * dirichletPolyEnergy a N σ := by
  have hs := dirichletPoly_mean_sq_symm_le (logTwist a k) N u (T:=(L:ℝ)) (Nat.cast_nonneg _)
  have hc := ((continuous_poly_t a N k u).norm.pow 2).intervalIntegrable (μ:=volume) (-(L:ℝ)) L
  have hmono : (∫ t in (0:ℝ)..L, ‖poly a N k u t‖^2) ≤ ∫ t in -(L:ℝ)..L, ‖poly a N k u t‖^2 := by
    apply intervalIntegral.integral_mono_interval (by simp) (Nat.cast_nonneg _) le_rfl
    · exact Filter.Eventually.of_forall fun t => sq_nonneg _
    · exact hc
  apply (hmono.trans hs).trans
  rw [mul_assoc (2*(L:ℝ)+2*Real.pi*N)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact dirichletPoly_logTwist_energy a hN hu hk

private lemma sampling_vertical_integrals {S : Finset ℂ} {L : ℕ} {K : ℝ}
    (hL : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < L)
    (hmult : ∀ j < L, ((S.filter (fun z => ⌊z.im⌋₊ = j)).card : ℝ) ≤ K)
    (a : ℕ → ℂ) (N k : ℕ) (u : ℝ) :
    ∑ z ∈ S, ‖poly a N k u z.im‖^2 ≤ K *
      (2*(∫ t in (0:ℝ)..L, ‖poly a N k u t‖^2) + ∫ t in (0:ℝ)..L, ‖poly a N (k+1) u t‖^2) := by
  let f := fun t => 2*‖poly a N k u t‖^2 + ‖poly a N (k+1) u t‖^2
  have hfc : Continuous f := (continuous_const.mul ((continuous_poly_t ..).norm.pow 2)).add ((continuous_poly_t ..).norm.pow 2)
  have hf0 (t : ℝ) : 0 ≤ f t := by dsimp only [f]; positivity
  have hmap (z : ℂ) (hz : z ∈ S) : ⌊z.im⌋₊ ∈ range L := mem_range.mpr ((Nat.floor_lt (hL z hz).1).mpr (hL z hz).2)
  rw [← sum_fiberwise_of_maps_to hmap]
  have hblock (j : ℕ) (hj : j ∈ range L) :
      ∑ z ∈ S.filter (fun z => ⌊z.im⌋₊=j), ‖poly a N k u z.im‖^2 ≤ K*∫ t in (j:ℝ)..(j+1:ℕ), f t := by
    let W := S.filter (fun z => ⌊z.im⌋₊=j)
    have hzbd (z : ℂ) (hz : z ∈ W) : ‖poly a N k u z.im‖^2 ≤ ∫ t in (j:ℝ)..(j+1:ℕ), f t := by
      have hz' := (hL _ (mem_filter.mp hz).1).1
      have hj' := (mem_filter.mp hz).2
      have hplace : z.im ∈ Set.Icc (j:ℝ) (j+1) := ⟨hj' ▸ Nat.floor_le hz', by
        simpa only [hj'] using (Nat.lt_floor_add_one z.im).le⟩
      have hs := sobolev_square_unit hplace (poly_dt a N k u)
        (continuous_const.mul (continuous_poly_t a N (k+1) u))
      simpa [f, norm_mul] using hs
    apply (sum_le_sum hzbd).trans
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hmult j (mem_range.mp hj))
      (intervalIntegral.integral_nonneg (by exact_mod_cast Nat.le_succ j) (fun t _ => hf0 t))
  apply (sum_le_sum hblock).trans
  rw [← mul_sum, intervalIntegral.sum_integral_adjacent_intervals (a:=fun j : ℕ => (j:ℝ)) (fun _ _ => hfc.intervalIntegrable ..)]
  simp only [Nat.cast_zero]
  change K * (∫ t in (0:ℝ)..L, 2*‖poly a N k u t‖^2 + ‖poly a N (k+1) u t‖^2) ≤ _
  rw [intervalIntegral.integral_add (f:=fun t => 2*‖poly a N k u t‖^2) (g:=fun t => ‖poly a N (k+1) u t‖^2) ((continuous_const.mul ((continuous_poly_t ..).norm.pow 2)).intervalIntegrable ..)
    (((continuous_poly_t ..).norm.pow 2).intervalIntegrable ..), intervalIntegral.integral_const_mul]

/-- A common bound for the vertical square means of the first two logarithmic derivatives
yields a strip sampling bound for a finite family of Dirichlet polynomials. -/
theorem dirichletPoly_family_sampling_strip {ι : Type*} (F : Finset ι) (a : ι → ℕ → ℂ) (S : ι → Finset ℂ)
    {N L : ℕ} {K B σ : ℝ} (hK : 0 ≤ K)
    (hre : ∀ p ∈ F, ∀ z ∈ S p, z.re ∈ Set.Icc σ (σ+1))
    (hL : ∀ p ∈ F, ∀ z ∈ S p, 0 ≤ z.im ∧ z.im < L)
    (hmult : ∀ p ∈ F, ∀ j < L, (((S p).filter (fun z => ⌊z.im⌋₊=j)).card : ℝ) ≤ K)
    (hmean : ∀ u ∈ Set.Icc σ (σ+1), ∀ k ≤ 2,
      ∑ p ∈ F, (∫ t in (0:ℝ)..L, ‖dirichletPoly (fun n => a p n * (-Complex.log n)^k) N ((u:ℂ)+(t:ℂ)*I)‖^2) ≤ B) :
    ∑ p ∈ F, ∑ z ∈ S p, ‖dirichletPoly (a p) N z‖^2 ≤ 9*K*B := by
  let f (p : ι) (z : ℂ) (u : ℝ) := 2*‖poly (a p) N 0 u z.im‖^2 + ‖poly (a p) N 1 u z.im‖^2
  have hfc (p : ι) (z : ℂ) : Continuous (f p z) :=
    (continuous_const.mul ((continuous_poly_r ..).norm.pow 2)).add ((continuous_poly_r ..).norm.pow 2)
  have hfcs (p : ι) : Continuous fun u => ∑ z ∈ S p, f p z u :=
    continuous_finsetSum _ fun z _ => hfc p z
  have hz (p : ι) (hp : p ∈ F) (z : ℂ) (hz : z ∈ S p) :
      ‖dirichletPoly (a p) N z‖^2 ≤ ∫ r in σ..σ+1, f p z r := by
    have h := sobolev_square_unit (hre p hp z hz) (fun t => poly_dr (a p) N 0 t z.im) (continuous_poly_r (a p) N 1 z.im)
    have hzero : logTwist (a p) 0 = a p := funext fun n => by simp [logTwist]
    simpa [f,poly,hzero,Complex.re_add_im] using h
  have hswap (p : ι) : (∑ z ∈ S p, ∫ r in σ..σ+1, f p z r) =
      ∫ r in σ..σ+1, ∑ z ∈ S p, f p z r :=
    (intervalIntegral.integral_finsetSum (fun z _ => (hfc p z).intervalIntegrable ..)).symm
  have hvert (t : ℝ) (ht : t ∈ Set.Icc σ (σ+1)) (k : ℕ) (hk : k ≤ 1) :
      ∑ p ∈ F, ∑ z ∈ S p, ‖poly (a p) N k t z.im‖^2 ≤ 3*K*B := by
    apply (sum_le_sum fun p hp => sampling_vertical_integrals (hL p hp) (hmult p hp) (a p) N k t).trans
    rw [←mul_sum, sum_add_distrib, ←mul_sum]
    have h1 := hmean t ht k (by omega)
    have h2 := hmean t ht (k+1) (by omega)
    calc
      _ ≤ K*(2*B+B) := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤2)) h2) hK
      _ = _ := by ring
  apply (sum_le_sum fun p hp => sum_le_sum (hz p hp)).trans
  simp_rw [hswap]
  rw [← intervalIntegral.integral_finsetSum (fun p _ => (hfcs p).intervalIntegrable ..)]
  calc
    _ ≤ ∫ _r in σ..σ+1, 9*K*B := by
      apply intervalIntegral.integral_mono_on (by linarith) ((continuous_finsetSum _ (fun p _ => hfcs p)).intervalIntegrable ..)
        (continuous_const.intervalIntegrable ..)
      intro t ht
      simp only [f,sum_add_distrib,← mul_sum]
      linarith only [hvert t ht 0 (by decide), hvert t ht 1 (by decide)]
    _ = _ := by simp

/-- A Dirichlet-polynomial square mean on a finite set of points with varying
real parts in a strip of width one and at most `K` ordinates per unit interval. -/
theorem dirichletPoly_sampling_strip {S : Finset ℂ} {L : ℕ} {K σ : ℝ} (hK : 0 ≤ K)
    (hre : ∀ z ∈ S, z.re ∈ Set.Icc σ (σ+1))
    (hL : ∀ z ∈ S, 0 ≤ z.im ∧ z.im < L)
    (hmult : ∀ j < L, ((S.filter (fun z => ⌊z.im⌋₊=j)).card : ℝ) ≤ K)
    (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ z ∈ S, ‖dirichletPoly a N z‖^2 ≤ 9*K *
      ((2*(L:ℝ)+2*Real.pi*N) * (1+Real.log N)^4 * dirichletPolyEnergy a N σ) := by
  simpa only [sum_singleton] using dirichletPoly_family_sampling_strip ({()} : Finset Unit) (fun _ => a) (fun _ => S)
    hK (fun _ _ => hre) (fun _ _ => hL) (fun _ _ => hmult) (fun u hu k hk => by
      rw [sum_singleton]
      have hm := poly_vertical_integral a (L:=L) hN hu.1 hk
      simpa only [poly, show logTwist a k = (fun n => a n * (-Complex.log n)^k) from rfl] using hm)

end AnalyticNumberTheory.PrimeDistribution
