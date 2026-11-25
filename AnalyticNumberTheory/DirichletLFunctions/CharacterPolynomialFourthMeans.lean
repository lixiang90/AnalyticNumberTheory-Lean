import AnalyticNumberTheory.DirichletLFunctions.CharacterPolynomialDiagonals
import AnalyticNumberTheory.DirichletLFunctions.AbsolutePolynomialBounds
import AnalyticNumberTheory.SieveMethods.FixedModulusHybridMean

/-!
# Fourth moments of character polynomials and their tails

Both initial polynomials and infinite tails are averaged over all characters
of one modulus. The bounds are uniform in translations of the height interval.
-/
noncomputable section
open Real Complex Set Finset MeasureTheory Filter
open scoped Interval Topology
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.SieveMethods
namespace AnalyticNumberTheory.DirichletLFunctions

set_option maxHeartbeats 800000 in
/-- Finite character polynomials on the critical and quarter lines. -/
theorem character_polynomial_fourth_means {q N : ℕ} [NeZero q] (hN : 1≤N) {a b : ℝ} (hab : a≤b) :
    let H := (q.totient:ℝ)*(b-a+2*π*(N:ℝ)^2/q)
    ((∑χ : DirichletCharacter ℂ q,∫t in a..b,‖dirichletPoly (fun n : ℕ=>χ n) N ((1/2:ℂ)+t*I)‖^4) ≤ H*(1+Real.log (N^2:ℕ))^4) ∧
    ((∑χ : DirichletCharacter ℂ q,∫t in a..b,‖dirichletPoly (fun n : ℕ=>χ n) N ((1/4:ℂ)+t*I)‖^4) ≤ H*(2*N*(1+Real.log (N^2:ℕ))^3)) := by
  intro H
  let S := Finset.Icc 1 N
  have hH : 0≤H := by dsimp [H];positivity [sub_nonneg.mpr hab]
  have hσ (σ : ℝ) : (∑χ : DirichletCharacter ℂ q,∫t in a..b,‖dirichletPoly (fun n : ℕ=>χ n) N ((σ:ℂ)+t*I)‖^4) ≤
      H*∑k∈Finset.Icc 1 (N^2),‖characterSquareWeight S σ k‖^2 := by
    have he (χ : DirichletCharacter ℂ q) (t : ℝ) := characterPolynomial_norm_four χ S (Finset.Subset.refl _) σ t
    dsimp only [S] at he
    unfold dirichletPoly;simp_rw [he]
    simpa only [H,Nat.cast_pow] using fixed_modulus_hybrid_mean_square (q:=q) (Nat.one_le_pow 2 N hN) (characterSquareWeight S σ) hab
  constructor
  · simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (hσ (1/2)).trans (mul_le_mul_of_nonneg_left (characterSquareWeight_critical S hN) hH)
  · simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (hσ (1/4)).trans (mul_le_mul_of_nonneg_left (characterSquareWeight_quarter S hN) hH)

private theorem finite_tail_fourth {q N M : ℕ} [NeZero q] {a b : ℝ} (hab : a≤b) {C : ℝ}
    (hC : ∑k∈Finset.Icc 1 (M^2),‖characterSquareWeight (Finset.Ioc N M) (3/2) k‖^2≤C/(N:ℝ)^4*(1+Real.log (N^2:ℕ))^3)
    (hD : ∑k∈Finset.Icc 1 (M^2),(k:ℝ)*‖characterSquareWeight (Finset.Ioc N M) (3/2) k‖^2≤C/(N:ℝ)^2*(1+Real.log (N^2:ℕ))^3) :
    (∑χ : DirichletCharacter ℂ q,∫t in a..b,‖∑n∈Finset.Ioc N M,χ n*(n:ℂ)^(-((3/2:ℂ)+t*I))‖^4)≤
       q.totient*C*((b-a+2*weightedHilbertConstant)/(N:ℝ)^4+
          2*weightedHilbertConstant/((q:ℝ)*(N:ℝ)^2))*(1+Real.log (N^2:ℕ))^3 := by
  let S := Finset.Ioc N M
  let w := characterSquareWeight S (3/2)
  have hs : S⊆Finset.Icc 1 M := fun n hn=>by obtain ⟨h1,h2⟩ := mem_Ioc.mp hn;exact mem_Icc.mpr ⟨by omega,h2⟩
  have he (χ : DirichletCharacter ℂ q) (t : ℝ) := characterPolynomial_norm_four χ S hs (3/2) t
  simp only [S,Complex.ofReal_div,Complex.ofReal_ofNat] at he
  simp_rw [he]
  have H := fixed_modulus_hybrid_weighted_mean_square (q:=q) (N:=M^2) w hab
  have hw : (∑k∈Finset.Icc 1 (M^2),(1+(k:ℝ)/q)*‖w k‖^2)=
      (∑k∈Finset.Icc 1 (M^2),‖w k‖^2)+((q:ℝ)⁻¹)*∑k∈Finset.Icc 1 (M^2),(k:ℝ)*‖w k‖^2 := by
    rw [mul_sum,←sum_add_distrib];apply sum_congr rfl;intro k _;ring
  rw [hw] at H
  apply H.trans
  change (∑k∈Finset.Icc 1 (M^2),‖w k‖^2)≤_ at hC
  change (∑k∈Finset.Icc 1 (M^2),(k:ℝ)*‖w k‖^2)≤_ at hD
  apply (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hC (sub_nonneg.mpr hab))
      (mul_le_mul_of_nonneg_left (add_le_add hC (mul_le_mul_of_nonneg_left hD (by positivity : 0≤(q:ℝ)⁻¹)))
        (by positivity [weightedHilbertConstant_pos] : 0≤2*weightedHilbertConstant))) (Nat.cast_nonneg (α:=ℝ) q.totient)).trans_eq
  ring

/-- The full infinite tail on the three-halves line inherits the hybrid
fourth-moment bound. No restriction couples the modulus, height or cutoff. -/
theorem character_tail_fourth_mean :
    ∃ C : ℝ,0<C ∧ ∀ {q N : ℕ} [NeZero q],1≤N → ∀{a b : ℝ},a≤b →
      (∑χ : DirichletCharacter ℂ q,∫t in a..b,‖χ.LFunction ((3/2:ℂ)+t*I)-
        dirichletPoly (fun n : ℕ=>χ n) N ((3/2:ℂ)+t*I)‖^4)≤
        q.totient*C*((b-a+2*weightedHilbertConstant)/(N:ℝ)^4+
        2*weightedHilbertConstant/((q:ℝ)*(N:ℝ)^2))*(1+Real.log (N^2:ℕ))^3 := by
  obtain ⟨C,hC,H⟩ := characterSquareWeight_tail
  refine ⟨C,hC,?_⟩;intro q N _ hN a b hab
  let z (t : ℝ) := (3/2:ℂ)+t*I
  let P (χ : DirichletCharacter ℂ q) (M : ℕ) (t : ℝ) := dirichletPoly (fun n : ℕ=>χ n) M (z t)
  have hz (t : ℝ) : (z t).re=3/2 := by simp [z]
  have hlim (χ : DirichletCharacter ℂ q) (t : ℝ) : Tendsto (fun M=>P χ M t) atTop (𝓝 (χ.LFunction (z t))) := by
    have hr : 1<(z t).re := by rw [hz];norm_num
    have ha := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hr
    have h := ha.dirichletConvergesAt.tendsto
    rw [ha.dirichletSum_eq_LSeries,←DirichletCharacter.LFunction_eq_LSeries χ hr] at h
    exact h.congr (fun M=>(dirichletPoly_eq_dirichletPartialSum _ _ _).symm)
  have hcut (χ : DirichletCharacter ℂ q) {M : ℕ} (hM : 1≤M) (t : ℝ) : ‖χ.LFunction (z t)-P χ M t‖≤2 := by
    have h := norm_LFunction_sub_polynomial_absolute χ hM (s:=z t) (by rw [hz];norm_num)
    rw [hz] at h
    have hh := Real.rpow_le_one_of_one_le_of_nonpos (show (1:ℝ)≤M by exact_mod_cast hM) (by norm_num : 1-(3/2:ℝ)≤0)
    exact h.trans (by norm_num at hh ⊢;linarith only [hh])
  have he (χ : DirichletCharacter ℂ q) {M : ℕ} (hM : N≤M) (t : ℝ) :
      P χ M t-P χ N t=∑n∈Finset.Ioc N M,χ n*(n:ℂ)^(-(z t)) := by
    let f := fun n : ℕ=>χ n*(n:ℂ)^(-(z t))
    have hseg (K : ℕ) : Finset.Ioc 0 K=Finset.Icc 1 K := by ext i;simp;omega
    have h := sum_Ioc_consecutive f (Nat.zero_le N) hM
    simp only [hseg] at h
    change (∑n∈Finset.Icc 1 M,f n)-(∑n∈Finset.Icc 1 N,f n)=_
    linear_combination -h
  let G (χ : DirichletCharacter ℂ q) (M : ℕ) := ∫t in a..b,‖P χ M t-P χ N t‖^4
  have hG (χ : DirichletCharacter ℂ q) : Tendsto (G χ) atTop (𝓝 (∫t in a..b,‖χ.LFunction (z t)-P χ N t‖^4)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>(4:ℝ)^4)
    · refine Eventually.of_forall (fun M=>?_);apply Continuous.aestronglyMeasurable
      have hc (L : ℕ) : Continuous (P χ L) := (differentiable_dirichletPoly _ _).continuous.comp (by dsimp [z];fun_prop)
      exact ((hc M).sub (hc N)).norm.pow 4
    · filter_upwards [eventually_ge_atTop 1] with M hM
      apply ae_of_all;intro t _
      rw [Real.norm_of_nonneg (by positivity : 0≤‖P χ M t-P χ N t‖^4)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have h := norm_sub_le (χ.LFunction (z t)-P χ N t) (χ.LFunction (z t)-P χ M t)
      rw [sub_sub_sub_cancel_left] at h
      linarith only [h,hcut χ hM t,hcut χ hN t]
    · exact continuous_const.intervalIntegrable ..
    · exact ae_of_all _ (fun t _=>((hlim χ t).sub_const _).norm.pow 4)
  apply le_of_tendsto (tendsto_finsetSum univ (fun χ _=>hG χ))
  filter_upwards [eventually_ge_atTop N] with M hM
  change (∑χ,∫t in a..b,‖P χ M t-P χ N t‖^4)≤_
  simp_rw [he _ hM]
  exact finite_tail_fourth hab (H hN M).1 (H hN M).2

end AnalyticNumberTheory.DirichletLFunctions
