import AnalyticNumberTheory.AnalyticTools.Summation.LogarithmicTails
import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola
import AnalyticNumberTheory.RiemannZeta.DivisorPolynomialDiagonals
import AnalyticNumberTheory.DirichletSeries.Operations
import AnalyticNumberTheory.SieveMethods.WeightedMeanValues

/-!
# Dirichlet-polynomial tails of the square of zeta

The positive divisor coefficients have a linear-logarithmic partial sum;
their squares have a cubic-logarithmic one. These estimates give bounds
for the absolute tail and its mean square on the line of real part two.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory Filter
open scoped Interval Topology
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.DivisorProblems
namespace AnalyticNumberTheory.RiemannZeta

theorem sum_divisors_card_le_log {N : ℕ} (hN : 1≤N) :
    ∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)≤2*(N:ℝ)*(1+Real.log N) := by
  have h := congrArg ((↑):ℕ→ℝ) (sum_card_divisors_add_sqrt_sq N)
  push_cast at h
  have hh : (∑d∈Finset.Icc 1 N.sqrt,((N/d:ℕ):ℝ))≤(N:ℝ)*∑d∈Finset.Icc 1 N,(d:ℝ)⁻¹ := by
    rw [mul_sum]
    apply le_trans (sum_le_sum (g:=fun d : ℕ=>(N:ℝ)*(d:ℝ)⁻¹) _)
    · exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.sqrt_le_self _)) (fun _ _ _ => by positivity)
    · intro d hd
      rw [←div_eq_mul_inv,le_div_iff₀ (Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1)]
      exact_mod_cast Nat.div_mul_le_self N d
  have hH := sum_inv_le_one_add_log (show (1:ℝ)≤N by exact_mod_cast hN)
  rw [Nat.floor_natCast] at hH
  linarith only [h,hh,mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (α:=ℝ) N),sq_nonneg (N.sqrt:ℝ)]

private theorem divisor_tail_point_bound : ∃ C : ℝ,0<C ∧ ∀{N : ℕ},1≤N → ∀ M : ℕ,
    (∑n∈Finset.Ioc N M,(n.divisors.card:ℝ)/(n:ℝ)^2)≤C/(N:ℝ)*(1+Real.log N) := by
  obtain ⟨C,hC,H⟩ := logarithmic_power_tail 1 2 (by decide) (f:=fun n => (n.divisors.card:ℝ)) (fun _=>by positivity)
    (B:=2) (by norm_num) (fun hx => by simpa using sum_divisors_card_le_log hx)
  refine ⟨C,hC,?_⟩;intro N hN M
  apply (H hN M).trans_eq
  have hp : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  field_simp

private theorem divisor_tail_square_bound : ∃ C : ℝ,0<C ∧ ∀{N : ℕ},1≤N → ∀ M : ℕ,
    (∑n∈Finset.Ioc N M,(n.divisors.card:ℝ)^2/(n:ℝ)^3)≤C/(N:ℝ)^2*(1+Real.log N)^3 := by
  obtain ⟨C,hC,H⟩ := logarithmic_power_tail 3 3 (by decide) (f:=fun n => (n.divisors.card:ℝ)^2) (fun _=>by positivity)
    (B:=1) (by norm_num) (fun {X} hx => by simpa only [one_mul,max_eq_left hx] using sum_Icc_card_divisors_sq_le X)
  refine ⟨C,hC,?_⟩;intro N hN M
  apply (H hN M).trans_eq
  have hp : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  field_simp

private theorem tail_poly {N M : ℕ} (hNM : N≤M) (s : ℂ) :
    divisorPolynomial M s-divisorPolynomial N s=
      dirichletPoly (fun n : ℕ=>if N<n then (n.divisors.card:ℂ) else 0) M s := by
  let f := fun n : ℕ => (n.divisors.card:ℂ)*(n:ℂ)^(-s)
  have hfilter : (Finset.Icc 1 M).filter (fun n=>n≤N)=Finset.Icc 1 N := by ext n;simp;omega
  have h := sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun n=>n≤N) f
  rw [hfilter] at h
  simp only [divisorPolynomial,dirichletPoly,ite_mul,zero_mul,←sum_filter,not_le] at h ⊢
  change _-_=∑n∈(Finset.Icc 1 M).filter (fun n=>N<n),f n
  linear_combination -h

private theorem tail_sum {R : Type*} [AddCommMonoid R] (f : ℕ→R) (N M : ℕ) :
    (∑n∈Finset.Icc 1 M,if N<n then f n else 0)=∑n∈Finset.Ioc N M,f n := by
  rw [←sum_filter]
  have he : (Finset.Icc 1 M).filter (fun n=>N<n)=Finset.Ioc N M := by ext n;simp;omega
  rw [he]

/-- The finite divisor polynomial on the line of real part two converges to
the square of zeta. -/
theorem tendsto_divisorPolynomial_zeta_sq {s : ℂ} (hs : 1<s.re) :
    Tendsto (fun M=>divisorPolynomial M s) atTop (𝓝 (riemannZeta s^2)) := by
  let a := fun n : ℕ => (n.divisors.card:ℂ)
  have ha : LSeriesSummable a s :=
    (LSeriesSummable_congr s (f:=fun n => (((ArithmeticFunction.sigma 0 n):ℕ):ℂ)) (g:=a)
      (fun {n} _ => by simp [a,ArithmeticFunction.sigma_zero_apply])).mp (LSeriesSummable_sigma_zero_iff.mpr hs)
  have h := ha.dirichletConvergesAt.tendsto
  rw [ha.dirichletSum_eq_LSeries,LSeries_card_divisors_eq hs] at h
  exact h.congr fun M => (dirichletPoly_eq_dirichletPartialSum a M s).symm

private theorem finite_tail_pointwise {C : ℝ}
    (H : ∀ {N : ℕ},1≤N → ∀ M : ℕ,(∑n∈Finset.Ioc N M,(n.divisors.card:ℝ)/(n:ℝ)^2)≤C/N*(1+Real.log N))
    {N M : ℕ} (hN : 1≤N) (hNM : N≤M) (t : ℝ) :
    let s := (2:ℂ)+t*I
    ‖divisorPolynomial M s-divisorPolynomial N s‖≤C/N*(1+Real.log N) := by
  intro s;rw [tail_poly hNM]
  apply (norm_sum_le ..).trans
  apply le_trans _ (H hN M)
  rw [←tail_sum];apply sum_le_sum;intro n hn
  have hnp := (Finset.mem_Icc.mp hn).1
  dsimp only
  split_ifs with hh
  · rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast_cpow_of_pos hnp,neg_re,
      show s.re=2 by simp [s],Real.rpow_neg (Nat.cast_nonneg _)]
    norm_num [div_eq_mul_inv]
  · simp

/-- Pointwise reciprocal-square tail bound with an absolute constant,
independent of the ordinate and of the cutoff. -/
theorem zeta_square_tail_pointwise : ∃ C : ℝ,0<C ∧ ∀{N : ℕ},1≤N → ∀t : ℝ,
    ‖riemannZeta ((2:ℂ)+t*I)^2-divisorPolynomial N ((2:ℂ)+t*I)‖≤C/N*(1+Real.log N) := by
  obtain ⟨C,hC,H⟩ := divisor_tail_point_bound
  refine ⟨C,hC,?_⟩;intro N hN t
  have ht := ((tendsto_divisorPolynomial_zeta_sq (s:=(2:ℂ)+t*I) (by simp)).sub_const (divisorPolynomial N ((2:ℂ)+t*I))).norm
  exact le_of_tendsto ht ((eventually_ge_atTop N).mono (fun M hM => finite_tail_pointwise H hN hM t))

private theorem finite_tail_mean {C : ℝ} (hC : 0<C)
    (H : ∀ {N : ℕ},1≤N → ∀ M : ℕ,(∑n∈Finset.Ioc N M,(n.divisors.card:ℝ)^2/(n:ℝ)^3)≤C/(N:ℝ)^2*(1+Real.log N)^3)
    {N M : ℕ} (hN : 1≤N) (hNM : N≤M) {T : ℝ} (hT : 0≤T) :
    (∫t in T..(2*T),‖divisorPolynomial M ((2:ℂ)+t*I)-divisorPolynomial N ((2:ℂ)+t*I)‖^2) ≤
      (T/(N:ℝ)+4*weightedHilbertConstant)*(C/(N:ℝ)^2*(1+Real.log N)^3) := by
  let a := fun n : ℕ => if N<n then (n.divisors.card:ℂ) else 0
  let L := ∑n∈Finset.Ioc N M,(n.divisors.card:ℝ)^2/(n:ℝ)^3
  have hNp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hE := weighted_dirichletPoly_mean_square a M 2 T (2*T)
  have hpoly (t : ℝ) : divisorPolynomial M ((2:ℂ)+t*I)-divisorPolynomial N ((2:ℂ)+t*I)=dirichletPoly a M ((2:ℂ)+t*I) := tail_poly hNM _
  simp_rw [hpoly]
  have hfac (n : ℕ) : (n:ℝ)^(-2*(2:ℝ))=((n:ℝ)^4)⁻¹ := by norm_num [Real.rpow_neg (Nat.cast_nonneg _)]
  simp_rw [hfac] at hE
  have hdiag : (∑n∈Finset.Icc 1 M,‖a n‖^2*((n:ℝ)^4)⁻¹)≤(N:ℝ)⁻¹*L := by
    dsimp only [L];rw [mul_sum,←tail_sum]
    apply sum_le_sum;intro n hn
    have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    by_cases hh : N<n
    · simp only [a,if_pos hh,Complex.norm_natCast]
      have hpn : (N:ℝ)≤n := by exact_mod_cast hh.le
      have he : (n.divisors.card:ℝ)^2*((n:ℝ)^4)⁻¹=(n:ℝ)⁻¹*((n.divisors.card:ℝ)^2/(n:ℝ)^3) := by field_simp
      rw [he];exact mul_le_mul_of_nonneg_right (inv_anti₀ hNp hpn) (by positivity)
    · simp [a,hh]
  have hweight : (∑n∈Finset.Icc 1 M,(n:ℝ)*‖a n‖^2*((n:ℝ)^4)⁻¹)=L := by
    dsimp only [L];rw [←tail_sum];apply sum_congr rfl;intro n hn
    have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    by_cases hh : N<n
    · simp only [a,if_pos hh,Complex.norm_natCast];field_simp
    · simp [a,hh]
  have hh := (abs_le.mp hE).2
  rw [hweight,show 2*T-T=T by ring] at hh
  norm_num only [Complex.ofReal_ofNat] at hh
  have hL := H hN M
  change L≤_ at hL
  apply le_trans (b:=(T/(N:ℝ)+4*weightedHilbertConstant)*L)
  · rw [div_eq_mul_inv]
    nlinarith only [hh,mul_le_mul_of_nonneg_left hdiag hT]
  · exact mul_le_mul_of_nonneg_left hL (by positivity [weightedHilbertConstant_pos])

/-- Mean square of the infinite tail on a dyadic height interval, with separate
height and cutoff parameters. -/
theorem zeta_square_tail_mean : ∃ C : ℝ,0<C ∧ ∀{N : ℕ},1≤N → ∀{T : ℝ},0≤T →
    (∫t in T..(2*T),‖riemannZeta ((2:ℂ)+t*I)^2-divisorPolynomial N ((2:ℂ)+t*I)‖^2)≤
    (T/(N:ℝ)+4*weightedHilbertConstant)*(C/(N:ℝ)^2*(1+Real.log N)^3) := by
  obtain ⟨C,hC,H⟩ := divisor_tail_square_bound
  obtain ⟨D,hD,K⟩ := divisor_tail_point_bound
  refine ⟨C,hC,?_⟩;intro N hN T hT
  let f := fun (M : ℕ) (t : ℝ) => ‖divisorPolynomial M ((2:ℂ)+t*I)-divisorPolynomial N ((2:ℂ)+t*I)‖^2
  let g := fun t : ℝ => ‖riemannZeta ((2:ℂ)+t*I)^2-divisorPolynomial N ((2:ℂ)+t*I)‖^2
  let B := D/N*(1+Real.log N)
  have hb : 0≤B := by dsimp [B];positivity [Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)]
  have hi : Tendsto (fun M => ∫ t in T..(2*T),f M t) atTop (𝓝 (∫ t in T..(2*T),g t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B^2)
    · exact Eventually.of_forall (fun M => ((divisorPolynomial_continuous M 2).sub (divisorPolynomial_continuous N 2)).norm.pow 2 |>.aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop N] with M hM
      exact ae_of_all _ (fun t _=>by rw [Real.norm_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (norm_nonneg _) (finite_tail_pointwise K hN hM t) 2)
    · exact continuous_const.intervalIntegrable ..
    · exact ae_of_all _ (fun t _=>(((tendsto_divisorPolynomial_zeta_sq (s:=(2:ℂ)+t*I) (by simp)).sub_const _).norm.pow 2))
  exact le_of_tendsto hi ((eventually_ge_atTop N).mono (fun M hM => finite_tail_mean hC H hN hM hT))

end AnalyticNumberTheory.RiemannZeta
