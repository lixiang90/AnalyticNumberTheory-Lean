import AnalyticNumberTheory.DirichletSeries.OrdinaryAbel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor

/-! # Boundary convergence and Abel limits of ordinary Dirichlet series -/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries

/-- Abel's boundary theorem for an ordinary Dirichlet series. At a point of
ordinary convergence the sum has the same limit from inside each fixed
sector meeting the boundary nontangentially. -/
theorem DirichletConvergesAt.tendsto_dirichletSum_of_sector {a : ℕ → ℂ} {s : ℂ}
    (hs : DirichletConvergesAt a s) {ι : Type*} {l : Filter ι} {z : ι → ℂ} {K : ℝ}
    (hK : 0 < K) (hz : Tendsto z l (𝓝 s))
    (hsector : ∀ᶠ i in l, s.re < (z i).re ∧ ‖z i-s‖ ≤ K*((z i).re-s.re)) :
    Tendsto (fun i => dirichletSum a (z i)) l (𝓝 (dirichletSum a s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (4*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ * (4*(K+1)) = ε := div_mul_cancel₀ ε (by positivity)
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hs.tendsto) δ hδ)
  have htail (n : ℕ) (hn : M ≤ n) :
      ‖dirichletPartialSum a s n - dirichletPartialSum a s M‖ ≤ 2*δ := by
    rw [← dist_eq_norm]
    calc
      _ ≤ dist (dirichletPartialSum a s n) (dirichletSum a s) +
          dist (dirichletSum a s) (dirichletPartialSum a s M) := dist_triangle _ _ _
      _ ≤ _ := by rw [dist_comm (dirichletSum a s)]; linarith [hM n hn,hM M le_rfl]
  have hp := (dirichletPartialSum_differentiable a M).continuous.continuousAt.tendsto.comp hz
  filter_upwards [hsector,(Metric.tendsto_nhds.mp hp) δ hδ] with i hi hpoly
  have hc := dirichletConvergesAt_of_re_lt_re hs hi.1
  have hu : ‖dirichletSum a (z i) - dirichletPartialSum a (z i) M‖ ≤ (2*δ)*K := by
    apply le_of_tendsto ((hc.tendsto.sub_const _).norm)
    filter_upwards [eventually_ge_atTop M] with n hn
    exact (norm_dirichletPartialSum_sub_le_of_re_lt a hi.1 hn
      (fun k hk => htail k (Finset.mem_Icc.mp hk).1)).trans
      (mul_le_mul_of_nonneg_left ((div_le_iff₀ (sub_pos.mpr hi.1)).mpr hi.2) (by positivity))
  change dist (dirichletPartialSum a (z i) M) (dirichletPartialSum a s M) < δ at hpoly
  rw [← dist_eq_norm] at hu
  calc
    _ ≤ dist (dirichletSum a (z i)) (dirichletPartialSum a (z i) M) +
        dist (dirichletPartialSum a (z i) M) (dirichletSum a s) := dist_triangle _ _ _
    _ ≤ (2*δ)*K + (dist (dirichletPartialSum a (z i) M) (dirichletPartialSum a s M) +
        dist (dirichletPartialSum a s M) (dirichletSum a s)) := add_le_add hu (dist_triangle _ _ _)
    _ < ε := by nlinarith [hM M le_rfl]

/-- The horizontal Abel limit at every ordinary convergence point. -/
theorem DirichletConvergesAt.tendsto_dirichletSum_add_real {a : ℕ → ℂ} {s : ℂ}
    (hs : DirichletConvergesAt a s) :
    Tendsto (fun u : ℝ => dirichletSum a (s+(u:ℂ))) (𝓝[>] 0) (𝓝 (dirichletSum a s)) := by
  apply hs.tendsto_dirichletSum_of_sector (K := 1) one_pos
  · have h : Continuous (fun u : ℝ => s+(u:ℂ)) := continuous_const.add Complex.continuous_ofReal
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 0 < u := hu
    simp [hu', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu']

/-- A saving of two logarithms in the summatory function gives ordinary
convergence on the entire line of real part one, by partial summation. -/
theorem dirichletConvergesAt_of_coeffPartialSum_log_sq {a : ℕ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ᶠ x : ℝ in atTop, ‖coeffPartialSum a ⌊x⌋₊‖ ≤ C*x/(Real.log x)^2)
    {s : ℂ} (hs : s.re = 1) : DirichletConvergesAt a s := by
  obtain ⟨A₀,hA₀⟩ := eventually_atTop.mp h
  let A := max 2 A₀
  have hA : 1 < A := (by norm_num : (1:ℝ) < 2).trans_le (le_max_left ..)
  have hApos : 0 < A := zero_lt_one.trans hA
  have hcoeff (t : ℝ) (ht : A ≤ t) := hA₀ t ((le_max_right ..).trans ht)
  let g (t : ℝ) := coeffPartialSum a ⌊t⌋₊ * (t:ℂ)^(-s-1)
  have hg (t : ℝ) (ht : A ≤ t) : ‖g t‖ ≤ C*(t⁻¹/(Real.log t)^2) := by
    have ht0 := hApos.trans_le ht
    rw [show ‖g t‖ = ‖coeffPartialSum a ⌊t⌋₊‖ * t^(-2:ℝ) by
      dsimp only [g]
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num [hs]]
    calc
      _ ≤ (C*t/(Real.log t)^2) * t^(-2:ℝ) := by gcongr; exact hcoeff t ht
      _ = _ := by rw [Real.rpow_neg ht0.le,Real.rpow_two]; field_simp [ht0.ne']
  have hmeas : Measurable g := ((measurable_from_top (f := coeffPartialSum a)).comp Nat.measurable_floor).mul
    (Complex.continuous_ofReal.measurable.pow_const (-s-1))
  have hi : IntegrableOn g (Ioi A) := by
    apply ((integrableOn_inv_div_log_sq_Ioi hA).const_mul C).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact hg t ht.le
  have hpow : Tendsto (fun N : ℕ => ((Real.log (N:ℝ))^2)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun N : ℕ => coeffPartialSum a N * (N:ℂ)^(-s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_nhds.div_atTop hpow (a := C))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop A] with N hN
    have hn := hApos.trans_le hN
    have hcoef := hcoeff N hN
    rw [Nat.floor_natCast] at hcoef
    rw [norm_mul,show (N:ℂ) = ((N:ℝ):ℂ) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.neg_re,hs,Real.rpow_neg_one]
    calc
      _ ≤ (C*N/(Real.log N)^2) * (N:ℝ)⁻¹ := by gcongr
      _ = _ := by field_simp [hn.ne']
  have hInt := intervalIntegral_tendsto_integral_Ioi A hi tendsto_natCast_atTop_atTop
  let k := dirichletPartialSum a s ⌊A⌋₊ - coeffPartialSum a ⌊A⌋₊ * (A:ℂ)^(-s)
  refine ⟨k + s * ∫ t in Ioi A, g t, ?_⟩
  have H := (tendsto_const_nhds (x := k)).add (hb.add (hInt.const_mul s))
  rw [zero_add] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hp := dirichletPartialSum_sub_eq_coeffPartialSum_integral a s hApos hNpos
  rw [Nat.floor_natCast] at hp
  dsimp only [k,g,Pi.add_apply,Function.comp_apply]
  push_cast at hp ⊢
  linear_combination -hp

end AnalyticNumberTheory.DirichletSeries
