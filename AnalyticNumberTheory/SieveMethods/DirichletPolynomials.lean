import AnalyticNumberTheory.AnalyticTools.Transforms
import AnalyticNumberTheory.DirichletSeries.VerticalOrder
import AnalyticNumberTheory.SieveMethods.LargeSieve

/-!
# Mean values of Dirichlet polynomials and the hybrid large sieve

The mean-value theorem uses Hilbert's inequality at logarithmic frequencies. Combining
the character large sieve with Gallagher's integral inequality gives the hybrid bound.

## Main Results

- `dirichletPoly_mean_sq_Icc_asymp`, `dirichletPoly_mean_sq_Icc_le`,
  `dirichletPoly_mean_sq_symm_asymp`, `dirichletPoly_mean_sq_symm_le`,
  `dirichletPoly_mean_sq_Ioc_le`: Montgomery–Vaughan mean value theorems for Dirichlet
  polynomials via Hilbert's inequality on `{log n / (2π)}`.
- `character_large_sieve_dirichlet`, `character_large_sieve_dirichlet_Icc`:
  multiplicative character large sieve inequality via primitive Gauss sums, character
  orthogonality, and Farey spacing.
- `tentKernel`, `fourier_tentKernel`, `tent_gallagher_integral_bound`: compactly supported
  tent kernel and Gallagher's integral inequality via Fourier inversion.
- `hybrid_large_sieve_Ioc`, `hybrid_large_sieve`, `hybrid_large_sieve_unweighted`:
  hybrid large sieve combining character sums and vertical `t`-integration.
-/

open Complex Real Finset MeasureTheory Filter
open scoped Topology Matrix Classical InnerProductSpace FourierTransform
open AnalyticNumberTheory.AnalyticTools
open AnalyticNumberTheory.DirichletLFunctions
open AnalyticNumberTheory.DirichletSeries

namespace AnalyticNumberTheory.SieveMethods

noncomputable section

section InternalAnalyticCore

private theorem complex_mul_star_dp (z : ℂ) :
    z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- Hilbert's inequality for an arbitrary finite set of separated real frequencies. -/
theorem hilbert_inequality_separated {κ : Type*} (J : Finset κ) (x : κ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hx : ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ |x r - x s|) (u : κ → ℂ) :
    ‖∑ r ∈ J, ∑ s ∈ J,
        (if r = s then (0 : ℂ) else u r * star (u s) / ((x r - x s : ℝ) : ℂ))‖ ≤
      Real.pi * δ⁻¹ * ∑ r ∈ J, ‖u r‖ ^ 2 := by
  by_cases hJ : J.card = 0
  · rw [Finset.card_eq_zero.mp hJ]; simp
  let R := J.card
  have hinj : Set.InjOn x (J : Set κ) := by
    intro r hr s hs heq
    by_contra hne
    have h := hx r hr s hs hne
    rw [heq, sub_self, abs_zero] at h
    linarith
  let Sx : Finset ℝ := J.image x
  have hSx_card : Sx.card = R := Finset.card_image_of_injOn hinj
  let y : Fin R → ℝ := fun i => Sx.orderEmbOfFin hSx_card i
  have hy_mem : ∀ i : Fin R, y i ∈ Sx := fun i => Sx.orderEmbOfFin_mem hSx_card i
  have hy_strict : StrictMono y := fun _ _ hij => (Sx.orderEmbOfFin hSx_card).strictMono hij
  have hchoose : ∀ i : Fin R, ∃ r ∈ J, x r = y i := fun i => Finset.mem_image.mp (hy_mem i)
  let σ : Fin R → κ := fun i => (hchoose i).choose
  have hσ_mem : ∀ i : Fin R, σ i ∈ J := fun i => (hchoose i).choose_spec.1
  have hσ_eq : ∀ i : Fin R, x (σ i) = y i := fun i => (hchoose i).choose_spec.2
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    apply (Sx.orderEmbOfFin hSx_card).injective
    change y i = y j
    rw [← hσ_eq i, ← hσ_eq j, hij]
  have hσ_bij : ∀ r ∈ J, ∃ i : Fin R, σ i = r := by
    have himg : (Finset.univ.image σ) = J := by
      apply Finset.eq_of_subset_of_card_le
      · intro r hr
        rcases Finset.mem_image.mp hr with ⟨i, _, rfl⟩
        exact hσ_mem i
      · rw [Finset.card_image_of_injective _ hσ_inj, Finset.card_univ, Fintype.card_fin]
    intro r hr
    rw [← himg, Finset.mem_image] at hr
    rcases hr with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  have hy_spaced : ∀ i j : Fin R, i < j → δ ≤ y j - y i := by
    intro i j hij
    have hne : σ j ≠ σ i := fun h => hij.ne' (hσ_inj h)
    have h1 := hx (σ j) (hσ_mem j) (σ i) (hσ_mem i) hne
    rw [hσ_eq j, hσ_eq i, abs_of_pos (sub_pos.mpr (hy_strict hij))] at h1
    exact h1
  have hrew_sum :
      ∑ r ∈ J, ∑ s ∈ J, (if r = s then (0 : ℂ) else u r * star (u s) / ((x r - x s : ℝ) : ℂ)) =
        ∑ i : Fin R, ∑ j : Fin R,
          (if i = j then (0 : ℂ) else u (σ i) * star (u (σ j)) / ((y i - y j : ℝ) : ℂ)) := by
    symm
    refine Finset.sum_bij (fun i _ => σ i) (fun i _ => hσ_mem i)
      (fun i₁ _ i₂ _ h => hσ_inj h) (fun r hr => ?_) (fun i _ => ?_)
    · obtain ⟨i, hi⟩ := hσ_bij r hr
      exact ⟨i, Finset.mem_univ i, hi⟩
    · refine Finset.sum_bij (fun j _ => σ j) (fun j _ => hσ_mem j)
        (fun j₁ _ j₂ _ h => hσ_inj h) (fun s hs => ?_) (fun j _ => ?_)
      · obtain ⟨j, hj⟩ := hσ_bij s hs
        exact ⟨j, Finset.mem_univ j, hj⟩
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : σ i ≠ σ j := fun h => hij (hσ_inj h)
          simp only [hij, hne, ↓reduceIte, hσ_eq i, hσ_eq j]
  have hrew_norm : ∑ r ∈ J, ‖u r‖ ^ 2 = ∑ i : Fin R, ‖u (σ i)‖ ^ 2 := by
    symm
    refine Finset.sum_bij (fun i _ => σ i) (fun i _ => hσ_mem i)
      (fun i₁ _ i₂ _ h => hσ_inj h) (fun r hr => ?_) (fun _ _ => rfl)
    obtain ⟨i, hi⟩ := hσ_bij r hr
    exact ⟨i, Finset.mem_univ i, hi⟩
  rw [hrew_sum, hrew_norm]
  exact hilbert_inequality_real hδ hy_spaced (fun i => u (σ i))

end InternalAnalyticCore

section MeanValueTheorem

private theorem continuous_finset_sum_dp {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Continuous (f i)) :
    Continuous fun t : ℝ => ∑ i ∈ S, f i t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp; exact continuous_const
  | insert a s ha ih =>
    have hfun : (fun t : ℝ => ∑ i ∈ insert a s, f i t) = fun t : ℝ => f a t + ∑ i ∈ s, f i t := by
      funext t; exact Finset.sum_insert ha
    rw [hfun]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem intervalIntegral_finset_sum_dp {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (a b : ℝ) (hf : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    ∫ t in a..b, ∑ i ∈ S, f i t = ∑ i ∈ S, ∫ t in a..b, f i t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hint_s : IntervalIntegrable (fun t : ℝ => ∑ i ∈ s, f i t) volume a b := by
      have hsum : (fun t : ℝ => ∑ i ∈ s, f i t) = ∑ i ∈ s, f i := by
        funext t; simp
      rw [hsum]
      exact IntervalIntegrable.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [intervalIntegral.integral_congr (fun t _ => by rw [Finset.sum_insert hx]),
      intervalIntegral.integral_add (hf x (Finset.mem_insert_self x s)) hint_s,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      Finset.sum_insert hx]

private theorem natCast_cpow_neg_vertical_dp {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
  have hexp : ((Real.log n : ℝ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ((Real.log n * (-σ) : ℝ) : ℂ) + (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hn_pos]

private theorem natCast_cpow_neg_it_dp {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
  congr 1
  push_cast
  ring

private theorem star_natCast_cpow_mul_self_dp {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    star ((m : ℂ) ^ (-(t : ℂ) * Complex.I)) * (m : ℂ) ^ (-(t : ℂ) * Complex.I) = 1 := by
  rw [natCast_cpow_neg_it_dp hm t, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have hexp0 : (starRingEnd ℂ) (-((t * Real.log m : ℝ) : ℂ) * Complex.I) +
      -((t * Real.log m : ℝ) : ℂ) * Complex.I = 0 := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hexp0, Complex.exp_zero]

private theorem integral_cexp_log_div_sub (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hne : m ≠ n) (t₀ t₁ : ℝ) :
    ∫ t in t₀..t₁, (m : ℂ) ^ (-(t : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      (((m : ℂ) ^ (-(t₁ : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) -
          (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(t₀ : ℂ) * Complex.I))) /
        (-Complex.I * ((Real.log m - Real.log n : ℝ) : ℂ))) := by
  let α : ℝ := Real.log n - Real.log m
  have hα_ne : α ≠ 0 := by
    intro h0
    have hlog : Real.log (n : ℝ) = Real.log (m : ℝ) := sub_eq_zero.mp h0
    have hmn : (n : ℝ) = (m : ℝ) :=
      Real.log_injOn_pos (by positivity : (0 : ℝ) < n) (by positivity : (0 : ℝ) < m) hlog
    exact hne (by exact_mod_cast hmn.symm)
  have hfun : ∀ t : ℝ,
      (m : ℂ) ^ (-(t : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * (α : ℂ) * (t : ℂ)) := by
    intro t
    rw [natCast_cpow_neg_it_dp hm t, natCast_cpow_neg_it_dp hn t]
    have hstar : star (Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * ((Real.log n : ℝ) : ℂ) * (t : ℂ)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul]
      ring
    rw [hstar, ← Complex.exp_add]
    congr 1
    dsimp [α]
    push_cast
    ring
  have hIα_ne : Complex.I * (α : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hα_ne)
  have hderiv : ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * (α : ℂ) * (u : ℂ)) / (Complex.I * (α : ℂ)))
        (Complex.exp (Complex.I * (α : ℂ) * (t : ℂ))) t := by
    intro t _
    have hc : HasDerivAt (fun u : ℝ => Complex.I * (α : ℂ) * (u : ℂ)) (Complex.I * (α : ℂ)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (α : ℂ))
    have he := hc.cexp.div_const (Complex.I * (α : ℂ))
    convert he using 1
    rw [mul_div_cancel_right₀ _ hIα_ne]
  have hcont : IntervalIntegrable (fun u : ℝ => Complex.exp (Complex.I * (α : ℂ) * (u : ℂ)))
      volume t₀ t₁ := by
    refine Continuous.intervalIntegrable ?_ t₀ t₁
    exact (continuous_const.mul Complex.continuous_ofReal).cexp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  have hint_congr :
      ∫ t in t₀..t₁, (m : ℂ) ^ (-(t : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        ∫ t in t₀..t₁, Complex.exp (Complex.I * (α : ℂ) * (t : ℂ)) :=
    intervalIntegral.integral_congr fun t _ => hfun t
  rw [hint_congr, hint, ← hfun t₁, ← hfun t₀, sub_div]
  have hden : Complex.I * (α : ℂ) = -Complex.I * ((Real.log m - Real.log n : ℝ) : ℂ) := by
    dsimp [α]; push_cast; ring
  rw [hden]

private theorem norm_integral_dirichlet_sub_diag_le (a : ℕ → ℂ) (N : ℕ) (σ t₀ t₁ : ℝ)
    (_ht : t₀ ≤ t₁) :
    ‖(∫ t in t₀..t₁, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) -
        (t₁ - t₀) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)‖ ≤
      2 * Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  by_cases hN0 : N = 0
  · subst hN0
    have hzero : ∀ t : ℝ, dirichletPoly a 0 ((σ : ℂ) + (t : ℂ) * Complex.I) = 0 := fun t => by
      simp [dirichletPoly]
    simp [hzero]
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
  let S : Finset ℕ := Finset.Icc 1 N
  let c : ℕ → ℂ := fun n => a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
  have hc_norm : ∀ n ∈ S, ‖c n‖ ^ 2 = ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    dsimp [c]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hn_pos.le _),
      mul_pow, ← Real.rpow_two ((n : ℝ) ^ (-σ)), ← Real.rpow_mul hn_pos.le]
    congr 2
    ring
  have hpoly_eq : ∀ t : ℝ,
      dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I) =
        ∑ n ∈ S, c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    intro t
    dsimp [dirichletPoly, S]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [natCast_cpow_neg_vertical_dp hn1 σ t, ← natCast_cpow_neg_it_dp hn1 t]
    dsimp [c]
    ring
  have hnorm_sq_eq : ∀ t : ℝ,
      ((‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    intro t
    rw [hpoly_eq t, ← complex_mul_star_dp, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => Finset.mul_sum _ _ _
  have hcont_fn : ∀ m n : ℕ, m ∈ S → n ∈ S →
      IntervalIntegrable (fun t : ℝ =>
        (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))) volume t₀ t₁ := by
    intro m n hm hn
    refine Continuous.intervalIntegrable ?_ t₀ t₁
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hc1 : Continuous fun t : ℝ => c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I) := by
      have hrew : (fun t : ℝ => c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) =
          fun t : ℝ => c m * Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I) := by
        funext t; rw [natCast_cpow_neg_it_dp hm1 t]
      rw [hrew]
      exact continuous_const.mul (Complex.continuous_exp.comp
        (((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).neg).mul continuous_const))
    have hc2 : Continuous fun t : ℝ => star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
      have hrew : (fun t : ℝ => star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
          fun t : ℝ => star (c n * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)) := by
        funext t; rw [natCast_cpow_neg_it_dp hn1 t]
      rw [hrew]
      exact continuous_star.comp (continuous_const.mul (Complex.continuous_exp.comp
        (((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).neg).mul continuous_const)))
    exact hc1.mul hc2
  have hintC :
      ((∫ t in t₀..t₁, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          ∫ t in t₀..t₁, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_congr fun t _ => hnorm_sq_eq t]
    rw [intervalIntegral_finset_sum_dp S
      (fun m t => ∑ n ∈ S, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
        star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))) t₀ t₁ fun m hm => by
      have hsum : (fun t : ℝ => ∑ n ∈ S, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
          ∑ n ∈ S, fun t : ℝ => (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
        funext t; simp
      rw [hsum]
      exact IntervalIntegrable.sum S fun n hn => hcont_fn m n hm hn]
    refine Finset.sum_congr rfl fun m hm => ?_
    exact intervalIntegral_finset_sum_dp S
      (fun n t => (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
        star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))) t₀ t₁ fun n hn => hcont_fn m n hm hn
  have hdiag_term : ∀ m ∈ S,
      ∫ t in t₀..t₁, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          star (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        ((t₁ - t₀) : ℂ) * ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hconst : ∀ t : ℝ,
        (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            star (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) =
          ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
      intro t
      rw [star_mul]
      calc
        c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I) *
            (star ((m : ℂ) ^ (-(t : ℂ) * Complex.I)) * star (c m))
            = (c m * star (c m)) *
                (star ((m : ℂ) ^ (-(t : ℂ) * Complex.I)) * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
              ring
        _ = ((‖c m‖ ^ 2 : ℝ) : ℂ) * 1 := by
              rw [complex_mul_star_dp, star_natCast_cpow_mul_self_dp hm1 t]
        _ = ((‖c m‖ ^ 2 : ℝ) : ℂ) := mul_one _
    rw [intervalIntegral.integral_congr fun t _ => hconst t, intervalIntegral.integral_const,
      Complex.real_smul, Complex.ofReal_sub]
  have hoff_term : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      ∫ t in t₀..t₁, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
          star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I) *
            star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) -
          c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) *
            star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I))) /
          (-Complex.I * ((Real.log m - Real.log n : ℝ) : ℂ)) := by
    intro m hm n hn hne
    have hfun : ∀ t : ℝ,
        (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
          (c m * star (c n)) *
            ((m : ℂ) ^ (-(t : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
      intro t; rw [star_mul]; ring
    rw [intervalIntegral.integral_congr fun t _ => hfun t, intervalIntegral.integral_const_mul,
      integral_cexp_log_div_sub m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 hne t₀ t₁]
    have h1 : ∀ u : ℝ,
        (c m * star (c n)) *
            ((m : ℂ) ^ (-(u : ℂ) * Complex.I) * star ((n : ℂ) ^ (-(u : ℂ) * Complex.I))) =
          c m * (m : ℂ) ^ (-(u : ℂ) * Complex.I) *
            star (c n * (n : ℂ) ^ (-(u : ℂ) * Complex.I)) := by
      intro u; simp only [star_mul]; ring
    rw [mul_div_assoc', mul_sub, h1 t₁, h1 t₀]
  have hsplit_sum :
      ∑ m ∈ S, ∑ n ∈ S,
          ∫ t in t₀..t₁, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
            star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        (((t₁ - t₀) * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) : ℝ) : ℂ) +
          (Complex.I) * ∑ m ∈ S, ∑ n ∈ S,
            (if m = n then (0 : ℂ) else
              (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) *
                star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) /
                  ((Real.log m - Real.log n : ℝ) : ℂ)) -
          (Complex.I) * ∑ m ∈ S, ∑ n ∈ S,
            (if m = n then (0 : ℂ) else
              (c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) *
                star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) /
                  ((Real.log m - Real.log n : ℝ) : ℂ)) := by
    have hsplit1 : ∀ m ∈ S,
        ∑ n ∈ S,
            ∫ t in t₀..t₁, (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
          ((t₁ - t₀ : ℝ) : ℂ) * ((‖c m‖ ^ 2 : ℝ) : ℂ) +
            ∑ n ∈ S, (if m = n then (0 : ℂ) else
              Complex.I * ((c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I) *
                  star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I))) /
                ((Real.log m - Real.log n : ℝ) : ℂ)) -
              Complex.I * ((c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) *
                  star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I))) /
                ((Real.log m - Real.log n : ℝ) : ℂ))) := by
      intro m hm
      rw [← Finset.add_sum_erase S _ hm, hdiag_term m hm]
      congr 1
      · rw [Complex.ofReal_sub]
      · rw [← Finset.sum_erase_add S _ hm]
        have hdiag0 : (if m = m then (0 : ℂ) else
            Complex.I * ((c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I) *
                star (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I))) /
              ((Real.log m - Real.log m : ℝ) : ℂ)) -
            Complex.I * ((c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) *
                star (c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I))) /
              ((Real.log m - Real.log m : ℝ) : ℂ))) = 0 := by simp
        rw [hdiag0, add_zero]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hne : m ≠ n := (Finset.mem_erase.mp hn).1.symm
        rw [hoff_term m hm n (Finset.mem_erase.mp hn).2 hne]
        simp only [hne, ↓reduceIte]
        have hinvI : (-Complex.I)⁻¹ = Complex.I := by
          rw [inv_neg, inv_I, neg_neg]
        rw [div_eq_mul_inv, mul_inv, hinvI]
        ring
    rw [Finset.sum_congr rfl hsplit1, Finset.sum_add_distrib]
    have hdiagC :
        ∑ m ∈ S, ((t₁ - t₀ : ℝ) : ℂ) * ((‖c m‖ ^ 2 : ℝ) : ℂ) =
          (((t₁ - t₀) * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) : ℝ) : ℂ) := by
      rw [← Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_sum]
      congr 1
      refine Finset.sum_congr rfl fun n hn => by rw [hc_norm n hn]
    rw [hdiagC]
    have hif_sub : ∀ m n : ℕ,
        (if m = n then (0 : ℂ) else
          Complex.I * ((c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I) *
              star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I))) /
            ((Real.log m - Real.log n : ℝ) : ℂ)) -
          Complex.I * ((c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) *
              star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I))) /
            ((Real.log m - Real.log n : ℝ) : ℂ))) =
        (if m = n then (0 : ℂ) else
          Complex.I * ((c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I) *
              star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I))) /
            ((Real.log m - Real.log n : ℝ) : ℂ))) -
        (if m = n then (0 : ℂ) else
          Complex.I * ((c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I) *
              star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I))) /
            ((Real.log m - Real.log n : ℝ) : ℂ))) := by
      intro m n; split_ifs <;> simp
    simp_rw [hif_sub, Finset.sum_sub_distrib]
    have hpull1 : ∀ t : ℝ,
        ∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            Complex.I * ((c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I) *
                star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))) /
              ((Real.log m - Real.log n : ℝ) : ℂ))) =
          Complex.I * ∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ)) := by
      intro t
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hmn : m = n
      · simp [hmn]
      · simp only [hmn, ↓reduceIte]
    rw [hpull1 t₁, hpull1 t₀]
    ring
  have hlog_spaced : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      (N : ℝ)⁻¹ ≤ |Real.log m - Real.log n| := by
    intro m hm n hn hne
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmN := (Finset.mem_Icc.mp hm).2
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN := (Finset.mem_Icc.mp hn).2
    have hlog_step : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ N → (N : ℝ)⁻¹ ≤ Real.log b - Real.log a := by
      intro p q hp1 hpq hqN
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp1
      have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 1 ≤ q)
      have h1 : Real.log ((p : ℝ) / (q : ℝ)) ≤ (p : ℝ) / (q : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hp_pos hq_pos)
      have h2 : Real.log (q : ℝ) - Real.log (p : ℝ) = -Real.log ((p : ℝ) / (q : ℝ)) := by
        rw [Real.log_div hp_pos.ne' hq_pos.ne', neg_sub]
      have hqp1_nat : 1 ≤ q - p := by omega
      have hqp1 : (1 : ℝ) ≤ (q : ℝ) - (p : ℝ) := by
        have h' : (1 : ℝ) ≤ ((q - p : ℕ) : ℝ) := by exact_mod_cast hqp1_nat
        rwa [Nat.cast_sub hpq.le] at h'
      have hqN_R : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqN
      calc
        (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq_pos hqN_R
        _ = 1 / (q : ℝ) := (one_div _).symm
        _ ≤ ((q : ℝ) - (p : ℝ)) / (q : ℝ) := by gcongr
        _ = 1 - (p : ℝ) / (q : ℝ) := by field_simp [hq_pos.ne']
        _ ≤ -Real.log ((p : ℝ) / (q : ℝ)) := by linarith
        _ = Real.log (q : ℝ) - Real.log (p : ℝ) := h2.symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := hlog_step m n hm1 hlt hnN
      have habs : |Real.log m - Real.log n| = Real.log n - Real.log m := by
        rw [← neg_sub (Real.log n) (Real.log m), abs_neg, abs_of_nonneg]
        have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
        linarith
      rwa [habs]
    · have h := hlog_step n m hn1 hgt hmN
      have habs : |Real.log m - Real.log n| = Real.log m - Real.log n := by
        rw [abs_of_nonneg]
        have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
        linarith
      rwa [habs]
  have hhilb_u : ∀ t : ℝ,
      ‖∑ m ∈ S, ∑ n ∈ S,
          (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))‖ ≤
        Real.pi * (N : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    intro t
    have hN_inv_pos : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN1)
    have hh := hilbert_inequality_separated S (fun n => Real.log n) hN_inv_pos hlog_spaced
      (fun n => c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))
    have hinv_inv : ((N : ℝ)⁻¹)⁻¹ = (N : ℝ) := inv_inv _
    have hnorm_sum :
        ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2 =
          ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_unit : ‖(n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ = 1 := by
        rw [natCast_cpow_neg_it_dp hn1 t]
        have hrew : -((t * Real.log n : ℝ) : ℂ) * Complex.I =
            ((-(t * Real.log n) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [hrew]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, hn_unit, mul_one, hc_norm n hn]
    have hdec :
        ∑ m ∈ S, ∑ n ∈ S,
            (if m = n then (0 : ℂ) else
              (c m * (m : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                star (c n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) /
                  ((Real.log m - Real.log n : ℝ) : ℂ)) =
          ∑ r ∈ S, ∑ s ∈ S,
            @ite ℂ (r = s) (Classical.propDecidable _) 0
              ((c r * (r : ℂ) ^ (-(t : ℂ) * Complex.I)) *
                star (c s * (s : ℂ) ^ (-(t : ℂ) * Complex.I)) /
                  ((Real.log r - Real.log s : ℝ) : ℂ)) :=
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by split_ifs <;> rfl
    rw [hdec]
    rwa [hinv_inv, hnorm_sum] at hh
  have hdiffC :
      (((∫ t in t₀..t₁, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) -
          (t₁ - t₀) * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) : ℝ) : ℂ) =
        Complex.I * (∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))) -
          Complex.I * (∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))) := by
    rw [Complex.ofReal_sub, hintC, hsplit_sum]
    ring
  rw [← Complex.norm_real, hdiffC]
  calc
    ‖Complex.I * (∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))) -
          Complex.I * (∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ)))‖
        ≤ ‖Complex.I * (∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ)))‖ +
          ‖Complex.I * (∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ)))‖ := norm_sub_le _ _
    _ = ‖∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₁ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))‖ +
          ‖∑ m ∈ S, ∑ n ∈ S, (if m = n then (0 : ℂ) else
            (c m * (m : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) *
              star (c n * (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))‖ := by
          rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_I, one_mul]
    _ ≤ Real.pi * (N : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) +
          Real.pi * (N : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
          add_le_add (hhilb_u t₁) (hhilb_u t₀)
    _ = 2 * Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
          ring

/-- **Mean Value Theorem for Dirichlet Polynomials (Asymptotic Form on `[t₀, t₁]`)**:
for any `t₀ ≤ t₁` and `σ : ℝ`,
`‖(∫ t in t₀..t₁, ‖dirichletPoly a N (σ + i t)‖²) - (t₁ - t₀) * ∑_{1 ≤ n ≤ N} ‖a n‖² n^{-2σ}‖ ≤ 2π N ∑_{1 ≤ n ≤ N} ‖a n‖² n^{-2σ}`. -/
theorem dirichletPoly_mean_sq_asymp (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) :
    ‖(∫ t in t₀..t₁, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) -
        (t₁ - t₀) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)‖ ≤
      2 * Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
  norm_integral_dirichlet_sub_diag_le a N σ t₀ t₁ ht

/-- **Mean Value Theorem for Dirichlet Polynomials on `[0, T]` (Asymptotic Form)**:
for any `0 ≤ T`,
`‖(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N (i t)‖²) - T * ∑_{1 ≤ n ≤ N} ‖a n‖²‖ ≤ 2π N ∑_{1 ≤ n ≤ N} ‖a n‖²`. -/
theorem dirichletPoly_mean_sq_Icc_asymp (a : ℕ → ℂ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖(∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * Complex.I)‖ ^ 2) -
        T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2‖ ≤
      2 * Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := norm_integral_dirichlet_sub_diag_le a N 0 0 T hT
  simpa using h

/-- **Mean Value Theorem for Dirichlet Polynomials on `[0, T]` (Upper Bound)**:
for any `0 ≤ T`,
`∫ t in (0 : ℝ)..T, ‖dirichletPoly a N (i t)‖² ≤ (T + 2π N) * ∑_{1 ≤ n ≤ N} ‖a n‖²`. -/
theorem dirichletPoly_mean_sq_Icc_le (a : ℕ → ℂ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖dirichletPoly a N ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      (T + 2 * Real.pi * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := dirichletPoly_mean_sq_Icc_asymp a N hT
  rw [Real.norm_eq_abs, abs_le] at h
  linarith [h.2]

/-- **Mean Value Theorem for Dirichlet Polynomials on `[-T, T]` (Asymptotic Form)**:
for any `0 ≤ T` and `σ : ℝ`,
`‖(∫ t in (-T)..T, ‖dirichletPoly a N (σ + i t)‖²) - 2 T ∑_{1 ≤ n ≤ N} ‖a n‖² n^{-2σ}‖ ≤ 2π N ∑_{1 ≤ n ≤ N} ‖a n‖² n^{-2σ}`. -/
theorem dirichletPoly_mean_sq_symm_asymp (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖(∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) -
        2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)‖ ≤
      2 * Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  have h := norm_integral_dirichlet_sub_diag_le a N σ (-T) T (by linarith)
  simpa [sub_neg_eq_add, two_mul] using h

/-- **Mean Value Theorem for Dirichlet Polynomials on `[-T, T]` (Upper Bound)**:
for any `0 ≤ T` and `σ : ℝ`,
`∫ t in (-T)..T, ‖dirichletPoly a N (σ + i t)‖² ≤ (2 T + 2π N) * ∑_{1 ≤ n ≤ N} ‖a n‖² n^{-2σ}`. -/
theorem dirichletPoly_mean_sq_symm_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
      (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  have h := dirichletPoly_mean_sq_symm_asymp a N σ hT
  rw [Real.norm_eq_abs, abs_le] at h
  linarith [h.2]

/-- **Mean Value Theorem for Dirichlet Polynomials Supported on `(M, M + N]`**:
for any `M N : ℕ` and `0 ≤ T`,
`∫ t in t₀..(t₀ + T), ‖∑_{n ∈ (M, M+N]} a n * n^{-it}‖² ≤ (T + 2π (M + N)) * ∑_{n ∈ (M, M+N]} ‖a n‖²`. -/
theorem dirichletPoly_mean_sq_Ioc_le (a : ℕ → ℂ) (M N : ℕ) (t₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in t₀..(t₀ + T),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2 ≤
      (T + 2 * Real.pi * ((M + N : ℕ) : ℝ)) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  let a' : ℕ → ℂ := fun n => if M < n then a n else 0
  have hpoly : ∀ t : ℝ,
      ∑ n ∈ Finset.Ioc M (M + N), a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
        dirichletPoly a' (M + N) ((t : ℂ) * Complex.I) := by
    intro t
    rw [dirichletPoly]
    have hsub : Finset.Ioc M (M + N) ⊆ Finset.Icc 1 (M + N) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      exact ⟨by omega, hn.2⟩
    have hsplit :
        ∑ n ∈ Finset.Icc 1 (M + N), a' n * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) =
          ∑ n ∈ Finset.Ioc M (M + N), a' n * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
      rw [← Finset.sum_subset hsub]
      intro n hn hnot
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_Ioc] at hnot
      have hnotlt : ¬ M < n := fun h => hnot ⟨h, hn.2⟩
      simp [a', hnotlt]
    rw [hsplit]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [a', (Finset.mem_Ioc.mp hn).1]
  have hnorm_sum :
      ∑ n ∈ Finset.Icc 1 (M + N), ‖a' n‖ ^ 2 =
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
    have hsub : Finset.Ioc M (M + N) ⊆ Finset.Icc 1 (M + N) := by
      intro n hn; rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; exact ⟨by omega, hn.2⟩
    have hzero : ∀ n ∈ Finset.Icc 1 (M + N), n ∉ Finset.Ioc M (M + N) →
        ‖a' n‖ ^ 2 = 0 := by
      intro n hn hnot
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_Ioc] at hnot
      have hnotlt : ¬ M < n := fun h => hnot ⟨h, hn.2⟩
      simp [a', hnotlt]
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [a', (Finset.mem_Ioc.mp hn).1]
  have hbd := norm_integral_dirichlet_sub_diag_le a' (M + N) 0 t₀ (t₀ + T) (by linarith)
  have hbd' :
      ‖(∫ t in t₀..(t₀ + T), ‖dirichletPoly a' (M + N) ((t : ℂ) * Complex.I)‖ ^ 2) -
          T * ∑ n ∈ Finset.Icc 1 (M + N), ‖a' n‖ ^ 2‖ ≤
        2 * Real.pi * ((M + N : ℕ) : ℝ) * ∑ n ∈ Finset.Icc 1 (M + N), ‖a' n‖ ^ 2 := by
    simpa [add_sub_cancel_left] using hbd
  rw [Real.norm_eq_abs, abs_le] at hbd'
  have hle : ∫ t in t₀..(t₀ + T),
      ‖dirichletPoly a' (M + N) ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      (T + 2 * Real.pi * ((M + N : ℕ) : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (M + N), ‖a' n‖ ^ 2 := by
    linarith [hbd'.2]
  rw [hnorm_sum] at hle
  refine le_of_eq_of_le ?_ hle
  exact intervalIntegral.integral_congr fun t _ => by rw [hpoly t]

end MeanValueTheorem

section CharacterLargeSieve

/-- **Multiplicative Character Large Sieve Inequality**:
for any coefficient sequence `a : ℕ → ℂ` and integers `M N Q : ℕ`,
`∑ q ∈ Icc 1 Q, (q / φ(q)) ∑^*_{χ mod q} ‖∑_{n ∈ (M, M+N]} a n * χ n‖² ≤ (N + Q²) * ∑_{n ∈ (M, M+N]} ‖a n‖²`. -/
theorem character_large_sieve_dirichlet (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (Nat.totient q : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simpa using mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      (Finset.sum_nonneg fun n (_ : n ∈ Finset.Ioc M (M + N)) => sq_nonneg ‖a n‖)
  exact character_large_sieve_add_sq a M hN hQ

/-- **Multiplicative Character Large Sieve Inequality on `[1, N]`**:
special case `M = 0` with summation over `Finset.Icc 1 N`. -/
theorem character_large_sieve_dirichlet_Icc (a : ℕ → ℂ) (N Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (Nat.totient q : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  simpa [hIoc] using character_large_sieve_dirichlet a 0 N Q

/-- **Unweighted Multiplicative Character Large Sieve Inequality**:
dropping the factor `q / φ(q) ≥ 1`,
`∑ q ∈ Icc 1 Q, ∑^*_{χ mod q} ‖∑_{n ∈ (M, M+N]} a n * χ n‖² ≤ (N + Q²) * ∑_{n ∈ (M, M+N]} ‖a n‖²`. -/
theorem character_large_sieve_dirichlet_unweighted (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
            (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have h1 :
      ∑ q ∈ Finset.Icc 1 Q,
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 := by
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_pos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq_pos
    have hphi_le : (Nat.totient q : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.totient_le q
    have hge1 : (1 : ℝ) ≤ (q : ℝ) / (Nat.totient q : ℝ) :=
      (one_le_div hphi_pos).mpr hphi_le
    exact le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) hge1
  exact h1.trans (character_large_sieve_dirichlet a M N Q)

end CharacterLargeSieve

section HybridLargeSieve

open scoped FourierTransform

/-- The unit tent (Fejér) kernel `max (1 - |x|) 0` supported on `[-1, 1]`. -/
def tentKernel (x : ℝ) : ℝ :=
  max (1 - |x|) 0

/-- Nonnegativity of `tentKernel`. -/
theorem tentKernel_nonneg (x : ℝ) : 0 ≤ tentKernel x :=
  le_max_right _ _

/-- Upper bound `tentKernel x ≤ 1`. -/
theorem tentKernel_le_one (x : ℝ) : tentKernel x ≤ 1 := by
  dsimp [tentKernel]
  exact max_le (sub_le_self 1 (abs_nonneg x)) zero_le_one

/-- Symmetry of `tentKernel`. -/
theorem tentKernel_neg (x : ℝ) : tentKernel (-x) = tentKernel x := by
  simp [tentKernel, abs_neg]

/-- `tentKernel` is continuous on `ℝ`. -/
theorem continuous_tentKernel : Continuous tentKernel :=
  (continuous_const.sub continuous_abs).max continuous_const

private theorem tentKernel_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tentKernel x = 0 := by
  dsimp [tentKernel]
  exact max_eq_right (by linarith)

private def boxHalfDP (x : ℝ) : ℝ :=
  if |x| ≤ 1 / 2 then 1 else 0

private theorem boxHalfDP_eq_indicator (a : ℝ) :
    (fun u : ℝ => boxHalfDP (u - a)) =
      (Set.Icc (a - 1 / 2) (a + 1 / 2)).indicator (fun _ => (1 : ℝ)) := by
  ext u
  dsimp [boxHalfDP]
  rw [Set.indicator_apply]
  have hmem : (u ∈ Set.Icc (a - 1 / 2) (a + 1 / 2)) ↔ |u - a| ≤ 1 / 2 := by
    rw [Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith
  by_cases h : |u - a| ≤ 1 / 2
  · have hm : u ∈ Set.Icc (a - 1 / 2) (a + 1 / 2) := hmem.mpr h
    simp only [h, hm, ↓reduceIte]
  · have hm : u ∉ Set.Icc (a - 1 / 2) (a + 1 / 2) := fun hm => h (hmem.mp hm)
    simp only [h, hm, ↓reduceIte]

private theorem integrable_boxHalfDP_sub (a : ℝ) :
    Integrable (fun u : ℝ => boxHalfDP (u - a)) := by
  rw [boxHalfDP_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (hs := measure_Icc_lt_top.ne))

private theorem integrable_finset_sum_dp {ι β : Type*} [NormedAddCommGroup β]
    (s : Finset ι) (f : ι → ℝ → β) (hf : ∀ i ∈ s, Integrable (f i)) :
    Integrable (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integrable_zero ℝ β volume
  | insert a s ha ih =>
    have hfun : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; exact Finset.sum_insert ha
    rw [hfun]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem intervalIntegrable_finset_sum_dp {ι β : Type*} [NormedAddCommGroup β]
    (s : Finset ι) (f : ι → ℝ → β) {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntervalIntegrable.zero
  | insert c s hc ih =>
    have hfun : (fun x => ∑ i ∈ insert c s, f i x) = fun x => f c x + ∑ i ∈ s, f i x := by
      funext x; exact Finset.sum_insert hc
    rw [hfun]
    exact (hf c (Finset.mem_insert_self c s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem integral_ofReal_dp {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
  Complex.ofRealCLM.integral_comp_comm hf

/-- Convolution representation of `tentKernel`:
`tentKernel x = ∫ u : ℝ, (if |u| ≤ 1/2 then 1 else 0) * (if |u - x| ≤ 1/2 then 1 else 0)`. -/
theorem tentKernel_eq_conv (x : ℝ) :
    tentKernel x =
      ∫ u : ℝ, (if |u| ≤ 1 / 2 then (1 : ℝ) else 0) * (if |u - x| ≤ 1 / 2 then (1 : ℝ) else 0) := by
  let a : ℝ := max (-(1 / 2 : ℝ)) (x - 1 / 2)
  let b : ℝ := min (1 / 2 : ℝ) (x + 1 / 2)
  have hfun :
      (fun u : ℝ => (if |u| ≤ 1 / 2 then (1 : ℝ) else 0) *
          (if |u - x| ≤ 1 / 2 then (1 : ℝ) else 0)) =
        (Set.Icc a b).indicator (fun _ => (1 : ℝ)) := by
    ext u
    rw [Set.indicator_apply]
    have hmem : u ∈ Set.Icc a b ↔ |u| ≤ 1 / 2 ∧ |u - x| ≤ 1 / 2 := by
      simp only [Set.mem_Icc, a, b, max_le_iff, le_min_iff, abs_le]
      constructor
      · intro h
        exact ⟨⟨by linarith [h.1.1], by linarith [h.2.1]⟩,
          ⟨by linarith [h.1.2], by linarith [h.2.2]⟩⟩
      · intro h
        exact ⟨⟨by linarith [h.1.1], by linarith [h.2.1]⟩,
          ⟨by linarith [h.1.2], by linarith [h.2.2]⟩⟩
    by_cases h1 : |u| ≤ 1 / 2 <;> by_cases h2 : |u - x| ≤ 1 / 2
    · have hm : u ∈ Set.Icc a b := hmem.mpr ⟨h1, h2⟩
      simp only [h1, h2, hm, ↓reduceIte, mul_one]
    · have hm : u ∉ Set.Icc a b := fun hm => h2 (hmem.mp hm).2
      simp only [h1, h2, hm, ↓reduceIte, mul_zero]
    · have hm : u ∉ Set.Icc a b := fun hm => h1 (hmem.mp hm).1
      simp only [h1, h2, hm, ↓reduceIte, zero_mul]
    · have hm : u ∉ Set.Icc a b := fun hm => h1 (hmem.mp hm).1
      simp only [h1, h2, hm, ↓reduceIte, zero_mul]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    Real.volume_real_Icc, smul_eq_mul, mul_one]
  dsimp [tentKernel, a, b]
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx]
    have hmin : min (1 / 2 : ℝ) (x + 1 / 2) = x + 1 / 2 := min_eq_right (by linarith)
    have hmax : max (-(1 / 2 : ℝ)) (x - 1 / 2) = -(1 / 2 : ℝ) := max_eq_left (by linarith)
    rw [hmin, hmax]
    congr 1; ring
  · rw [abs_of_nonneg hx]
    have hmin : min (1 / 2 : ℝ) (x + 1 / 2) = 1 / 2 := min_eq_left (by linarith)
    have hmax : max (-(1 / 2 : ℝ)) (x - 1 / 2) = x - 1 / 2 := max_eq_right (by linarith)
    rw [hmin, hmax]
    congr 1; ring

/-- The squared Fejér sinc kernel `fejerSincSq t = (sin(π t) / (π t))^2` (with value `1` at `0`). -/
def fejerSincSq (t : ℝ) : ℝ :=
  if t = 0 then 1 else (Real.sin (Real.pi * t) / (Real.pi * t)) ^ 2

/-- Nonnegativity of `fejerSincSq`. -/
theorem fejerSincSq_nonneg (t : ℝ) : 0 ≤ fejerSincSq t := by
  dsimp [fejerSincSq]
  split_ifs
  · exact zero_le_one
  · exact sq_nonneg _

/-- Uniform bound `fejerSincSq t ≤ 1`. -/
theorem fejerSincSq_le_one (t : ℝ) : fejerSincSq t ≤ 1 := by
  dsimp [fejerSincSq]
  split_ifs with ht
  · exact le_rfl
  · have hpi_t : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    have hratio : |Real.sin (Real.pi * t) / (Real.pi * t)| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hpi_t)).mpr (Real.abs_sin_le_abs (x := Real.pi * t))
    nlinarith [sq_abs (Real.sin (Real.pi * t) / (Real.pi * t)),
      abs_nonneg (Real.sin (Real.pi * t) / (Real.pi * t))]

private theorem fejerSincSq_le_two_div (t : ℝ) :
    fejerSincSq t ≤ 2 / (1 + (Real.pi * t) ^ 2) := by
  let x := Real.pi * t
  have hx1 : 0 < 1 + x ^ 2 := by positivity
  by_cases hsmall : |x| ≤ 1
  · have hsq : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    have h1 : (1 : ℝ) ≤ 2 / (1 + x ^ 2) := (one_le_div hx1).mpr (by linarith)
    exact (fejerSincSq_le_one t).trans h1
  · have hgt : 1 < |x| := lt_of_not_ge hsmall
    have hx_ne : x ≠ 0 := by intro h0; rw [h0, abs_zero] at hgt; linarith
    have ht_ne : t ≠ 0 := fun h0 => hx_ne (by dsimp [x]; rw [h0, mul_zero])
    have hsq1 : 1 < x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have h1_le : (1 : ℝ) / x ^ 2 ≤ 2 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) hx1]
      nlinarith
    dsimp [fejerSincSq]
    simp only [ht_ne, ↓reduceIte]
    calc
      (Real.sin x / x) ^ 2 = Real.sin x ^ 2 / x ^ 2 := div_pow _ _ _
      _ ≤ 1 / x ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (sq_nonneg x)
        have := Real.sin_sq_le_one x
        exact this
      _ ≤ 2 / (1 + x ^ 2) := h1_le

private theorem integrable_fejerSincSq :
    Integrable (fun t : ℝ => (fejerSincSq t : ℂ)) := by
  have hdom : Integrable (fun t : ℝ => 2 / (1 + (Real.pi * t) ^ 2)) := by
    have hbase := integrable_inv_one_add_mul_sq Real.pi_ne_zero
    have hconst := hbase.const_mul (2 : ℝ)
    refine hconst.congr (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [div_eq_mul_inv]
  have hmeas : Measurable (fun t : ℝ => (fejerSincSq t : ℂ)) := by
    refine Complex.continuous_ofReal.measurable.comp ?_
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).div
        (measurable_const.mul measurable_id) |>.pow_const 2)
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (fejerSincSq_nonneg t)]
  exact fejerSincSq_le_two_div t

/-- Explicit Fourier transform of the unit tent kernel:
`𝓕 (fun x => (tentKernel x : ℂ)) t = (fejerSincSq t : ℂ)`. -/
theorem fourier_tentKernel (t : ℝ) :
    𝓕 (fun x : ℝ => (tentKernel x : ℂ)) t = (fejerSincSq t : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hsupp : ∀ x ∉ Set.Ioc (-1 : ℝ) 1,
      Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) • (tentKernel x : ℂ) = 0 := by
    intro x hx
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h1 : 1 ≤ |x| := by
      rcases hx with hx1 | hx1
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; exact hx1.le
    rw [tentKernel_eq_zero_of_one_le h1, Complex.ofReal_zero, smul_zero]
  have hIoc :
      (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) • (tentKernel x : ℂ)) =
        ∫ x in (-1 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x _ => smul_eq_mul _ _
  rw [hIoc]
  have hint :
      (∫ x in (-1 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ)) =
        (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ)) +
          ∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ) := by
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ)) :=
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
        (Complex.continuous_ofReal.comp continuous_tentKernel)
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hleft :
      (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ)) =
        ∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (1 + (x : ℂ)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Icc] at hx
    have htent : tentKernel x = 1 + x := by
      dsimp [tentKernel]
      rw [abs_of_nonpos hx.2, sub_neg_eq_add]
      exact max_eq_left (by linarith [hx.1])
    rw [htent, Complex.ofReal_add, Complex.ofReal_one]
  have hright :
      (∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (tentKernel x : ℂ)) =
        ∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (1 - (x : ℂ)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hx
    have htent : tentKernel x = 1 - x := by
      dsimp [tentKernel]
      rw [abs_of_nonneg hx.1]
      exact max_eq_left (by linarith [hx.2])
    rw [htent, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hint, hleft, hright]
  have hX : ∀ x : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) x := fun _ =>
    Complex.ofRealCLM.hasDerivAt
  by_cases ht0 : t = 0
  · subst ht0
    simp only [fejerSincSq, ↓reduceIte, Complex.ofReal_one, mul_zero, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, one_mul]
    have hL : (∫ x in (-1 : ℝ)..0, (1 : ℂ) + (x : ℂ)) = 1 / 2 := by
      have hreal : (∫ x in (-1 : ℝ)..0, ((1 + x : ℝ) : ℂ)) =
          ((∫ x in (-1 : ℝ)..0, (1 + x : ℝ) : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
      have hrew : (∫ x in (-1 : ℝ)..0, (1 : ℂ) + (x : ℂ)) =
          ∫ x in (-1 : ℝ)..0, ((1 + x : ℝ) : ℂ) :=
        intervalIntegral.integral_congr fun x _ => by simp
      rw [hrew, hreal, intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
        (g := fun x : ℝ => x) (μ := volume) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
        intervalIntegral.integral_const, integral_id]
      norm_num
    have hR : (∫ x in (0 : ℝ)..1, (1 : ℂ) - (x : ℂ)) = 1 / 2 := by
      have hreal : (∫ x in (0 : ℝ)..1, ((1 - x : ℝ) : ℂ)) =
          ((∫ x in (0 : ℝ)..1, (1 - x : ℝ) : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
      have hrew : (∫ x in (0 : ℝ)..1, (1 : ℂ) - (x : ℂ)) =
          ∫ x in (0 : ℝ)..1, ((1 - x : ℝ) : ℂ) :=
        intervalIntegral.integral_congr fun x _ => by simp
      rw [hrew, hreal, intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
        (g := fun x : ℝ => x) (μ := volume) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
        intervalIntegral.integral_const, integral_id]
      norm_num
    rw [hL, hR]
    norm_num
  · let c : ℂ := ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I
    have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht0)) Complex.I_ne_zero
    have harg : ∀ x : ℝ, (↑(-2 * Real.pi * x * t) * Complex.I : ℂ) = c * (x : ℂ) := by
      intro x
      dsimp [c]
      push_cast
      ring
    have hL :
        (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (1 + (x : ℂ))) =
          1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
      have hrew :
          (∫ x in (-1 : ℝ)..0, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (1 + (x : ℂ))) =
            ∫ x in (-1 : ℝ)..0, Complex.exp (c * (x : ℂ)) * (1 + (x : ℂ)) :=
        intervalIntegral.integral_congr fun x _ => by rw [harg x]
      rw [hrew]
      let F₁ : ℝ → ℂ := fun u => Complex.exp (c * (u : ℂ)) * ((1 + (u : ℂ)) / c - 1 / c ^ 2)
      have hd : ∀ x ∈ Set.uIcc (-1 : ℝ) 0,
          HasDerivAt F₁ (Complex.exp (c * (x : ℂ)) * (1 + (x : ℂ))) x := by
        intro x _
        have hcexp : HasDerivAt (fun u : ℝ => Complex.exp (c * (u : ℂ)))
            (Complex.exp (c * (x : ℂ)) * (c * 1)) x := ((hX x).const_mul c).cexp
        have hlin : HasDerivAt (fun u : ℝ => (1 + (u : ℂ)) / c - 1 / c ^ 2) (1 / c) x := by
          simpa using (((hX x).const_add 1).div_const c).sub_const (1 / c ^ 2)
        have hmul := hcexp.mul hlin
        refine hmul.congr_deriv ?_
        field_simp [hc]
        ring
      have hcont : Continuous (fun u : ℝ => Complex.exp (c * (u : ℂ)) * (1 + (u : ℂ))) :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
          (continuous_const.add Complex.continuous_ofReal)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
      dsimp [F₁]
      push_cast
      rw [mul_zero, Complex.exp_zero]
      field_simp [hc]
      ring
    have hR :
        (∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (1 - (x : ℂ))) =
          Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2 := by
      have hrew :
          (∫ x in (0 : ℝ)..1, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) * (1 - (x : ℂ))) =
            ∫ x in (0 : ℝ)..1, Complex.exp (c * (x : ℂ)) * (1 - (x : ℂ)) :=
        intervalIntegral.integral_congr fun x _ => by rw [harg x]
      rw [hrew]
      let F₂ : ℝ → ℂ := fun u => Complex.exp (c * (u : ℂ)) * ((1 - (u : ℂ)) / c + 1 / c ^ 2)
      have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt F₂ (Complex.exp (c * (x : ℂ)) * (1 - (x : ℂ))) x := by
        intro x _
        have hcexp : HasDerivAt (fun u : ℝ => Complex.exp (c * (u : ℂ)))
            (Complex.exp (c * (x : ℂ)) * (c * 1)) x := ((hX x).const_mul c).cexp
        have hlin : HasDerivAt (fun u : ℝ => (1 - (u : ℂ)) / c + 1 / c ^ 2) ((-1) / c) x := by
          simpa using (((hX x).const_sub 1).div_const c).add_const (1 / c ^ 2)
        have hmul := hcexp.mul hlin
        refine hmul.congr_deriv ?_
        field_simp [hc]
        ring
      have hcont : Continuous (fun u : ℝ => Complex.exp (c * (u : ℂ)) * (1 - (u : ℂ))) :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
          (continuous_const.sub Complex.continuous_ofReal)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
      dsimp [F₂]
      push_cast
      rw [mul_zero, Complex.exp_zero]
      field_simp [hc]
      ring
    rw [hL, hR]
    dsimp [fejerSincSq]
    simp only [ht0, ↓reduceIte]
    have hexp_cos : Complex.exp c + Complex.exp (-c) = 2 * Complex.cos (2 * ((Real.pi * t : ℝ) : ℂ)) := by
      have hc1 : c = (-((2 * (Real.pi * t) : ℝ) : ℂ)) * Complex.I := by
        dsimp [c]; push_cast; ring
      have hc2 : -c = (((2 * (Real.pi * t) : ℝ) : ℂ)) * Complex.I := by
        dsimp [c]; push_cast; ring
      have he1 : Complex.exp c =
          Complex.cos (-(2 * ((Real.pi * t : ℝ) : ℂ))) +
            Complex.sin (-(2 * ((Real.pi * t : ℝ) : ℂ))) * Complex.I := by
        rw [hc1]; push_cast; rw [Complex.exp_mul_I]
      have he2 : Complex.exp (-c) =
          Complex.cos (2 * ((Real.pi * t : ℝ) : ℂ)) +
            Complex.sin (2 * ((Real.pi * t : ℝ) : ℂ)) * Complex.I := by
        rw [hc2]; push_cast; rw [Complex.exp_mul_I]
      rw [he1, he2, Complex.cos_neg, Complex.sin_neg]
      ring
    have hcos_sin : Complex.exp c + Complex.exp (-c) - 2 =
        -4 * Complex.sin ((Real.pi * t : ℝ) : ℂ) ^ 2 := by
      rw [hexp_cos, Complex.cos_two_mul]
      linear_combination 4 * Complex.sin_sq_add_cos_sq ((Real.pi * t : ℝ) : ℂ)
    have hc_sq : c ^ 2 = -4 * ((Real.pi * t : ℝ) : ℂ) ^ 2 := by
      dsimp [c]
      push_cast
      rw [mul_pow, Complex.I_sq]
      ring
    have hpi_t : ((Real.pi * t : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht0)
    calc
      1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 + (Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2)
          = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by ring
      _ = (-4 * Complex.sin ((Real.pi * t : ℝ) : ℂ) ^ 2) / (-4 * ((Real.pi * t : ℝ) : ℂ) ^ 2) := by
          rw [hcos_sin, hc_sq]
      _ = (Complex.sin ((Real.pi * t : ℝ) : ℂ) / ((Real.pi * t : ℝ) : ℂ)) ^ 2 := by
          field_simp [hpi_t]
      _ = (((Real.sin (Real.pi * t) / (Real.pi * t)) ^ 2 : ℝ) : ℂ) := by
          push_cast; rfl

/-- Fourier inversion representation of the tent kernel:
`(tentKernel ξ : ℂ) = ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * t * ξ) * Complex.I) * (fejerSincSq t : ℂ)`. -/
theorem tentKernel_eq_integral_fejerSincSq (ξ : ℝ) :
    (tentKernel ξ : ℂ) =
      ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * t * ξ) * Complex.I) * (fejerSincSq t : ℂ) := by
  have hf_int : Integrable (fun x : ℝ => (tentKernel x : ℂ)) := by
    have hind :
        (fun x : ℝ => (tentKernel x : ℂ)) =
          (Set.Icc (-1 : ℝ) 1).indicator (fun x : ℝ => (tentKernel x : ℂ)) := by
      ext x
      rw [Set.indicator_apply]
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
      · simp [hx]
      · simp only [hx, ↓reduceIte]
        rw [Set.mem_Icc, not_and_or, not_le] at hx
        have h1 : 1 ≤ |x| := by
          rcases hx with hx1 | hx1
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_nonneg (by linarith)]; linarith
        rw [tentKernel_eq_zero_of_one_le h1, Complex.ofReal_zero]
    rw [hind]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      ((Complex.continuous_ofReal.comp continuous_tentKernel).continuousOn.integrableOn_Icc)
  have hFf_eq : 𝓕 (fun x : ℝ => (tentKernel x : ℂ)) = fun t : ℝ => (fejerSincSq t : ℂ) :=
    funext fourier_tentKernel
  have hFf_int : Integrable (𝓕 (fun x : ℝ => (tentKernel x : ℂ))) := by
    rw [hFf_eq]
    exact integrable_fejerSincSq
  have hinv := (Complex.continuous_ofReal.comp continuous_tentKernel).fourierInv_fourier_eq
    hf_int hFf_int
  have hinv' : 𝓕⁻ (𝓕 (fun x : ℝ => (tentKernel x : ℂ))) = fun x : ℝ => (tentKernel x : ℂ) := hinv
  have hat := congrFun hinv' ξ
  rw [hFf_eq, Real.fourierInv_eq'] at hat
  refine hat.symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  ring_nf

private theorem integrable_fejerSincSq_div (T : ℝ) (hT : 0 < T) :
    Integrable (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T))) := by
  have hre : Integrable (fun t : ℝ => fejerSincSq t) := by
    have hC := integrable_fejerSincSq.re
    refine hC.congr (Filter.Eventually.of_forall fun t => Complex.ofReal_re _)
  have ha : (2 * Real.pi * T)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  refine (hre.comp_mul_left' ha).congr (Filter.Eventually.of_forall fun τ => ?_)
  dsimp only
  rw [div_eq_inv_mul]

private theorem integrable_fejerSincSq_div_cexp (T ξ : ℝ) (hT : 0 < T) :
    Integrable (fun τ : ℝ =>
      (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) * Complex.exp (Complex.I * (τ : ℂ) * (ξ : ℂ))) := by
  have hdom : Integrable (fun τ : ℝ => ‖fejerSincSq (τ / (2 * Real.pi * T))‖) :=
    (integrable_fejerSincSq_div T hT).norm
  have hmeas : AEStronglyMeasurable (fun τ : ℝ =>
      (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
        Complex.exp (Complex.I * (τ : ℂ) * (ξ : ℂ))) volume := by
    have hm1 : Measurable (fun τ : ℝ => (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp <|
        (Measurable.ite (measurableSet_singleton 0) measurable_const
          ((Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)).div
            (measurable_const.mul measurable_id) |>.pow_const 2)).comp
          (measurable_id.div_const _)
    have hc2 : Continuous (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (ξ : ℂ))) :=
      Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
    exact (hm1.mul hc2.measurable).aestronglyMeasurable
  refine hdom.mono' hmeas (Filter.Eventually.of_forall fun τ => ?_)
  rw [norm_mul, Complex.norm_real]
  have he : ‖Complex.exp (Complex.I * (τ : ℂ) * (ξ : ℂ))‖ = 1 := by
    have harg : Complex.I * (τ : ℂ) * (ξ : ℂ) = ((τ * ξ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [he, mul_one]

private theorem tentKernel_scale_integral_eq (T ξ : ℝ) (hT : 0 < T) :
    ((2 * Real.pi * T : ℝ) : ℂ) * (tentKernel (T * ξ) : ℂ) =
      ∫ τ : ℝ, (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
        Complex.exp (Complex.I * (τ : ℂ) * (ξ : ℂ)) := by
  let a : ℝ := (2 * Real.pi * T)⁻¹
  have hsc := Measure.integral_comp_mul_left
    (fun t : ℝ => (fejerSincSq t : ℂ) * Complex.exp (↑(2 * Real.pi * t * (T * ξ)) * Complex.I)) a
  have ha_inv : |a⁻¹| = 2 * Real.pi * T := by
    dsimp [a]; rw [inv_inv, abs_of_pos (by positivity)]
  rw [ha_inv] at hsc
  have htent := tentKernel_eq_integral_fejerSincSq (T * ξ)
  have htent' : (tentKernel (T * ξ) : ℂ) =
      ∫ t : ℝ, (fejerSincSq t : ℂ) * Complex.exp (↑(2 * Real.pi * t * (T * ξ)) * Complex.I) := by
    rw [htent]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
  rw [← htent', Complex.real_smul] at hsc
  rw [← hsc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  dsimp [a]
  have h1 : (2 * Real.pi * T)⁻¹ * τ = τ / (2 * Real.pi * T) := (div_eq_inv_mul _ _).symm
  have h2 : (↑(2 * Real.pi * (τ / (2 * Real.pi * T)) * (T * ξ)) * Complex.I : ℂ) =
      Complex.I * (τ : ℂ) * (ξ : ℂ) := by
    have hreal : 2 * Real.pi * (τ / (2 * Real.pi * T)) * (T * ξ) = τ * ξ := by
      field_simp [hT.ne', Real.pi_ne_zero]
    rw [hreal]
    push_cast
    ring
  rw [h1, h2]

private theorem integrable_boxHalfDP_prod (a b : ℝ) :
    Integrable (fun u : ℝ => boxHalfDP (u - a) * boxHalfDP (u - b)) := by
  refine (integrable_boxHalfDP_sub a).mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · have hm : ∀ c : ℝ, Measurable (fun u : ℝ => boxHalfDP (u - c)) := fun c => by
      rw [boxHalfDP_eq_indicator]
      exact measurable_const.indicator measurableSet_Icc
    exact ((hm a).mul (hm b)).aestronglyMeasurable
  · have hnonneg : ∀ c u : ℝ, 0 ≤ boxHalfDP (u - c) := fun c u => by
      dsimp [boxHalfDP]; split_ifs <;> norm_num
    have hle1 : ∀ c u : ℝ, boxHalfDP (u - c) ≤ 1 := fun c u => by
      dsimp [boxHalfDP]; split_ifs <;> norm_num
    rw [Real.norm_of_nonneg (mul_nonneg (hnonneg a u) (hnonneg b u))]
    exact mul_le_of_le_one_right (hnonneg a u) (hle1 b u)

private theorem tentKernel_eq_conv_boxHalfDP (x : ℝ) :
    tentKernel x = ∫ u : ℝ, boxHalfDP u * boxHalfDP (u - x) :=
  tentKernel_eq_conv x

private theorem tent_integral_identity_frequencies (S : Finset ℕ) (ξ : ℕ → ℝ)
    (c : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ τ : ℝ, fejerSincSq (τ / (2 * Real.pi * T)) *
        ‖∑ n ∈ S, c n * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))‖ ^ 2 =
      (2 * Real.pi * T) *
        ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 := by
  let F : ℝ → ℂ := fun τ => ∑ n ∈ S, c n * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))
  have hstar_phase : ∀ (n : ℕ) (τ : ℝ),
      (starRingEnd ℂ) (Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))) =
        Complex.exp (Complex.I * (τ : ℂ) * (ξ n : ℂ)) := by
    intro n τ
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hnorm_sq : ∀ τ : ℝ,
      ((‖F τ‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          (c m * (starRingEnd ℂ) (c n)) *
            Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ)) := by
    intro τ
    dsimp [F]
    have hC :
        ((‖∑ n ∈ S, c n * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))‖ ^ 2 : ℝ) : ℂ) =
          (∑ m ∈ S, c m * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ m : ℂ)))) *
            (starRingEnd ℂ) (∑ n ∈ S, c n * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rw [hC, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [map_mul, hstar_phase n τ]
    have hexp :
        Complex.exp (-(Complex.I * (τ : ℂ) * (ξ m : ℂ))) *
            Complex.exp (Complex.I * (τ : ℂ) * (ξ n : ℂ)) =
          Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    calc
      c m * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ m : ℂ))) *
          ((starRingEnd ℂ) (c n) * Complex.exp (Complex.I * (τ : ℂ) * (ξ n : ℂ)))
          = (c m * (starRingEnd ℂ) (c n)) *
              (Complex.exp (-(Complex.I * (τ : ℂ) * (ξ m : ℂ))) *
                Complex.exp (Complex.I * (τ : ℂ) * (ξ n : ℂ))) := by ring
      _ = (c m * (starRingEnd ℂ) (c n)) *
            Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ)) := by
          rw [hexp]
  have hLHS_int :
      Integrable (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2) := by
    let C₀ : ℝ := (∑ n ∈ S, ‖c n‖) ^ 2
    have hF_bd : ∀ τ : ℝ, ‖F τ‖ ^ 2 ≤ C₀ := by
      intro τ
      have h1 : ‖F τ‖ ≤ ∑ n ∈ S, ‖c n‖ := by
        dsimp [F]
        refine (norm_sum_le S _).trans (Finset.sum_le_sum fun n hn => ?_)
        rw [norm_mul]
        have harg : -(Complex.I * (τ : ℂ) * (ξ n : ℂ)) =
            ((-(τ * ξ n) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hdom : Integrable (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T)) * C₀) :=
      (integrable_fejerSincSq_div T hT).mul_const C₀
    have hcontF : Continuous F := by
      dsimp [F]
      refine continuous_finset_sum_dp S _ fun n hn => continuous_const.mul ?_
      exact Complex.continuous_exp.comp
        (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)
    have hmeas : AEStronglyMeasurable
        (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2) volume :=
      ((integrable_fejerSincSq_div T hT).aestronglyMeasurable.mul
        ((continuous_norm.comp hcontF).pow 2).aestronglyMeasurable)
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (fejerSincSq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hF_bd τ) (fejerSincSq_nonneg _)
  have hRHS_pair_int : ∀ m n : ℕ,
      Integrable (fun u : ℝ =>
        (c m * (starRingEnd ℂ) (c n)) *
          ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ)) := by
    intro m n
    exact (Complex.ofRealCLM.integrable_comp (integrable_boxHalfDP_prod _ _)).const_mul _
  have hRHS_box_eq : ∀ u : ℝ,
      ((‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S,
          (c m * (starRingEnd ℂ) (c n)) *
            ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ) := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    have hfil :
        (∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n) =
          ∑ n ∈ S, ((boxHalfDP (u - T * ξ n) : ℝ) : ℂ) * c n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [boxHalfDP]
      split_ifs <;> simp
    rw [hfil, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hRHS_int :
      Integrable (fun u : ℝ =>
        ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2) := by
    have hsum_int :
        Integrable (fun u : ℝ => ∑ m ∈ S, ∑ n ∈ S,
          (c m * (starRingEnd ℂ) (c n)) *
            ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ)) :=
      integrable_finset_sum_dp S _ fun m _ =>
        integrable_finset_sum_dp S _ fun n _ => hRHS_pair_int m n
    have hre := Complex.reCLM.integrable_comp hsum_int
    have hre' : (fun u : ℝ => Complex.reCLM (∑ m ∈ S, ∑ n ∈ S,
          (c m * (starRingEnd ℂ) (c n)) *
            ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ))) =
        fun u : ℝ => ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 := by
      funext u
      change (∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)) *
        ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ)).re = _
      rw [← hRHS_box_eq u, Complex.ofReal_re]
    rwa [hre'] at hre
  have hL1 :
      ((∫ τ : ℝ, fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)) *
          ∫ τ : ℝ, (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
            Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ)) := by
    rw [← integral_ofReal_dp hLHS_int]
    have hrew :
        (∫ τ : ℝ, ((fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 : ℝ) : ℂ)) =
          ∫ τ : ℝ, ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)) *
            ((fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
              Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ))) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      dsimp only
      rw [Complex.ofReal_mul, hnorm_sq τ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hrew, MeasureTheory.integral_finsetSum S (fun m _ =>
      integrable_finset_sum_dp S _ fun n _ => (integrable_fejerSincSq_div_cexp T _ hT).const_mul _)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MeasureTheory.integral_finsetSum S (fun n _ =>
      (integrable_fejerSincSq_div_cexp T _ hT).const_mul _)]
    refine Finset.sum_congr rfl fun n _ => MeasureTheory.integral_const_mul _ _
  have hconv_id : ∀ m n : ℕ,
      ∫ τ : ℝ, (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
          Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ)) =
        ((2 * Real.pi * T : ℝ) : ℂ) *
          ∫ u : ℝ, ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ) := by
    intro m n
    rw [← tentKernel_scale_integral_eq T (ξ n - ξ m) hT,
      tentKernel_eq_conv_boxHalfDP]
    congr 1
    have hshift :
        (∫ u : ℝ, boxHalfDP u * boxHalfDP (u - T * (ξ n - ξ m))) =
          ∫ u : ℝ, boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) := by
      have hsub := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun u : ℝ => boxHalfDP u * boxHalfDP (u - T * (ξ n - ξ m)))
        (T * ξ m)
      rw [← hsub]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      congr 2
      ring
    rw [hshift, integral_ofReal_dp (integrable_boxHalfDP_prod _ _)]
  have hR1 :
      (∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)) *
          ∫ τ : ℝ, (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
            Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ))) =
        (((2 * Real.pi * T) *
          ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 : ℝ) : ℂ) := by
    calc
      (∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)) *
          ∫ τ : ℝ, (fejerSincSq (τ / (2 * Real.pi * T)) : ℂ) *
            Complex.exp (Complex.I * (τ : ℂ) * ((ξ n - ξ m : ℝ) : ℂ)))
          = ((2 * Real.pi * T : ℝ) : ℂ) * ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)) *
              ∫ u : ℝ, ((boxHalfDP (u - T * ξ m) *
                boxHalfDP (u - T * ξ n) : ℝ) : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [hconv_id m n]
            ring
      _ = ((2 * Real.pi * T : ℝ) : ℂ) * ∫ u : ℝ, ∑ m ∈ S, ∑ n ∈ S,
            (c m * (starRingEnd ℂ) (c n)) *
              ((boxHalfDP (u - T * ξ m) * boxHalfDP (u - T * ξ n) : ℝ) : ℂ) := by
            congr 1
            symm
            rw [MeasureTheory.integral_finsetSum S (fun m _ =>
              integrable_finset_sum_dp S _ fun n _ => hRHS_pair_int m n)]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [MeasureTheory.integral_finsetSum S (fun n _ => hRHS_pair_int m n)]
            refine Finset.sum_congr rfl fun n _ => MeasureTheory.integral_const_mul _ _
      _ = ((2 * Real.pi * T : ℝ) : ℂ) *
            ∫ u : ℝ, ((‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 : ℝ) : ℂ) := by
            congr 1
            exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => (hRHS_box_eq u).symm)
      _ = (((2 * Real.pi * T) *
            ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 : ℝ) : ℂ) := by
            rw [integral_ofReal_dp hRHS_int, Complex.ofReal_mul (2 * Real.pi * T)]
  exact Complex.ofReal_injective (hL1.trans hR1)

/-- Gallagher's integral bound for arbitrary real frequencies. Only pairs
lying in a common window of width `1/T` contribute on the right. -/
theorem tent_gallagher_frequency_bound (S : Finset ℕ) (ξ : ℕ → ℝ)
    (c : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ τ in (-T)..T, ‖∑ n ∈ S, c n * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))‖ ^ 2 ≤
      (Real.pi ^ 3 / 2) * T *
        ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 := by
  let F : ℝ → ℂ := fun τ => ∑ n ∈ S, c n * Complex.exp (-(Complex.I * (τ : ℂ) * (ξ n : ℂ)))
  have hcontF : Continuous F := by
    dsimp [F]
    refine continuous_finset_sum_dp S _ fun n hn => continuous_const.mul ?_
    exact Complex.continuous_exp.comp
      (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)
  have hFejer_lb : ∀ τ ∈ Set.Icc (-T) T,
      (2 / Real.pi) ^ 2 ≤ fejerSincSq (τ / (2 * Real.pi * T)) := by
    intro τ hτ
    rw [Set.mem_Icc] at hτ
    by_cases hτ0 : τ = 0
    · subst hτ0
      simp only [zero_div, fejerSincSq, ↓reduceIte]
      have h2pi : 2 ≤ Real.pi := Real.two_le_pi
      have hle : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr h2pi
      nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le]
    · have hdiv_ne : τ / (2 * Real.pi * T) ≠ 0 :=
        div_ne_zero hτ0 (by positivity)
      have harg_le : |τ / (2 * T)| ≤ Real.pi / 2 := by
        rw [abs_div, abs_of_pos (mul_pos two_pos hT)]
        have h1 : |τ| ≤ T := abs_le.mpr hτ
        have h2 : |τ| / (2 * T) ≤ 1 / 2 := (div_le_iff₀ (mul_pos two_pos hT)).mpr (by linarith)
        have h3 : (1 / 2 : ℝ) ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
        exact h2.trans h3
      have hjordan := Real.mul_abs_le_abs_sin harg_le
      have harg_ne : |τ / (2 * T)| ≠ 0 := by
        rw [abs_ne_zero]
        exact div_ne_zero hτ0 (by positivity)
      have hsin_ge : 2 / Real.pi ≤ |Real.sin (τ / (2 * T)) / (τ / (2 * T))| := by
        rw [abs_div, le_div_iff₀ (lt_of_le_of_ne (abs_nonneg _) harg_ne.symm)]
        exact hjordan
      have hpi_eq : Real.pi * (τ / (2 * Real.pi * T)) = τ / (2 * T) := by
        field_simp [Real.pi_ne_zero]
      dsimp [fejerSincSq]
      simp only [hdiv_ne, ↓reduceIte, hpi_eq]
      have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hsin_ge 2
      rwa [sq_abs] at hsq
  have hLHS_int :
      Integrable (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2) := by
    let C₀ : ℝ := (∑ n ∈ S, ‖c n‖) ^ 2
    have hF_bd : ∀ τ : ℝ, ‖F τ‖ ^ 2 ≤ C₀ := by
      intro τ
      have h1 : ‖F τ‖ ≤ ∑ n ∈ S, ‖c n‖ := by
        dsimp [F]
        refine (norm_sum_le S _).trans (Finset.sum_le_sum fun n hn => ?_)
        rw [norm_mul]
        have harg : -(Complex.I * (τ : ℂ) * (ξ n : ℂ)) =
            ((-(τ * ξ n) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hdom : Integrable (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T)) * C₀) :=
      (integrable_fejerSincSq_div T hT).mul_const C₀
    have hmeas : AEStronglyMeasurable
        (fun τ : ℝ => fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2) volume :=
      ((integrable_fejerSincSq_div T hT).aestronglyMeasurable.mul
        ((continuous_norm.comp hcontF).pow 2).aestronglyMeasurable)
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (fejerSincSq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hF_bd τ) (fejerSincSq_nonneg _)
  have hint_Ioc :
      ∫ τ in (-T)..T, ‖F τ‖ ^ 2 = ∫ τ in Set.Ioc (-T) T, ‖F τ‖ ^ 2 :=
    intervalIntegral.integral_of_le (by linarith)
  have hIoc_le :
      ∫ τ in Set.Ioc (-T) T, ‖F τ‖ ^ 2 ≤
        (Real.pi / 2) ^ 2 * ∫ τ in Set.Ioc (-T) T, fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on
      (((continuous_norm.comp hcontF).pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (hLHS_int.integrableOn.const_mul _) measurableSet_Ioc fun τ hτ => ?_
    have hτ_icc : τ ∈ Set.Icc (-T) T := Set.Ioc_subset_Icc_self hτ
    have hlb := hFejer_lb τ hτ_icc
    have h1 : 1 ≤ (Real.pi / 2) ^ 2 * fejerSincSq (τ / (2 * Real.pi * T)) := by
      have hpi2 : (0 : ℝ) < (Real.pi / 2) ^ 2 := by positivity
      calc
        (1 : ℝ) = (Real.pi / 2) ^ 2 * (2 / Real.pi) ^ 2 := by field_simp [Real.pi_ne_zero]
        _ ≤ (Real.pi / 2) ^ 2 * fejerSincSq (τ / (2 * Real.pi * T)) :=
            mul_le_mul_of_nonneg_left hlb hpi2.le
    calc
      ‖F τ‖ ^ 2 = 1 * ‖F τ‖ ^ 2 := (one_mul _).symm
      _ ≤ (Real.pi / 2) ^ 2 * fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (Real.pi / 2) ^ 2 * (fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2) := mul_assoc _ _ _
  have hset_le_univ :
      ∫ τ in Set.Ioc (-T) T, fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 ≤
        ∫ τ : ℝ, fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 :=
    MeasureTheory.setIntegral_le_integral hLHS_int
      (Filter.Eventually.of_forall fun _ => mul_nonneg (fejerSincSq_nonneg _) (sq_nonneg _))
  calc
    ∫ τ in (-T)..T, ‖F τ‖ ^ 2
        = ∫ τ in Set.Ioc (-T) T, ‖F τ‖ ^ 2 := hint_Ioc
    _ ≤ (Real.pi / 2) ^ 2 *
          ∫ τ in Set.Ioc (-T) T, fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 := hIoc_le
    _ ≤ (Real.pi / 2) ^ 2 * ∫ τ : ℝ, fejerSincSq (τ / (2 * Real.pi * T)) * ‖F τ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hset_le_univ (by positivity)
    _ = (Real.pi / 2) ^ 2 * ((2 * Real.pi * T) *
          ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2) := by
        rw [tent_integral_identity_frequencies S ξ c hT]
    _ = (Real.pi ^ 3 / 2) * T *
          ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * ξ n| ≤ 1 / 2), c n‖ ^ 2 := by
        ring

/-- **Gallagher's Integral Mean-Value Bound for Dirichlet Polynomials**:
for any finite set `S ⊆ [1, ∞)`, complex coefficients `c`, and `T > 0`,
`∫ t in (-T)..T, ‖∑ n ∈ S, c n * n^(-I * t)‖^2 ≤ (π^3 / 2) * T * ∫ u : ℝ, ‖∑_{n ∈ S, |u - T log n| ≤ 1/2} c n‖^2`. -/
theorem tent_gallagher_integral_bound (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ τ in (-T)..T, ‖∑ n ∈ S, c n * (n : ℂ) ^ (-(Complex.I * (τ : ℂ)))‖ ^ 2 ≤
      (Real.pi ^ 3 / 2) * T *
        ∫ u : ℝ, ‖∑ n ∈ S.filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2), c n‖ ^ 2 := by
  have hcpow : ∀ (n : ℕ) (τ : ℝ), 1 ≤ n →
      (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) =
        Complex.exp (-(Complex.I * (τ : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
    intro n τ hn
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hne : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]
    congr 1; ring
  apply le_trans _ (tent_gallagher_frequency_bound S (fun n => Real.log n) c hT)
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro τ _
  have hsum := Finset.sum_congr (s₁:=S) (s₂:=S) rfl
    (fun n hn => congrArg (fun z => c n*z) (hcpow n τ (hS n hn)))
  exact congrArg (fun z : ℂ => ‖z‖^2) hsum

private theorem real_exp_sub_one_le_two_mul_dp {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Real.exp θ - 1 ≤ 2 * θ := by
  have hz : ‖(θ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg h0]
    exact h1
  have hbd := Complex.norm_exp_sub_one_sub_id_le hz
  have hre : |Real.exp θ - 1 - θ| ≤ θ ^ 2 := by
    have hre1 : |((Complex.exp (θ : ℂ) - 1 - (θ : ℂ)).re)| ≤
        ‖Complex.exp (θ : ℂ) - 1 - (θ : ℂ)‖ := Complex.abs_re_le_norm _
    have hre2 : (Complex.exp (θ : ℂ) - 1 - (θ : ℂ)).re = Real.exp θ - 1 - θ := by
      rw [Complex.sub_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        ← Complex.ofReal_exp, Complex.ofReal_re]
    have hsq : ‖(θ : ℂ)‖ ^ 2 = θ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hre2] at hre1
    rw [hsq] at hbd
    exact hre1.trans hbd
  have hle : Real.exp θ - 1 - θ ≤ θ ^ 2 := (abs_le.mp hre).2
  have hsq : θ ^ 2 ≤ θ := by nlinarith
  linarith

set_option maxHeartbeats 1800000 in
/-- **Hybrid Large Sieve Inequality on `[1, N]`**:
for any `N, Q : ℕ`, `0 < T`, and `a : ℕ → ℂ`,
`∑ q ∈ Icc 1 Q, (q / φ(q)) ∑^*_{χ mod q} ∫_{-T}^T ‖∑_{n=1}^N a n * χ n * n^{-it}‖^2 dt ≤ π^3 * (N + Q^2 * T) * ∑_{n=1}^N ‖a n‖^2`. -/
theorem hybrid_large_sieve (a : ℕ → ℂ) (N Q : ℕ) {T : ℝ} (hT : 0 < T) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (Nat.totient q : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ∫ t in (-T)..T,
              ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  by_cases hQ0 : Q = 0
  · subst hQ0; simp
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ0
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    nlinarith
  have hS1 : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  by_cases hT1 : T ≤ 1
  · have hpt : ∀ t : ℝ,
        ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
          ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      intro t
      let at_t : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))
      have hcls := character_large_sieve_dirichlet_Icc at_t N Q
      have heq_sum :
          ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 =
            ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Icc 1 N, at_t n * χ n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun χ _ => ?_
        have hinner :
            (∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
              ∑ n ∈ Finset.Icc 1 N, at_t n * χ n :=
          Finset.sum_congr rfl fun n _ => by dsimp [at_t]; ring
        rw [hinner]
      have hnorm_at : ∑ n ∈ Finset.Icc 1 N, ‖at_t n‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        dsimp [at_t]
        have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hne : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
        have hcpow : (n : ℂ) ^ (-(Complex.I * (t : ℂ))) =
            Complex.exp ((-(t * Real.log (n : ℝ)) : ℝ) * Complex.I) := by
          rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]
          congr 1; push_cast; ring
        rw [norm_mul, hcpow, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [heq_sum]
      exact hcls.trans_eq (by rw [hnorm_at])
    have hint_chi : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        IntervalIntegrable (fun t : ℝ =>
          ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
          volume (-T) T := by
      intro q χ
      refine Continuous.intervalIntegrable ?_ _ _
      refine (continuous_norm.comp (continuous_finset_sum_dp _ _ fun n hn =>
        continuous_const.mul ?_)).pow 2
      have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hne : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
      have hfn : (fun t : ℝ => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
          fun t : ℝ => Complex.exp (-(Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
        funext t
        rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]
        congr 1; ring
      rw [hfn]
      exact Complex.continuous_exp.comp
        (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)
    have hsum_int :
        ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ∫ t in (-T)..T,
                  ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 =
          ∫ t in (-T)..T,
            ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [intervalIntegral.integral_const_mul]
        congr 1
        exact (intervalIntegral.integral_finsetSum fun χ _ => hint_chi q χ).symm
      · intro q _
        exact (intervalIntegrable_finset_sum_dp _ _ fun χ _ => hint_chi q χ).const_mul _
    have hLHS_int :
        IntervalIntegrable (fun t : ℝ =>
          ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
          volume (-T) T :=
      intervalIntegrable_finset_sum_dp _ _ fun q _ =>
        (intervalIntegrable_finset_sum_dp _ _ fun χ _ => hint_chi q χ).const_mul _
    have hbd_int :
        ∫ t in (-T)..T,
            ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
          ∫ _t in (-T)..T, ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) hLHS_int intervalIntegrable_const
        fun t _ => hpt t
    rw [intervalIntegral.integral_const, smul_eq_mul] at hbd_int
    have h2pi3 : (2 : ℝ) ≤ Real.pi ^ 3 := by
      have h2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      calc
        (2 : ℝ) ≤ 2 ^ 3 := by norm_num
        _ ≤ Real.pi ^ 3 := by gcongr
    have hsum_nn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [hsum_int]
    refine hbd_int.trans ?_
    have hcoef : (T - -T) * ((N : ℝ) + (Q : ℝ) ^ 2) ≤ Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
      have hlen : T - -T = 2 * T := by ring
      rw [hlen]
      have h1 : 2 * T * ((N : ℝ) + (Q : ℝ) ^ 2) ≤ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
        nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ N)]
      have h2 : 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) ≤ Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) :=
        mul_le_mul_of_nonneg_right h2pi3 (by positivity)
      exact h1.trans h2
    calc
      (T - -T) * (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
          = ((T - -T) * ((N : ℝ) + (Q : ℝ) ^ 2)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring
      _ ≤ (Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hsum_nn
  · have h1T : 1 ≤ T := le_of_not_ge hT1
    have hstep1 :
        ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ∫ t in (-T)..T,
                  ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
          (Real.pi ^ 3 / 2) * T *
            ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ∫ u : ℝ,
                    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                      a n * χ n‖ ^ 2 := by
      have h1 : ∀ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ∫ t in (-T)..T,
                ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ((Real.pi ^ 3 / 2) * T *
                ∫ u : ℝ,
                  ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                    a n * χ n‖ ^ 2) := by
        intro q _
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) (by positivity)
        exact tent_gallagher_integral_bound (Finset.Icc 1 N) hS1 (fun n => a n * χ n) hT
      refine (Finset.sum_le_sum h1).trans_eq ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.mul_sum]
      ring_nf
    have hint_u : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        Integrable (fun u : ℝ =>
          ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2), a n * χ n‖ ^ 2) := by
      intro q χ
      have heqC : ∀ u : ℝ,
          ((‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
            a n * χ n‖ ^ 2 : ℝ) : ℂ) =
            ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (a m * χ m * (starRingEnd ℂ) (a n * χ n)) *
                ((boxHalfDP (u - T * Real.log (m : ℝ)) * boxHalfDP (u - T * Real.log (n : ℝ)) : ℝ) : ℂ) := by
        intro u
        rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
        have hfil :
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2), a n * χ n) =
              ∑ n ∈ Finset.Icc 1 N, ((boxHalfDP (u - T * Real.log (n : ℝ)) : ℝ) : ℂ) * (a n * χ n) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          dsimp [boxHalfDP]
          split_ifs <;> simp
        rw [hfil, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
        ring
      have hsum_int :
          Integrable (fun u : ℝ => ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (a m * χ m * (starRingEnd ℂ) (a n * χ n)) *
              ((boxHalfDP (u - T * Real.log (m : ℝ)) * boxHalfDP (u - T * Real.log (n : ℝ)) : ℝ) : ℂ)) :=
        integrable_finset_sum_dp _ _ fun m _ =>
          integrable_finset_sum_dp _ _ fun n _ =>
            (Complex.ofRealCLM.integrable_comp (integrable_boxHalfDP_prod _ _)).const_mul _
      have hre := Complex.reCLM.integrable_comp hsum_int
      have hre' : (fun u : ℝ => Complex.reCLM (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (a m * χ m * (starRingEnd ℂ) (a n * χ n)) *
              ((boxHalfDP (u - T * Real.log (m : ℝ)) * boxHalfDP (u - T * Real.log (n : ℝ)) : ℝ) : ℂ))) =
          fun u : ℝ =>
            ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2), a n * χ n‖ ^ 2 := by
        funext u
        change (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (a m * χ m * (starRingEnd ℂ) (a n * χ n)) *
            ((boxHalfDP (u - T * Real.log (m : ℝ)) * boxHalfDP (u - T * Real.log (n : ℝ)) : ℝ) : ℂ)).re = _
        rw [← heqC u, Complex.ofReal_re]
      rwa [hre'] at hre
    have hsum_swap :
        ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ∫ u : ℝ,
                  ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                    a n * χ n‖ ^ 2 =
          ∫ u : ℝ,
            ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                    a n * χ n‖ ^ 2 := by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact (MeasureTheory.integral_finsetSum _ fun χ _ => hint_u q χ).symm
      · intro q _
        exact (integrable_finset_sum_dp _ _ fun χ _ => hint_u q χ).const_mul _
    have hpt_u : ∀ u : ℝ,
        ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                  a n * χ n‖ ^ 2 ≤
          ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) *
            ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * boxHalfDP (u - T * Real.log (n : ℝ)) := by
      intro u
      let x_u : ℝ := Real.exp ((u - 1 / 2) / T)
      have hx_pos : 0 < x_u := Real.exp_pos _
      let M_u : ℕ := Nat.ceil x_u - 1
      let K_u : ℕ := Nat.floor (2 * (N : ℝ) / T) + 1
      have hM_succ : M_u + 1 = Nat.ceil x_u :=
        Nat.sub_add_cancel (Nat.ceil_pos.mpr hx_pos)
      let au : ℕ → ℂ := fun n =>
        if n ∈ Finset.Icc 1 N ∧ |u - T * Real.log (n : ℝ)| ≤ 1 / 2 then a n else 0
      by_cases hne :
          ((Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2)).Nonempty
      · obtain ⟨n₀, hn₀⟩ := hne
        rw [Finset.mem_filter, Finset.mem_Icc] at hn₀
        have hx_le_n₀ : x_u ≤ (n₀ : ℝ) := by
          have h1 : (u - 1 / 2) / T ≤ Real.log (n₀ : ℝ) :=
            (div_le_iff₀ hT).mpr (by linarith [(abs_le.mp hn₀.2).2])
          simpa only [x_u, Real.exp_log (by exact_mod_cast hn₀.1.1 : (0 : ℝ) < n₀)] using
            Real.exp_le_exp.mpr h1
        have hx_le_N : x_u ≤ (N : ℝ) :=
          hx_le_n₀.trans (by exact_mod_cast hn₀.1.2)
        have hsub :
            (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2) ⊆
              Finset.Ioc M_u (M_u + K_u) := by
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1.1
          have hlo : x_u ≤ (n : ℝ) := by
            have h1 : (u - 1 / 2) / T ≤ Real.log (n : ℝ) :=
              (div_le_iff₀ hT).mpr (by linarith [(abs_le.mp hn.2).2])
            simpa only [x_u, Real.exp_log hn_pos] using Real.exp_le_exp.mpr h1
          have hceil_le : Nat.ceil x_u ≤ n := Nat.ceil_le.mpr hlo
          have hM_lt : M_u < n := by omega
          have hhi : (n : ℝ) ≤ x_u * Real.exp (1 / T) := by
            have h1 : Real.log (n : ℝ) ≤ (u + 1 / 2) / T :=
              (le_div_iff₀ hT).mpr (by linarith [(abs_le.mp hn.2).1])
            calc
              (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hn_pos).symm
              _ ≤ Real.exp ((u + 1 / 2) / T) := Real.exp_le_exp.mpr h1
              _ = Real.exp ((u - 1 / 2) / T + 1 / T) := by congr 1; ring
              _ = x_u * Real.exp (1 / T) := Real.exp_add _ _
          have hexp_bd : Real.exp (1 / T) - 1 ≤ 2 / T := by
            have h0 : 0 ≤ 1 / T := by positivity
            have h1 : 1 / T ≤ 1 := (div_le_one hT).mpr h1T
            simpa only [div_eq_mul_inv, one_mul] using real_exp_sub_one_le_two_mul_dp h0 h1
          have hn_lt_real : (n : ℝ) < ((M_u + K_u + 1 : ℕ) : ℝ) := by
            have hx_ceil : x_u ≤ ((M_u + 1 : ℕ) : ℝ) := by
              rw [hM_succ]; exact Nat.le_ceil x_u
            have hfl : 2 * (N : ℝ) / T < (K_u : ℝ) := by
              dsimp [K_u]; push_cast; exact Nat.lt_floor_add_one _
            calc
              (n : ℝ) ≤ x_u + x_u * (Real.exp (1 / T) - 1) := by linarith
              _ ≤ x_u + (N : ℝ) * (2 / T) := by
                  refine add_le_add_right ?_ _
                  have hnn : 0 ≤ Real.exp (1 / T) - 1 := by
                    linarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 1 / T)]
                  exact mul_le_mul hx_le_N hexp_bd hnn (by positivity)
              _ < ((M_u + 1 : ℕ) : ℝ) + (K_u : ℝ) := by
                  have h2N : (N : ℝ) * (2 / T) = 2 * (N : ℝ) / T := by ring
                  rw [h2N]; linarith
              _ = ((M_u + K_u + 1 : ℕ) : ℝ) := by push_cast; ring
          have hn_lt : n < M_u + K_u + 1 := by exact_mod_cast hn_lt_real
          exact Finset.mem_Ioc.mpr ⟨hM_lt, by omega⟩
        have hcls := character_large_sieve_dirichlet au M_u K_u Q
        have heq_sum :
            ∑ q ∈ Finset.Icc 1 Q,
                ((q : ℝ) / (Nat.totient q : ℝ)) *
                  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                      (fun χ => χ.IsPrimitive),
                    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                      a n * χ n‖ ^ 2 =
              ∑ q ∈ Finset.Icc 1 Q,
                ((q : ℝ) / (Nat.totient q : ℝ)) *
                  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                      (fun χ => χ.IsPrimitive),
                    ‖∑ n ∈ Finset.Ioc M_u (M_u + K_u), au n * χ n‖ ^ 2 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          have hinner :
              (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                a n * χ n) =
                ∑ n ∈ Finset.Ioc M_u (M_u + K_u), au n * χ n := by
            rw [← Finset.sum_subset hsub ?_]
            · refine Finset.sum_congr rfl fun n hn => ?_
              have hn' := Finset.mem_filter.mp hn
              simp only [au, hn'.1, hn'.2, and_self, ↓reduceIte]
            · intro n _ hnot
              rw [Finset.mem_filter] at hnot
              dsimp [au]
              simp only [hnot, ↓reduceIte, zero_mul]
          rw [hinner]
        have heq_norm :
            ∑ n ∈ Finset.Ioc M_u (M_u + K_u), ‖au n‖ ^ 2 ≤
              ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * boxHalfDP (u - T * Real.log (n : ℝ)) := by
          have h1 :
              ∑ n ∈ Finset.Ioc M_u (M_u + K_u), ‖au n‖ ^ 2 =
                ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                  ‖a n‖ ^ 2 := by
            rw [← Finset.sum_subset hsub ?_]
            · refine Finset.sum_congr rfl fun n hn => ?_
              rw [Finset.mem_filter] at hn
              dsimp [au]
              simp only [hn.1, hn.2, and_self, ↓reduceIte]
            · intro n _ hnot
              rw [Finset.mem_filter] at hnot
              dsimp [au]
              simp only [if_neg hnot, norm_zero, zero_pow (by decide : 2 ≠ 0)]
          rw [h1, Finset.sum_filter]
          refine Finset.sum_le_sum fun n _ => ?_
          dsimp [boxHalfDP]
          split_ifs <;> simp
        have hK_le : (K_u : ℝ) ≤ 2 * (N : ℝ) / T + 1 := by
          dsimp [K_u]; push_cast
          linarith [Nat.floor_le (by positivity : 0 ≤ 2 * (N : ℝ) / T)]
        rw [heq_sum]
        calc
          ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Ioc M_u (M_u + K_u), au n * χ n‖ ^ 2
              ≤ ((K_u : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M_u (M_u + K_u), ‖au n‖ ^ 2 := hcls
          _ ≤ ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) *
                ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * boxHalfDP (u - T * Real.log (n : ℝ)) :=
              mul_le_mul (add_le_add_left hK_le _) heq_norm
                (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp only [hne, Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => ?_)
        refine mul_nonneg (sq_nonneg _) ?_
        dsimp [boxHalfDP]; split_ifs <;> norm_num
    have hRHS_u_int :
        Integrable (fun u : ℝ =>
          ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) *
            ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * boxHalfDP (u - T * Real.log (n : ℝ))) := by
      refine (integrable_finset_sum_dp _ _ fun n _ => ?_).const_mul _
      exact (integrable_boxHalfDP_sub _).const_mul _
    have hLHS_u_int :
        Integrable (fun u : ℝ =>
          ∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (Nat.totient q : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ => χ.IsPrimitive),
                ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                  a n * χ n‖ ^ 2) :=
      integrable_finset_sum_dp _ _ fun q _ =>
        (integrable_finset_sum_dp _ _ fun χ _ => hint_u q χ).const_mul _
    have hint_le :
        ∫ u : ℝ,
            ∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (Nat.totient q : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                    (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                    a n * χ n‖ ^ 2 ≤
          ∫ u : ℝ,
            ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) *
              ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * boxHalfDP (u - T * Real.log (n : ℝ)) :=
      MeasureTheory.integral_mono hLHS_u_int hRHS_u_int hpt_u
    have hRHS_val :
        ∫ u : ℝ,
            ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) *
              ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * boxHalfDP (u - T * Real.log (n : ℝ)) =
          ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [MeasureTheory.integral_const_mul]
        have hbox1 : ∫ u : ℝ, boxHalfDP (u - T * Real.log (n : ℝ)) = 1 := by
          rw [boxHalfDP_eq_indicator, MeasureTheory.integral_indicator measurableSet_Icc,
            MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_one]
          rw [max_eq_left (by linarith)]
          ring
        rw [hbox1, mul_one]
      · exact fun n _ => (integrable_boxHalfDP_sub _).const_mul _
    rw [hRHS_val] at hint_le
    calc
      ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ∫ t in (-T)..T,
                ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
          ≤ (Real.pi ^ 3 / 2) * T *
              ∫ u : ℝ,
                ∑ q ∈ Finset.Icc 1 Q,
                  ((q : ℝ) / (Nat.totient q : ℝ)) *
                    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                        (fun χ => χ.IsPrimitive),
                      ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => |u - T * Real.log (n : ℝ)| ≤ 1 / 2),
                        a n * χ n‖ ^ 2 := by
            rw [← hsum_swap]
            exact hstep1
      _ ≤ (Real.pi ^ 3 / 2) * T *
            (((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hint_le (by positivity)
      _ ≤ Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
          have hsum_nn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          have hcoef : (Real.pi ^ 3 / 2) * T * ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) ≤
              Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
            have hTmul : T * ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) =
                2 * (N : ℝ) + T * (1 + (Q : ℝ) ^ 2) := by
              field_simp [hT.ne'] <;> ring
            have hTle : T * (1 + (Q : ℝ) ^ 2) ≤ 2 * ((Q : ℝ) ^ 2 * T) := by
              nlinarith [mul_le_mul_of_nonneg_left hQ1R hT.le]
            calc
              _ = (Real.pi ^ 3 / 2) * (2 * (N : ℝ) + T * (1 + (Q : ℝ) ^ 2)) := by
                rw [← hTmul]; ring
              _ ≤ (Real.pi ^ 3 / 2) * (2 * (N : ℝ) + 2 * ((Q : ℝ) ^ 2 * T)) := by gcongr
              _ = _ := by ring
          calc
            (Real.pi ^ 3 / 2) * T *
                  (((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
                = ((Real.pi ^ 3 / 2) * T * ((2 * (N : ℝ) / T + 1) + (Q : ℝ) ^ 2)) *
                    ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring
            _ ≤ (Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T)) *
                  ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef hsum_nn

set_option maxHeartbeats 1800000 in
/-- **Hybrid Large Sieve Inequality on `(M, M + N]`**:
for any `M N Q : ℕ`, `0 < T`, and `a : ℕ → ℂ`,
`∑ q ∈ Icc 1 Q, (q / φ(q)) ∑^*_{χ mod q} ∫_{-T}^T ‖∑_{n ∈ (M, M+N]} a n * χ n * n^{-it}‖^2 dt ≤ π^3 * (M + N + Q^2 * T) * ∑_{n ∈ (M, M+N]} ‖a n‖^2`. -/
theorem hybrid_large_sieve_Ioc (a : ℕ → ℂ) (M N Q : ℕ) {T : ℝ} (hT : 0 < T) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (Nat.totient q : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ∫ t in (-T)..T,
              ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 3 * ((M : ℝ) + (N : ℝ) + (Q : ℝ) ^ 2 * T) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  let a' : ℕ → ℂ := fun n => if M < n then a n else 0
  have hsub : Finset.Ioc M (M + N) ⊆ Finset.Icc 1 (M + N) := by
    intro n hn; rw [Finset.mem_Ioc] at hn; exact Finset.mem_Icc.mpr ⟨by omega, hn.2⟩
  have heq_sum :
      ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ∫ t in (-T)..T,
                ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 =
        ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ∫ t in (-T)..T,
                ‖∑ n ∈ Finset.Icc 1 (M + N), a' n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      dsimp [a']
      simp only [hn.1, ↓reduceIte]
    · intro n hn hnot
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_Ioc] at hnot
      have hle : ¬ M < n := fun hlt => hnot ⟨hlt, hn.2⟩
      dsimp [a']
      simp [hle]
  have heq_norm :
      ∑ n ∈ Finset.Icc 1 (M + N), ‖a' n‖ ^ 2 = ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
    symm
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      dsimp [a']
      simp only [hn.1, ↓reduceIte]
    · intro n hn hnot
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_Ioc] at hnot
      have hle : ¬ M < n := fun hlt => hnot ⟨hlt, hn.2⟩
      dsimp [a']
      simp [hle]
  rw [heq_sum]
  have hmain := hybrid_large_sieve a' (M + N) Q hT
  rwa [heq_norm, Nat.cast_add] at hmain

/-- **Unweighted Hybrid Large Sieve Inequality on `[1, N]`**:
dropping the weight `q / φ(q) ≥ 1`,
`∑ q ∈ Icc 1 Q, ∑^*_{χ mod q} ∫_{-T}^T ‖∑_{n=1}^N a n * χ n * n^{-it}‖^2 dt ≤ π^3 * (N + Q^2 * T) * ∑_{n=1}^N ‖a n‖^2`. -/
theorem hybrid_large_sieve_unweighted (a : ℕ → ℂ) (N Q : ℕ) {T : ℝ} (hT : 0 < T) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
            (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T,
            ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
      Real.pi ^ 3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h1 :
      ∑ q ∈ Finset.Icc 1 Q,
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
              (fun χ => χ.IsPrimitive),
            ∫ t in (-T)..T,
              ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                (fun χ => χ.IsPrimitive),
              ∫ t in (-T)..T,
                ‖∑ n ∈ Finset.Icc 1 N, a n * χ n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2 := by
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_pos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq_pos
    have hphi_le : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hge1 : (1 : ℝ) ≤ (q : ℝ) / (Nat.totient q : ℝ) := (one_le_div hphi_pos).mpr hphi_le
    refine le_mul_of_one_le_left (Finset.sum_nonneg fun χ _ => ?_) hge1
    exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  exact h1.trans (hybrid_large_sieve a N Q hT)

end HybridLargeSieve

end

end AnalyticNumberTheory.SieveMethods
