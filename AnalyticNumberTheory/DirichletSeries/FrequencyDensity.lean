import AnalyticNumberTheory.DirichletSeries.FrequencyConvergence

/-! # Absolute convergence and the density of a Dirichlet frequency -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable (F : DirichletFrequency)

/-- Absolute convergence of the general Dirichlet series at a complex argument. -/
def AbsConvergesAt (a : ℕ → ℂ) (s : ℂ) : Prop :=
  Summable fun n => a n * Complex.exp (-s * F n)

/-- The abscissa of absolute convergence of a general Dirichlet series. -/
def absoluteAbscissa (a : ℕ → ℂ) : EReal :=
  sInf (Real.toEReal '' {x : ℝ | F.AbsConvergesAt a x})

theorem absConvergesAt_iff {a : ℕ → ℂ} {s : ℂ} : F.AbsConvergesAt a s ↔
    Summable (fun n => ‖a n‖ * Real.exp (-s.re * F n)) := by
  unfold AbsConvergesAt
  rw [← summable_norm_iff]
  simp [Complex.norm_exp, Complex.mul_re]

variable {F}

theorem AbsConvergesAt.of_re_le {a : ℕ → ℂ} {s w : ℂ} (h : F.AbsConvergesAt a s) (hw : s.re ≤ w.re) :
    F.AbsConvergesAt a w := by
  rw [F.absConvergesAt_iff] at h ⊢
  apply h.of_nonneg_of_le (fun n => by positivity)
  intro n
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hw) (F.nonneg n))) (norm_nonneg _)

theorem AbsConvergesAt.convergesAt {a : ℕ → ℂ} {s : ℂ} (h : F.AbsConvergesAt a s) :
    F.ConvergesAt a s :=
  ⟨_,h.hasSum.tendsto_sum_nat⟩

theorem AbsConvergesAt.sum_eq_tsum {a : ℕ → ℂ} {s : ℂ} (h : F.AbsConvergesAt a s) :
    F.sum a s = ∑' n, a n * Complex.exp (-s * F n) :=
  tendsto_nhds_unique h.convergesAt.tendsto h.hasSum.tendsto_sum_nat

theorem absoluteAbscissa_le_re {a : ℕ → ℂ} {s : ℂ} (h : F.AbsConvergesAt a s) :
    F.absoluteAbscissa a ≤ (s.re : EReal) :=
  sInf_le ⟨s.re, h.of_re_le (by simp), rfl⟩

theorem absConvergesAt_of_absoluteAbscissa_lt {a : ℕ → ℂ} {s : ℂ} (h : F.absoluteAbscissa a < (s.re : EReal)) :
    F.AbsConvergesAt a s := by
  rw [absoluteAbscissa, sInf_lt_iff] at h
  obtain ⟨_,⟨x,hx,rfl⟩,hlt⟩ := h
  exact hx.of_re_le (EReal.coe_lt_coe_iff.mp hlt).le

theorem abscissa_le_absoluteAbscissa (F : DirichletFrequency) (a : ℕ → ℂ) :
    F.abscissa a ≤ F.absoluteAbscissa a := by
  apply le_sInf
  rintro _ ⟨σ,hσ,rfl⟩
  exact abscissa_le_re (s := (σ : ℂ)) hσ.convergesAt

theorem logarithmic_absConvergesAt (a : ℕ → ℂ) (s : ℂ) :
    logarithmic.AbsConvergesAt (fun n => a (n+1)) s ↔ LSeriesSummable a s := by
  have hterm (n : ℕ) : a (n+1) * Complex.exp (-s * logarithmic n) = LSeries.term a s (n+1) := by
    have h := logarithmic_partialSum a s (n+1)
    rw [partialSum_succ, dirichletPartialSum_succ, logarithmic_partialSum] at h
    exact add_left_cancel h
  simpa only [AbsConvergesAt, hterm, LSeriesSummable] using (summable_nat_add_iff (f := LSeries.term a s) 1)

theorem logarithmic_absoluteAbscissa (a : ℕ → ℂ) :
    logarithmic.absoluteAbscissa (fun n => a (n+1)) = LSeries.abscissaOfAbsConv a := by
  simp only [absoluteAbscissa, LSeries.abscissaOfAbsConv, logarithmic_absConvergesAt]

/-- Upper exponential density of the frequencies. The index shift counts all
frequencies through the current term. A zero initial frequency has no effect
on the limit superior. -/
def exponentDensity (F : DirichletFrequency) : EReal :=
  limsup (fun n => ((Real.log ((n+1 : ℕ) : ℝ) / F n : ℝ) : EReal)) atTop

theorem exponentDensity_nonneg (F : DirichletFrequency) : 0 ≤ F.exponentDensity := by
  refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  exact Eventually.frequently (.of_forall fun n => EReal.coe_nonneg.mpr
    (div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_pos n)) (F.nonneg n)))

/-- Above the upper exponential density, the unweighted exponentials are summable. -/
theorem summable_exp_of_exponentDensity_lt {d : ℝ} (hd : F.exponentDensity < (d : EReal)) :
    Summable (fun n => Real.exp (-d * F n)) := by
  obtain ⟨β,hβ,hβd⟩ := EReal.exists_between_coe_real hd
  have hβ₀ : 0 < β := EReal.coe_pos.mp (F.exponentDensity_nonneg.trans_lt hβ)
  have hd' : β < d := EReal.coe_lt_coe_iff.mp hβd
  let p := d/β
  have hp : 1 < p := (one_lt_div hβ₀).mpr hd'
  have hs : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ) ^ (-p)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  apply hs.of_norm_bounded_eventually_nat
  have he : ∀ᶠ n in atTop, ((Real.log ((n+1 : ℕ) : ℝ) / F n : ℝ) : EReal) < (β : EReal) :=
    eventually_lt_of_limsup_lt hβ
  filter_upwards [he, F.tendsto_atTop.eventually_gt_atTop 0] with n hn hn₀
  have hlog := (div_lt_iff₀ hn₀).mp (EReal.coe_lt_coe_iff.mp hn)
  have hpβ : p*β = d := div_mul_cancel₀ d hβ₀.ne'
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  have H := mul_le_mul_of_nonneg_left hlog.le (by linarith : 0 ≤ p)
  rw [← mul_assoc, hpβ] at H
  linarith

/-- Ordered convergence at one point gives absolute convergence at every
displacement with real part greater than the frequency density. -/
theorem ConvergesAt.absConvergesAt_of_density_lt {a : ℕ → ℂ} {s₀ s : ℂ} (h : F.ConvergesAt a s₀)
    (hd : F.exponentDensity < ((s.re-s₀.re : ℝ) : EReal)) : F.AbsConvergesAt a s := by
  obtain ⟨C,hC⟩ := h.tendsto.norm.bddAbove_range
  have H (n : ℕ) : ‖a n * Complex.exp (-s₀ * F n)‖ ≤ C+C := by
    have hterm : a n * Complex.exp (-s₀ * F n) = F.partialSum a s₀ (n+1) - F.partialSum a s₀ n := by
      rw [partialSum_succ]; abel
    rw [hterm]
    exact (norm_sub_le _ _).trans (add_le_add (hC ⟨_,rfl⟩) (hC ⟨_,rfl⟩))
  apply ((summable_exp_of_exponentDensity_lt hd).mul_left (C+C)).of_norm_bounded
  intro n
  have hnorm (w : ℂ) : ‖a n * Complex.exp (-w * F n)‖ = ‖a n‖ * Real.exp (-w.re * F n) := by
    simp [Complex.norm_exp,Complex.mul_re]
  calc
    _ = (‖a n * Complex.exp (-s₀ * F n)‖) * Real.exp (-(s.re-s₀.re)*F n) := by
      rw [hnorm,hnorm,mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (H n) (Real.exp_pos _).le

/-- The gap between absolute and ordered convergence is at most the upper
exponential density. The extended-real statement also covers series converging
everywhere or nowhere, for every finite density bound `D`. -/
theorem absoluteAbscissa_le_abscissa_add {D : ℝ} (hD : F.exponentDensity ≤ (D : EReal)) (a : ℕ → ℂ) :
    F.absoluteAbscissa a ≤ F.abscissa a + (D : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro t ht
  have ht' : F.abscissa a < ((t-D : ℝ) : EReal) := by
    induction hx : F.abscissa a using EReal.rec with
    | bot => exact EReal.bot_lt_coe _
    | top => simp [hx] at ht
    | coe r =>
      rw [hx, ← EReal.coe_add, EReal.coe_lt_coe_iff] at ht
      exact EReal.coe_lt_coe_iff.mpr (lt_sub_iff_add_lt.mpr ht)
  obtain ⟨σ,hσ,hσt⟩ := exists_real_of_abscissa_lt ht'
  have hd : F.exponentDensity < ((t-σ : ℝ) : EReal) :=
    hD.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  exact absoluteAbscissa_le_re (s := (t : ℂ)) (hσ.absConvergesAt_of_density_lt hd)

/-- The ordinary Dirichlet frequency has density one. -/
@[simp] theorem logarithmic_exponentDensity : logarithmic.exponentDensity = 1 := by
  have h : (fun n : ℕ => ((Real.log ((n+1 : ℕ) : ℝ) / logarithmic n : ℝ) : EReal)) =ᶠ[atTop] fun _ => 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have ht : 1 < ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < n+1 by omega)
    change ((Real.log ((n+1 : ℕ) : ℝ) / Real.log ((n+1 : ℕ) : ℝ) : ℝ) : EReal) = 1
    rw [div_self (Real.log_pos ht).ne', EReal.coe_one]
  rw [exponentDensity, limsup_congr h, limsup_const]

/-- With positive integer frequencies the series is a power series in `exp(-s)`. -/
def positiveIntegers : DirichletFrequency where
  exponent n := ((n+1 : ℕ) : ℝ)
  nonneg_zero := by positivity
  strictMono := by
    intro m n h
    change ((m+1 : ℕ) : ℝ) < ((n+1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_lt_succ h
  tendsto_atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

@[simp] theorem positiveIntegers_exponentDensity : positiveIntegers.exponentDensity = 0 := by
  have h : Tendsto (fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp positiveIntegers.tendsto_atTop
  have he := (continuous_coe_real_ereal.tendsto 0).comp h
  simpa only [exponentDensity, positiveIntegers, Function.comp_def, EReal.coe_zero] using he.limsup_eq

/-- For a power series in `exp(-s)`, absolute and ordered convergence have
the same abscissa, including either infinite value. -/
theorem positiveIntegers_absoluteAbscissa_eq (a : ℕ → ℂ) :
    positiveIntegers.absoluteAbscissa a = positiveIntegers.abscissa a := by
  have H := absoluteAbscissa_le_abscissa_add (F := positiveIntegers) (D := 0) (by simp) a
  exact le_antisymm (by simpa using H) (positiveIntegers.abscissa_le_absoluteAbscissa a)

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
