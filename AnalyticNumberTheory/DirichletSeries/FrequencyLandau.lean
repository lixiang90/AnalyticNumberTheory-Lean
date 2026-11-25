import AnalyticNumberTheory.DirichletSeries.FrequencyPositive
import Mathlib.Analysis.Complex.TaylorSeries

/-! # Landau's singularity theorem for general Dirichlet series -/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace AnalyticNumberTheory.DirichletSeries.DirichletFrequency

variable {F : DirichletFrequency} {a : ℕ → ℝ}

private lemma absConvergesAt_of_taylor {x c : ℝ} {G : ℂ → ℂ} (ha : ∀ n, 0 ≤ a n) (hx : x ≤ c)
    (hc : F.abscissa (fun n => (a n : ℂ)) < (c : EReal))
    (hnear : G =ᶠ[𝓝 (c : ℂ)] F.sum (fun n => (a n : ℂ)))
    (hT : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ • ((x : ℂ)-c)^k • iteratedDeriv k G c) (G x)) :
    F.AbsConvergesAt (fun n => (a n : ℂ)) (x : ℂ) := by
  let b := F.taylorMoment a c x
  have hp (k n : ℕ) : 0 ≤ b k n := taylorMoment_nonneg ha hx k n
  have hrow (k : ℕ) := hasSum_taylorMoment_frequency ha hx hc k
  have hrowval (k : ℕ) : (∑' n, b k n) =
      ((k.factorial : ℂ)⁻¹ • ((x : ℂ)-c)^k • iteratedDeriv k G c).re := by
    rw [hnear.iteratedDeriv_eq, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    exact (hrow k).tsum_eq
  have hs : Summable (fun k => ∑' n, b k n) :=
    (Complex.reCLM.hasSum hT).summable.congr (fun k => (hrowval k).symm)
  have htotal : Summable (fun p : ℕ × ℕ => b p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => hp p.1 p.2)).mpr ⟨fun k => (hrow k).summable,hs⟩
  have hcol := ((summable_prod_of_nonneg (f := fun p : ℕ × ℕ => b p.2 p.1)
    (fun p => hp p.2 p.1)).mp htotal.prod_symm).2
  have hweight : Summable (fun n => a n * Real.exp (-x*F n)) :=
    hcol.congr fun n => (F.hasSum_taylorMoment_degree a c x n).tsum_eq
  simpa only [F.absConvergesAt_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha _),ofReal_re] using hweight

private lemma agrees_near_real {G L : ℂ → ℂ} {σ r c : ℝ}
    (hball : (c : ℂ) ∈ ball (σ : ℂ) r) (hσ : σ < c)
    (heq : ∀ z ∈ ball (σ : ℂ) r, σ < z.re → G z = L z) :
    G =ᶠ[𝓝 (c : ℂ)] L := by
  have hU : IsOpen (ball (σ : ℂ) r ∩ {z : ℂ | σ < z.re}) := isOpen_ball.inter (Complex.isOpen_re_gt σ)
  have hc : (c : ℂ) ∈ ball (σ : ℂ) r ∩ {z : ℂ | σ < z.re} := ⟨hball,hσ⟩
  filter_upwards [hU.mem_nhds hc] with z hz using heq z hz.1 hz.2

/-- **Landau's theorem for general Dirichlet series.** A holomorphic continuation
to a disk of radius `r` at a real boundary `σ` forces the absolute abscissa of
a series with nonnegative coefficients to be at most `σ - r`. -/
theorem landau_absoluteAbscissa_le {σ r : ℝ} {G : ℂ → ℂ} (ha : ∀ n, 0 ≤ a n) (hr : 0 < r)
    (hσ : F.abscissa (fun n => (a n : ℂ)) ≤ (σ : EReal)) (hG : DifferentiableOn ℂ G (ball (σ : ℂ) r))
    (heq : ∀ z ∈ ball (σ : ℂ) r, σ < z.re → G z = F.sum (fun n => (a n : ℂ)) z) :
    F.absoluteAbscissa (fun n => (a n : ℂ)) ≤ ((σ-r : ℝ) : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro x hx
  have hx' : σ-r < x := EReal.coe_lt_coe_iff.mp hx
  by_cases hright : σ < x
  · exact (absoluteAbscissa_eq_of_nonneg (F := F) ha).le.trans
      (hσ.trans (EReal.coe_le_coe_iff.mpr hright.le))
  have hxs : x ≤ σ := le_of_not_gt hright
  let δ := (x-(σ-r))/4
  let c := σ+δ
  let R := r-δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r := by dsimp [δ]; linarith
  have hsc : σ < c := lt_add_of_pos_right _ hδ
  have hxc : x < c := hxs.trans_lt hsc
  have hdist : dist (c : ℂ) (σ : ℂ) = δ := by
    rw [dist_eq_norm, ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      show c-σ=δ by dsimp [c]; ring, abs_of_pos hδ]
  have hcball : (c : ℂ) ∈ ball (σ : ℂ) r := by simpa only [mem_ball,hdist] using hδr
  have hsub : ball (c : ℂ) R ⊆ ball (σ : ℂ) r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc
      dist z (σ : ℂ) ≤ dist z (c : ℂ) + dist (c : ℂ) (σ : ℂ) := dist_triangle _ _ _
      _ < r := by rw [hdist]; dsimp [R] at hz; linarith
  have hxball : (x : ℂ) ∈ ball (c : ℂ) R := by
    rw [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hxc)]
    dsimp [R,c,δ]
    linarith
  have hconv := absConvergesAt_of_taylor ha hxc.le (hσ.trans_lt (EReal.coe_lt_coe_iff.mpr hsc))
    (agrees_near_real hcball hsc heq) (Complex.hasSum_taylorSeries_on_ball (hG.mono hsub) hxball)
  exact absoluteAbscissa_le_re (s := (x : ℂ)) hconv

/-- Under Landau's hypotheses the sum itself agrees with the proposed
continuation throughout the open disk. -/
theorem landau_eqOn_ball {σ r : ℝ} {G : ℂ → ℂ} (ha : ∀ n, 0 ≤ a n) (hr : 0 < r)
    (hσ : F.abscissa (fun n => (a n : ℂ)) ≤ (σ : EReal)) (hG : DifferentiableOn ℂ G (ball (σ : ℂ) r))
    (heq : ∀ z ∈ ball (σ : ℂ) r, σ < z.re → G z = F.sum (fun n => (a n : ℂ)) z) :
    (ball (σ : ℂ) r).EqOn G (F.sum (fun n => (a n : ℂ))) := by
  have H := landau_absoluteAbscissa_le ha hr hσ hG heq
  have hsub : ball (σ : ℂ) r ⊆ {z : ℂ | F.abscissa (fun n => (a n : ℂ)) < (z.re : EReal)} := by
    intro z hz
    rw [mem_ball,dist_eq_norm] at hz
    have hdiff := abs_lt.mp ((Complex.abs_re_le_norm (z-(σ : ℂ))).trans_lt hz)
    simp only [Complex.sub_re,Complex.ofReal_re] at hdiff
    exact ((F.abscissa_le_absoluteAbscissa _).trans H).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  have hL := (F.analyticOnNhd_sum _).mono hsub
  let c := σ+r/2
  have hsc : σ < c := by dsimp [c]; linarith
  have hc : (c : ℂ) ∈ ball (σ : ℂ) r := by
    rw [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hsc)]
    dsimp [c]
    linarith
  exact (hG.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq hL
    (convex_ball (σ : ℂ) r).isPreconnected hc (agrees_near_real hc hsc heq)

/-- The real point of a finite convergence abscissa is a singularity. The
obstruction is expressed for every proposed holomorphic extension from the right. -/
theorem no_continuation_at_abscissa {σ r : ℝ} {G : ℂ → ℂ} (ha : ∀ n, 0 ≤ a n) (hr : 0 < r)
    (hσ : F.abscissa (fun n => (a n : ℂ)) = (σ : EReal)) (hG : DifferentiableOn ℂ G (ball (σ : ℂ) r)) :
    ¬ (∀ z ∈ ball (σ : ℂ) r, σ < z.re → G z = F.sum (fun n => (a n : ℂ)) z) := by
  intro heq
  have H := landau_absoluteAbscissa_le ha hr hσ.le hG heq
  rw [absoluteAbscissa_eq_of_nonneg ha,hσ] at H
  have := EReal.coe_le_coe_iff.mp H
  linarith

end AnalyticNumberTheory.DirichletSeries.DirichletFrequency
