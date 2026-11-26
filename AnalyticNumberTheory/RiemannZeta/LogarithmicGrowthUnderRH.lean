import AnalyticNumberTheory.RiemannZeta.EulerLogBounds
import AnalyticNumberTheory.RiemannZeta.LogarithmUnderRH

/-!
# Logarithmic growth of the Euler branch under the Riemann hypothesis

Borel–Carathéodory controls the outer circle by the real part of the logarithm.
Hadamard interpolation from a circle inside the Euler-product half-plane then gives
a logarithmic power varying with the real part of the evaluation point.
-/

noncomputable section

open Complex Set
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

namespace AnalyticNumberTheory.RiemannZeta

private theorem disk_coordinates {z w : ℂ} {R : ℝ} (hw : w ∈ Metric.ball z R) :
    z.re - R < w.re ∧ |z.im| - R < |w.im| ∧ |w.im| < |z.im| + R := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hx := (Complex.abs_re_le_norm (w-z)).trans_lt hw
  have hy := (Complex.abs_im_le_norm (w-z)).trans_lt hw
  simp only [Complex.sub_re, Complex.sub_im] at hx hy
  have hrev := abs_sub_abs_le_abs_sub z.im w.im
  rw [abs_sub_comm z.im w.im] at hrev
  exact ⟨by linarith [(abs_lt.mp hx).1], by linarith, by linarith [abs_sub_abs_le_abs_sub w.im z.im]⟩

/-- The Euler branch is holomorphic on every disk strictly to the right of the critical
line whose radius is smaller than the absolute height of its center. -/
theorem differentiableOn_slitLogZeta_ball (hRH : RiemannHypothesisProp) {z : ℂ} {R : ℝ}
    (hleft : 1/2 < z.re-R) (hheight : R < |z.im|) :
    DifferentiableOn ℂ (slitLogZeta hRH) (Metric.ball z R) := by
  intro w hw
  obtain ⟨hx,hy,_⟩ := disk_coordinates hw
  apply (hasDerivAt_slitLogZeta hRH (hleft.trans hx) ?_).differentiableAt.differentiableWithinAt
  exact mem_slitPlane_iff.mpr (.inr (by simpa using (abs_pos.mp (by linarith : 0 < |w.im|))))

private theorem log_height_ge_one {t : ℝ} (ht : 2 ≤ |t|) : 1 ≤ Real.log (|t|+2) := by
  have h : Real.exp 1 ≤ |t|+2 := Real.exp_one_lt_d9.le.trans (by linarith)
  simpa using Real.log_le_log (Real.exp_pos 1) h

/-- On disks with fixed radii in the zero-free half-plane, the Euler-normalized
logarithm grows at most logarithmically in the height of the center. -/
theorem norm_slitLogZeta_on_closedBall (hRH : RiemannHypothesisProp) {c r R : ℝ}
    (hc : 1 < c) (hr : 0 ≤ r) (hrR : r < R) (hleft : 1/2 < c-R) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t : ℝ), R+4 ≤ |t| →
      ∀ w ∈ Metric.closedBall (⟨c,t⟩ : ℂ) r, ‖slitLogZeta hRH w‖ ≤ B * Real.log (|t|+2) := by
  obtain ⟨C,hC,H⟩ := riemannZeta_and_inv_bounds_of_riemannHypothesisProp hRH hleft (ε := 1) one_pos
  let K := max 1 (2*C)
  let A := Real.log K + 1
  let M := max 1 (Real.log ‖riemannZeta (c : ℂ)‖)
  let p := 2*r/(R-r)
  let q := (R+r)/(R-r)
  have hR := hr.trans_lt hrR
  have hK : 1 ≤ K := le_max_left _ _
  have hlogK := Real.log_nonneg hK
  have hM : 1 ≤ M := le_max_left _ _
  have hp : 0 ≤ p := div_nonneg (by positivity) (sub_pos.mpr hrR).le
  have hq : 0 ≤ q := div_nonneg (by linarith) (sub_pos.mpr hrR).le
  have hA : 0 ≤ A := by dsimp [A]; linarith
  refine ⟨1+p*A+q*M, by nlinarith [mul_nonneg hp hA, mul_nonneg hq (zero_le_one.trans hM)], ?_⟩
  intro t ht w hw
  let z : ℂ := ⟨c,t⟩
  let L := Real.log (|t|+2)
  have hL : 1 ≤ L := log_height_ge_one (by linarith)
  have hdiff := differentiableOn_slitLogZeta_ball hRH (z := z) hleft (by change R < |t|; linarith)
  have hre (v : ℂ) (hv : v ∈ Metric.ball z R) : (slitLogZeta hRH v).re ≤ A*L := by
    obtain ⟨hx,hy,hy'⟩ := disk_coordinates hv
    change c-R < v.re at hx
    change |t|-R < |v.im| at hy
    change |v.im| < |t|+R at hy'
    have him : 4 ≤ |v.im| := by linarith
    have hv1 : v ≠ 1 := by rintro rfl; norm_num at him
    have hval := (H hx.le him).1
    rw [Complex.re_add_im, Real.rpow_one] at hval
    have hzero := riemannHypothesisProp_iff_ne_zero_of_half_lt_re.mp hRH v (hleft.trans hx)
    have hbound : ‖riemannZeta v‖ ≤ K*(|t|+2) := calc
      _ ≤ C*(|v.im|+2) := hval
      _ ≤ C*(2*(|t|+2)) := mul_le_mul_of_nonneg_left (by linarith) hC.le
      _ = (2*C)*(|t|+2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hreal : (slitLogZeta hRH v).re = Real.log ‖riemannZeta v‖ := by
      rw [← exp_slitLogZeta hRH (hleft.trans hx) hv1, Complex.norm_exp, Real.log_exp]
    rw [hreal]
    calc
      _ ≤ Real.log (K*(|t|+2)) := Real.log_le_log (norm_pos_iff.mpr hzero) hbound
      _ = Real.log K + L := Real.log_mul (zero_lt_one.trans_le hK).ne' (by positivity)
      _ ≤ A*L := by dsimp only [A]; nlinarith [mul_le_mul_of_nonneg_left hL hlogK]
  have hcenter : ‖slitLogZeta hRH z‖ ≤ M := by
    rw [slitLogZeta_eq_logZeta hRH (show 1 < z.re from hc)]
    exact (norm_logZeta_le_log_norm_riemannZeta hc (le_refl c)).trans (le_max_right _ _)
  have hbc := borel_caratheodory_on_closedBall hr hrR (mul_nonneg hA (zero_le_one.trans hL)) hdiff hre hw
  change ‖slitLogZeta hRH w‖ ≤ p*(A*L)+q*‖slitLogZeta hRH z‖ at hbc
  calc
    _ ≤ p*(A*L)+q*M := hbc.trans (by gcongr)
    _ ≤ (1+p*A+q*M)*L := by nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg hq (zero_le_one.trans hM))]

/-- Upper estimate for the three-circles interpolation exponent with outer radius r+1/2. -/
private theorem three_circles_exponent_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    Real.log ((r+a)/r) / Real.log ((r+1/2)/r) ≤ 2*a + a/r := by
  have hr' : 0 < r + 1/2 := by linarith
  have hden : 0 < Real.log ((r+1/2)/r) := Real.log_pos ((one_lt_div hr).mpr (by linarith))
  have hnum : Real.log ((r+a)/r) ≤ a/r := calc
    _ ≤ (r+a)/r-1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) hr)
    _ = _ := by field_simp; ring
  have hlow : (1/2)/(r+1/2) ≤ Real.log ((r+1/2)/r) := calc
    _ = 1-((r+1/2)/r)⁻¹ := by field_simp; ring
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (div_pos hr' hr)
  rw [div_le_iff₀ hden]
  calc
    _ ≤ a/r := hnum
    _ = (2*a+a/r)*((1/2)/(r+1/2)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

private theorem log_power_bound_large_height (hRH : RiemannHypothesisProp) {σ₀ ε : ℝ}
    (hσ₀ : 1/2 < σ₀) (hε : 0 < ε) :
    ∃ D T : ℝ, 0 < D ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 → T ≤ |s.im| →
      ‖slitLogZeta hRH s‖ ≤ D * (Real.log (|s.im|+2)) ^ (2-2*s.re+ε) := by
  let δ := min ((σ₀-1/2)/2) (min (ε/8) (1/4))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by positivity) (by norm_num))
  have hδσ : δ ≤ (σ₀-1/2)/2 := min_le_left _ _
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₁ : δ ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  let r := 1+2/ε
  let c := r+(1+δ)
  let R := r+1/2+δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : r+1/2 < R := by dsimp [R]; linarith
  have hleft : 1/2 < c-R := by dsimp only [c,R]; linarith
  have hc : 1 < c := by dsimp only [c]; linarith
  obtain ⟨B,hB,H⟩ := norm_slitLogZeta_on_closedBall hRH hc
    (r := r+1/2) (by linarith) hR hleft
  let D := max B (Real.log ‖riemannZeta ((1+δ : ℝ) : ℂ)‖)
  have hD : 0 < D := hB.trans_le (le_max_left _ _)
  refine ⟨D,R+4,hD,?_⟩
  intro s hs₀ hs₁ ht
  let z : ℂ := ⟨c,s.im⟩
  let a := 1+δ-s.re
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha₁ : a ≤ 1 := by dsimp [a]; linarith
  have hnorm : ‖s-z‖ = r+a := by
    have he : s-z = ((s.re-c : ℝ) : ℂ) := by apply Complex.ext <;> simp [z]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    dsimp only [a,c]
    ring
  let L := Real.log (|s.im|+2)
  have hL : 1 ≤ L := log_height_ge_one (by linarith)
  have hdiff := differentiableOn_slitLogZeta_ball hRH (z := z) hleft (by change R < |s.im|; linarith)
  have hinner (v : ℂ) (hv : v ∈ Metric.sphere z r) : ‖slitLogZeta hRH v‖ ≤ D := by
    rw [Metric.mem_sphere, dist_eq_norm] at hv
    have hx := Complex.abs_re_le_norm (v-z)
    rw [Complex.sub_re,hv] at hx
    change |v.re-c| ≤ r at hx
    have hx' := (abs_le.mp hx).1
    have hv' : 1+δ ≤ v.re := by dsimp only [c] at hx'; linarith
    rw [slitLogZeta_eq_logZeta hRH (by linarith)]
    exact (norm_logZeta_le_log_norm_riemannZeta (by linarith : 1 < 1+δ) hv').trans (le_max_right _ _)
  have houter (v : ℂ) (hv : v ∈ Metric.sphere z (r+1/2)) : ‖slitLogZeta hRH v‖ ≤ D*L :=
    (H s.im ht v (Metric.sphere_subset_closedBall hv)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hL))
  let θ := Real.log ((r+a)/r) / Real.log ((r+1/2)/r)
  have hinterp : ‖slitLogZeta hRH s‖ ≤ D^(1-θ) * (D*L)^θ := by
    have hs := hadamard_three_circles_annulus hr (by linarith : r < r+1/2) hR hD
      (mul_pos hD (zero_lt_one.trans_le hL)) hdiff hinner houter (w := s)
      (by rw [hnorm]; linarith) (by rw [hnorm]; dsimp only [a]; linarith)
    simpa only [hnorm] using hs
  have haε : a/r ≤ ε/2 := by
    rw [div_le_iff₀ hr]
    calc
      _ ≤ 1 := ha₁
      _ ≤ ε/2*r := by dsimp only [r]; field_simp; nlinarith
  have hθ : θ ≤ 2-2*s.re+ε := by
    apply (three_circles_exponent_le hr ha).trans
    dsimp only [a] at *
    linarith
  calc
    _ ≤ D^(1-θ) * (D*L)^θ := hinterp
    _ = D * L^θ := by
      rw [Real.mul_rpow hD.le (zero_le_one.trans hL), ← mul_assoc, ← Real.rpow_add hD,
        sub_add_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hθ) hD.le

/-- Under RH, the Euler-normalized logarithm satisfies the uniform Littlewood bound
with exponent 2−2 Re s+ε, for every Re s in [σ₀,1] and every |Im s| ≥ 2. -/
theorem norm_slitLogZeta_le_log_rpow (hRH : RiemannHypothesisProp) {σ₀ ε : ℝ}
    (hσ₀ : 1/2 < σ₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 → 2 ≤ |s.im| →
      ‖slitLogZeta hRH s‖ ≤ C * (Real.log |s.im|) ^ (2-2*s.re+ε) := by
  obtain ⟨D,T,hD,H⟩ := log_power_bound_large_height hRH hσ₀ hε
  let K : Set ℂ := (Icc σ₀ 1 ×ℂ Icc (-T) T) ∩ {s : ℂ | 2 ≤ |s.im|}
  have hcpt : IsCompact K := (isCompact_Icc.reProdIm isCompact_Icc).inter_right
    (isClosed_le continuous_const Complex.continuous_im.abs)
  have hcont : ContinuousOn (slitLogZeta hRH) K := by
    intro s hs
    have him : 2 ≤ |s.im| := hs.2
    apply (hasDerivAt_slitLogZeta hRH (hσ₀.trans_le hs.1.1.1) ?_).continuousAt.continuousWithinAt
    exact mem_slitPlane_iff.mpr (.inr (by simpa using (abs_pos.mp (by linarith : 0 < |s.im|))))
  obtain ⟨M,hM⟩ := hcpt.exists_bound_of_continuousOn hcont
  let B := max D M
  have hB : 0 < B := hD.trans_le (le_max_left _ _)
  refine ⟨B*2^(1+ε), mul_pos hB (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro s hs₀ hs₁ ht
  let p := 2-2*s.re+ε
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp' : p ≤ 1+ε := by dsimp [p]; linarith
  have hL := log_height_ge_one ht
  have hfirst : ‖slitLogZeta hRH s‖ ≤ B * (Real.log (|s.im|+2))^p := by
    rcases le_or_gt T |s.im| with htT | htT
    · exact (H s hs₀ hs₁ htT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (zero_le_one.trans hL) _))
    · have hsK : s ∈ K := ⟨⟨⟨hs₀,hs₁⟩,abs_le.mp htT.le⟩,ht⟩
      exact ((hM s hsK).trans (le_max_right _ _)).trans
        (le_mul_of_one_le_right hB.le (Real.one_le_rpow hL hp))
  have hlog : Real.log (|s.im|+2) ≤ 2 * Real.log |s.im| := by
    have hsq : |s.im|+2 ≤ |s.im|^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (by positivity : 0 ≤ |s.im|+1)]
    simpa [Real.log_pow] using Real.log_le_log (by positivity) hsq
  have hbase : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
  calc
    _ ≤ B * (Real.log (|s.im|+2))^p := hfirst
    _ ≤ B * (2*Real.log |s.im|)^p := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (zero_le_one.trans hL) hlog hp) hB.le
    _ = (B*2^p)*(Real.log |s.im|)^p := by rw [Real.mul_rpow zero_le_two hbase, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two hp') hB.le)
      (Real.rpow_nonneg hbase _)

/-- On each closed substrip to the right of the critical line, the logarithm is
uniformly o(log |Im s|) as the absolute height tends to infinity. -/
theorem norm_slitLogZeta_le_mul_log_of_large_height (hRH : RiemannHypothesisProp) {σ₀ η : ℝ}
    (hσ₀ : 1/2 < σ₀) (hη : 0 < η) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 → T ≤ |s.im| →
      ‖slitLogZeta hRH s‖ ≤ η * Real.log |s.im| := by
  let δ := σ₀-1/2
  have hδ : 0 < δ := sub_pos.mpr hσ₀
  obtain ⟨C,hC,H⟩ := norm_slitLogZeta_le_log_rpow hRH hσ₀ hδ
  obtain ⟨U,hU⟩ := Filter.tendsto_atTop_atTop.mp
    ((tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop) (C/η)
  refine ⟨max 4 U, (by linarith [le_max_left 4 U]), ?_⟩
  intro s hs₀ hs₁ ht
  have ht₄ : 4 ≤ |s.im| := (le_max_left _ _).trans ht
  let L := Real.log |s.im|
  have hL : 1 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by linarith : _ ≤ |s.im|))
    simpa [L] using h
  have hLpos := zero_lt_one.trans_le hL
  have hCη : C ≤ η*L^δ := by
    have h := hU |s.im| ((le_max_right _ _).trans ht)
    exact (div_le_iff₀ hη).mp h |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ C*L^(2-2*s.re+δ) := H s hs₀ hs₁ (by linarith)
    _ ≤ C*L^(1-δ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by dsimp only [δ]; linarith)) hC.le
    _ ≤ (η*L^δ)*L^(1-δ) := mul_le_mul_of_nonneg_right hCη (Real.rpow_nonneg hLpos.le _)
    _ = η*L := by rw [mul_assoc, ← Real.rpow_add hLpos, show δ+(1-δ) = 1 by ring, Real.rpow_one]

/-- Both ζ and its reciprocal are eventually bounded by the pure power |Im s|^η,
uniformly on each substrip σ₀ ≤ Re s ≤ 1 with σ₀ > 1/2. -/
theorem norm_riemannZeta_and_inv_le_rpow_of_large_height (hRH : RiemannHypothesisProp) {σ₀ η : ℝ}
    (hσ₀ : 1/2 < σ₀) (hη : 0 < η) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 → T ≤ |s.im| →
      ‖riemannZeta s‖ ≤ |s.im|^η ∧ ‖(riemannZeta s)⁻¹‖ ≤ |s.im|^η := by
  obtain ⟨T,hT,H⟩ := norm_slitLogZeta_le_mul_log_of_large_height hRH hσ₀ hη
  refine ⟨T,hT,fun s hs₀ hs₁ ht => ?_⟩
  have him : 0 < |s.im| := by linarith
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at him
  have hr := (Complex.abs_re_le_norm (slitLogZeta hRH s)).trans (H s hs₀ hs₁ ht)
  rw [← exp_slitLogZeta hRH (hσ₀.trans_le hs₀) hs1, ← Complex.exp_neg, Complex.norm_exp,
    Complex.norm_exp, Complex.neg_re, Real.rpow_def_of_pos him, mul_comm (Real.log |s.im|)]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hr).2, Real.exp_le_exp.mpr (by linarith [(abs_le.mp hr).1])⟩

end AnalyticNumberTheory.RiemannZeta
