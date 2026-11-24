import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.LocalZeroMass
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.TuranLargeValues

/-!
# Detection of a zero by a high derivative of a logarithmic derivative

The real part of the first reciprocal-zero sum bounds the square mass of the
scaled reciprocal zeros. Turán detection then detects a nearby zero by an
order proportional to this mass.
-/

noncomputable section

open Complex Metric Finset
open scoped Classical

namespace AnalyticNumberTheory.AnalyticTools.ComplexAnalysis

/-- Local analytic zero detector. Here `B` bounds the logarithmic derivative at
the center and `D` bounds the analytic remainder in terms of the disk growth.
The order parameter costs `η(B+D)` rather than the unscaled local zero count. -/
theorem local_logDeriv_turan_detector {f : ℂ → ℂ} {c ρ : ℂ} {η G B D : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/1024) (hc : c.re = 1+η)
    (hf : AnalyticOnNhd ℂ f (closedBall c (3/4))) (hn : ∀ u : ℂ, 1 ≤ u.re → f u ≠ 0)
    (hG : 0 < G) (hg : ∀ w ∈ sphere c (3/4), ‖f w/f c‖ ≤ G)
    (hD : 0 ≤ D) (hDG : 352*Real.log G ≤ D) (hB : ‖logDeriv f c‖ ≤ B)
    (hρ : f ρ = 0) (hd : ‖c-ρ‖ ≤ 2*η)
    {M : ℕ} (hM : 16*256^2*(η*(B+D)+1) ≤ (M:ℝ)) :
    ∃ k ∈ Ioc M (2*M), (1/64:ℝ)^k ≤ η^k * ‖signedTaylorCoeff (logDeriv f) c (k-1)‖ := by
  have hcn : f c ≠ 0 := hn _ (by linarith)
  have hB₀ := (norm_nonneg _).trans hB
  have hH : 0 ≤ η*(B+D) := by positivity
  obtain ⟨Z,hZ,hsum,he⟩ := exists_local_scaled_inverse_square_mass hη hc hf hn hG hg hDG hB
  let m (u : ℂ) := analyticOrderNatAt f u
  let v (u : ℂ) := (η:ℂ)*(c-u)⁻¹
  have hzero {u : ℂ} (hu : u ∈ Z) : u ∈ closedBall c (3/8) ∧ f u = 0 := by
    apply mem_zeroSet.mp; rw [←hZ]; exact hu
  have hρ' : ρ ∈ closedBall c (3/8) := by
    rw [mem_closedBall,Complex.dist_eq,norm_sub_rev]; linarith
  have hρZ : ρ ∈ Z := by change ρ ∈ (Z:Set ℂ); rw [hZ]; exact ⟨hρ',hρ⟩
  have hmρ : 1 ≤ m ρ := by
    have hf' := hf.mono (closedBall_subset_closedBall (by norm_num : (3/8:ℝ) ≤ 3/4))
    have ht := analyticOrderAt_ne_top_of_closedBall (by norm_num) hf' hcn hρ'
    apply Nat.pos_of_ne_zero
    intro hh
    change analyticOrderNatAt f ρ = 0 at hh
    apply (hf' ρ hρ').analyticOrderAt_ne_zero.mpr hρ
    rw [←Nat.cast_analyticOrderNatAt ht,hh]; rfl
  have hnrm (u : ℂ) : ‖v u‖ = η/‖c-u‖ := by
    rw [show v u = _ from rfl,norm_mul,Complex.norm_real,Real.norm_of_nonneg hη.le,norm_inv,div_eq_mul_inv]
  have hsep {u : ℂ} (hu : u ∈ Z) : η ≤ (c-u).re := by
    have hlt : u.re < 1 := lt_of_not_ge fun h => hn _ h (hzero hu).2
    rw [sub_re,hc]; linarith
  have hdist {u : ℂ} (hu : u ∈ Z) : 0 < ‖c-u‖ := hη.trans_le ((hsep hu).trans (re_le_norm _))
  have hbig : 1/2 ≤ ‖v ρ‖ := by rw [hnrm,le_div_iff₀ (hdist hρZ)]; linarith
  let A (k : ℕ) := (η:ℂ)^k*signedTaylorCoeff (logDeriv f) c (k-1)
  have hscale (k : ℕ) (hk : 1 ≤ k) :
      ‖A k - ∑ u ∈ Z, (m u:ℂ)*v u^k‖ ≤ (η*(B+D))*(1/256:ℝ)^(k-1) := by
    have heq : A k - ∑ u ∈ Z, (m u:ℂ)*v u^k =
        (η:ℂ)^k * (signedTaylorCoeff (logDeriv f) c (k-1) -
         ∑ u ∈ Z, (m u:ℂ)*(c-u)⁻¹^k) := by
      rw [mul_sub,mul_sum]
      apply congrArg₂ Sub.sub rfl
      apply sum_congr rfl; intro u _
      dsimp only [v]; rw [mul_pow]; ring
    rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hη.le]
    have h := he (k-1)
    rw [Nat.sub_add_cancel hk] at h
    apply (mul_le_mul_of_nonneg_left h (pow_nonneg hη.le k)).trans
    calc
      η^k*(352*Real.log G*(16/5:ℝ)^(k-1)) =
          (η*(352*Real.log G))*(η*(16/5:ℝ))^(k-1) := by
        rw [mul_pow,show η^k = η^(k-1)*η by rw [←pow_succ]; congr 1; omega]; ring
      _ ≤ η*D*(η*(16/5:ℝ))^(k-1) := by gcongr
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : D ≤ B+D) hη.le)
        (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)
  obtain ⟨k,hk,hh⟩ := turan_detection_of_square_mass Z m v hρZ hmρ hbig hH hsum hM A hscale
  refine ⟨k,hk,?_⟩
  simpa only [A,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hη.le] using hh

end AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
