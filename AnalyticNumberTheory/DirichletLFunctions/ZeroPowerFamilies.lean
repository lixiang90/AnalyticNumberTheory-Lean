import AnalyticNumberTheory.DirichletLFunctions.LogDerivativePowerSums
import AnalyticNumberTheory.AnalyticTools.ComplexAnalysis.PowerSumDetection

/-!
# Finite zero families for Dirichlet logarithmic derivatives

Local zeros are enumerated with one index for each multiplicity. Scaling their
reciprocals by 1/4 places them in the closed unit disk. All estimates are
uniform in the modulus, the height and the order of differentiation.
-/

noncomputable section
open Complex Filter Metric Finset Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

abbrev ZeroPowerIndex := (u : ℂ) × ℕ

def zeroPowerPoint (c : ℂ) (i : ZeroPowerIndex) : ℂ := (c-i.1)⁻¹/4

/-- A finite list of zeros in a 3/8-radius disk, enumerated with multiplicity.
The real-part error decays geometrically, uniformly in the order k. -/
structure ZeroPowerBounds (f : ℂ → ℂ) (c : ℂ) (H : ℝ) (S : Finset ZeroPowerIndex) : Prop where
  norm_le : ∀ i ∈ S, ‖zeroPowerPoint c i‖ ≤ 1
  mem_of_zero : ∀ {u : ℂ}, u ∈ closedBall c (3/8) → f u = 0 → (⟨u,0⟩ : ZeroPowerIndex) ∈ S
  card_le : (S.card:ℝ) ≤ H
  sum_le : ∀ k : ℕ, (∑ i ∈ S,(zeroPowerPoint c i^(k+1)).re) ≤
    (signedTaylorCoeff (logDeriv f) c k).re/(4:ℝ)^(k+1) + H*(4/5:ℝ)^k

theorem ZeroPowerBounds.mono {f c H H' S} (h : ZeroPowerBounds f c H S) (h' : H ≤ H') :
    ZeroPowerBounds f c H' S where
  norm_le := h.norm_le
  mem_of_zero := h.mem_of_zero
  card_le := h.card_le.trans h'
  sum_le k := (h.sum_le k).trans (by gcongr)

theorem scaled_zero_power_bounds {f : ℂ → ℂ} {c : ℂ} {M H : ℝ} (hM : 0<M)
    (hc : c.re = 5/4) (hf : AnalyticOnNhd ℂ f (closedBall c (3/4)))
    (hn : ∀ u : ℂ, 1≤u.re → f u≠0) (hb : ∀ u ∈ sphere c (3/4), ‖f u/f c‖ ≤ M)
    (hcount : Real.log M / Real.log 2 ≤ H) (herr : 88*Real.log M ≤ H) :
    ∃ S, ZeroPowerBounds f c H S := by
  classical
  have hcn : f c ≠ 0 := hn c (by rw [hc]; norm_num)
  obtain ⟨Z,hZ,hcard,hs⟩ := local_logDeriv_power_sum hM hf hcn hb
  let S : Finset ZeroPowerIndex := Z.sigma (fun u => range (analyticOrderNatAt f u))
  refine ⟨S,⟨?_,?_,?_,?_⟩⟩
  · intro i hi
    have hu : i.1∈zeroSet f c (3/8) := by rw [←hZ]; exact (mem_sigma.mp hi).1
    have hlt : i.1.re<1 := lt_of_not_ge (fun h => hn _ h hu.2)
    have hnorm : 1/4≤‖c-i.1‖ := by
      have := Complex.re_le_norm (c-i.1)
      rw [Complex.sub_re,hc] at this; linarith
    simp only [zeroPowerPoint,norm_div,norm_inv,Complex.norm_ofNat]
    rw [div_le_one (by norm_num),inv_eq_one_div,div_le_iff₀ (by linarith)]; linarith
  · intro u hu hz
    have hu' : u∈Z := by change u∈(Z:Set ℂ); rw [hZ]; exact ⟨hu,hz⟩
    apply mem_sigma.mpr; refine ⟨hu',mem_range.mpr (Nat.pos_of_ne_zero ?_)⟩
    have hf' : AnalyticOnNhd ℂ f (closedBall c (3/8)) := hf.mono (closedBall_subset_closedBall (by norm_num))
    have ht := analyticOrderAt_ne_top_of_closedBall (by norm_num) hf' hcn hu
    intro h
    apply (hf' u hu).analyticOrderAt_ne_zero.mpr hz
    rw [←Nat.cast_analyticOrderNatAt ht,h]; rfl
  · simpa [S,Finset.card_sigma] using hcard.trans hcount
  · intro k
    let A := ∑ u ∈ Z,(analyticOrderNatAt f u:ℂ)*(c-u)⁻¹^(k+1)
    let T := signedTaylorCoeff (logDeriv f) c k
    have hA : A.re-T.re ≤ 352*Real.log M*(16/5:ℝ)^k := by
      calc
        _ = (A-T).re := by simp
        _ ≤ ‖A-T‖ := Complex.re_le_norm _
        _ ≤ _ := by rw [norm_sub_rev]; exact hs k
    have heq : (∑ i ∈ S,(zeroPowerPoint c i^(k+1)).re) = A.re/(4:ℝ)^(k+1) := by
      simp only [S,Finset.sum_sigma,zeroPowerPoint,div_pow,sum_const,card_range,nsmul_eq_mul]
      simp only [A,Complex.re_sum,sum_div,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
        zero_mul,sub_zero]
      apply sum_congr rfl; intro u _
      rw [show (4:ℂ)^(k+1)=((4:ℝ)^(k+1):ℝ) by push_cast; rfl,Complex.div_ofReal_re]; ring
    rw [heq]
    have hp : (0:ℝ)<4^(k+1) := by positivity
    calc
      _ ≤ T.re/(4:ℝ)^(k+1) + (352*Real.log M*(16/5:ℝ)^k)/(4:ℝ)^(k+1) := by
        rw [←add_div]; exact div_le_div_of_nonneg_right (by linarith) hp.le
      _ = T.re/(4:ℝ)^(k+1) + (88*Real.log M)*(4/5:ℝ)^k := by
        rw [show (16/5:ℝ) = (4/5)*4 by norm_num,mul_pow,pow_succ (4:ℝ)]
        field_simp
        ring
      _ ≤ _ := by gcongr

/-- Uniform zero-family estimates for a nonprincipal character at height t. -/
theorem exists_LFunction_zero_power_bounds {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (t : ℝ) :
    ∃ S, ZeroPowerBounds (DirichletCharacter.LFunction χ) (5/4+t*I)
      (1056*Real.log ((q:ℝ)*(|t|+2))) S := by
  let c : ℂ := 5/4+t*I
  let Q := (q:ℝ)*(|t|+2)
  have hc : c.re=5/4 := by simp [c]
  have hci : c.im=t := by simp [c]
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hQ : 2≤Q := by dsimp [Q]; nlinarith [abs_nonneg t,mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hlog : Real.log (1024*Q^2) ≤ 12*Real.log Q := by
    rw [Real.log_mul (by norm_num) (by positivity),show (1024:ℝ)=2^10 by norm_num,Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_log (by norm_num) hQ]
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (3/4)) :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  apply scaled_zero_power_bounds (M:=1024*Q^2) (by positivity) hc hf
    (fun u hu => LFunction_ne_zero_on_re_one χ hu (.inl hχ))
  · intro z hz
    have hd : ‖z-c‖=3/4 := by simpa [mem_sphere,dist_eq_norm] using hz
    have hre := Complex.abs_re_le_norm (z-c)
    have him := Complex.abs_im_le_norm (z-c)
    rw [Complex.sub_re,hc,hd] at hre
    rw [Complex.sub_im,hci,hd] at him
    have hzr : 1/2≤z.re := by linarith [(abs_le.mp hre).1]
    have hzi : |z.im|+2≤2*(|t|+2) := by
      have := abs_sub_abs_le_abs_sub z.im t
      linarith [abs_nonneg t]
    have hpoly : (q:ℝ)+48*(q:ℝ)^2+2 ≤ 51*(q:ℝ)^2 := by nlinarith [sq_nonneg ((q:ℝ)-1)]
    have hnum : ‖DirichletCharacter.LFunction χ z‖ ≤ 204*Q^2 := by
      calc
        _ ≤ _ := norm_LFunction_re_ge_half_le hχ hzr
        _ ≤ 51*(q:ℝ)^2 * (2*(|t|+2))^2 := by gcongr
        _ = _ := by dsimp [Q]; ring
    have hinv := norm_inv_LFunction_le_one_add_inv χ (s:=c) (by rw [hc]; norm_num)
    rw [hc] at hinv; norm_num at hinv
    rw [div_eq_mul_inv,norm_mul]
    calc
      _ ≤ (204*Q^2)*5 := by rw [norm_inv]; gcongr
      _ ≤ _ := by nlinarith [sq_nonneg Q]
  · rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    have hL := Real.log_nonneg (by linarith : 1≤Q)
    have h2 : 1/2≤Real.log 2 := by have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at this; linarith
    dsimp [Q] at *
    nlinarith [mul_nonneg hL (sub_nonneg.mpr h2)]
  · dsimp [Q] at *; linarith

/-- The fixed unshifted zeta factor has an absolute constant in all orders. -/
theorem exists_zetaOne_zero_power_bounds :
    ∃ H : ℝ, 0<H ∧ ∃ S, ZeroPowerBounds zetaOne (5/4) H S := by
  let c : ℂ := 5/4
  have hc : c.re=5/4 := by norm_num [c]
  have hn (z : ℂ) (hz : 1≤z.re) : zetaOne z≠0 := by
    by_cases he : z=1
    · simp [he]
    · rw [zetaOne_eq_sub_one_mul he]; exact mul_ne_zero (sub_ne_zero.mpr he) (riemannZeta_ne_zero_of_one_le_re hz)
  obtain ⟨B,hB,hb⟩ := norm_zetaOne_re_ge_half_le
  let M := 1+16*B*‖(zetaOne c)⁻¹‖
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨1+|Real.log M/Real.log 2|+|88*Real.log M|,by positivity,?_⟩
  apply scaled_zero_power_bounds hM hc
    ((differentiable_zetaOne.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)) hn
  · intro z hz
    have hd : ‖z-c‖=3/4 := by simpa [mem_sphere,dist_eq_norm] using hz
    have hre := Complex.abs_re_le_norm (z-c)
    have him := Complex.abs_im_le_norm (z-c)
    rw [Complex.sub_re,hc,hd] at hre
    have hci : c.im=0 := by norm_num [c]
    rw [Complex.sub_im,hci,sub_zero,hd] at him
    have hb' := hb z (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
    have hnorm : ‖zetaOne z‖ ≤ 16*B := by
      nlinarith [mul_nonneg hB.le (mul_nonneg (by linarith : 0≤1-|z.im|) (by linarith [abs_nonneg z.im] : 0≤7+|z.im|))]
    rw [div_eq_mul_inv,norm_mul]
    exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans (by dsimp [M]; linarith)
  · linarith [le_abs_self (Real.log M/Real.log 2),abs_nonneg (88*Real.log M)]
  · linarith [le_abs_self (88*Real.log M),abs_nonneg (Real.log M/Real.log 2)]

end AnalyticNumberTheory.DirichletLFunctions
