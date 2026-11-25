import AnalyticNumberTheory.ExponentialSums.LogarithmicPhases
import AnalyticNumberTheory.AnalyticTools.Summation.Abel
import AnalyticNumberTheory.AnalyticTools.Summation.DyadicBlocks

/-!
# Correlation kernels for logarithmic phases

The first derivative test controls low frequencies on a dyadic block. The
second derivative test supplies a square-root bound at higher frequencies.
Together they estimate the kernels in the Halász–Montgomery method.
-/

noncomputable section
open Real Complex Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem logPhase_first {M b : ℕ} (hM : 1 ≤ M) (hb : M ≤ b) (hb' : b ≤ 2*M)
    {τ : ℝ} (hτ : 0 < |τ|) (hτ' : |τ| ≤ (M:ℝ)/2) :
    ‖∑ n ∈ Ioc M b, Complex.exp (2*Real.pi*(logPhase τ 0 n:ℂ)*I)‖ ≤
      4*(M:ℝ)/|τ| := by
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : 0 < (M:ℝ) := by linarith
  have hx {x : ℝ} (h : x ∈ Set.Icc (M:ℝ) b) : 0<x := hM0.trans_le h.1
  have htop : (b:ℝ) ≤ 2*M := by exact_mod_cast hb'
  have h := vanDerCorput_first_deriv (f:=logPhase τ 0) (f':=fun x => τ/x) hb
    (show 0 < |τ|/(2*(M:ℝ)) by positivity)
    (fun x h => by simpa using logPhase_deriv τ 0 (x:=x) (by simpa using hx h))
    (continuousOn_const.div continuousOn_id fun x h => (hx h).ne') (by
      rcases le_total 0 τ with hpos | hneg
      · right; intro x hx' y _ hxy
        exact div_le_div_of_nonneg_left hpos (hx hx') hxy
      · left; intro x hx' y _ hxy
        have hh := div_le_div_of_nonneg_left (neg_nonneg.mpr hneg) (hx hx') hxy
        simpa only [neg_div,neg_le_neg_iff] using hh)
    (fun x h => by
      rw [abs_div,abs_of_pos (hx h)]
      exact ⟨div_le_div_of_nonneg_left hτ.le (hx h) (h.2.trans htop),
        (div_le_iff₀ (hx h)).mpr (by linarith [h.1])⟩)
  apply h.trans_eq
  field_simp; ring

/-- A partially completed block at every frequency, including zero. -/
theorem logPhase_correlation_bound {M b : ℕ} (hM : 1≤M) (hb : M≤b) (hb' : b≤2*M)
    (τ : ℝ) :
    ‖∑ n ∈ Ioc M b, Complex.exp (2*Real.pi*(logPhase τ 0 n:ℂ)*I)‖ ≤
      2000*((M:ℝ)/(1+|τ|)+Real.sqrt (1+|τ|)) := by
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : 0 < (M:ℝ) := by linarith
  have hpos : 0 < 1+|τ| := by positivity
  have hss := Real.sqrt_nonneg (1+|τ|)
  by_cases hsmall : |τ| ≤ 1
  · have htriv : ‖∑ n ∈ Ioc M b, Complex.exp (2*Real.pi*(logPhase τ 0 n:ℂ)*I)‖ ≤ M := by
      apply (norm_sum_le ..).trans
      have hone (n : ℕ) : ‖Complex.exp (2*Real.pi*(logPhase τ 0 n:ℂ)*I)‖=1 := by
        rw [Complex.norm_exp]; simp
      simp only [hone,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc]
      exact_mod_cast (show b-M ≤ M by omega)
    have hfrac : (M:ℝ)/2 ≤ M/(1+|τ|) := div_le_div_of_nonneg_left hM0.le hpos (by linarith)
    linarith only [htriv,hfrac,hM0,hss]
  have ht : 0 < |τ| := by linarith
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp; positivity
  by_cases hlo : |τ| ≤ (M:ℝ)/2
  · have hf := logPhase_first hM hb.le hb' ht hlo
    have hfrac : 1/|τ| ≤ 2/(1+|τ|) := (div_le_div_iff₀ ht hpos).mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hfrac (by positivity : 0≤(M:ℝ))
    have hnon : 0 ≤ (M:ℝ)/(1+|τ|) := by positivity
    simp only [div_eq_mul_inv] at hf hh hnon ⊢
    linarith only [hf,hh,hss,hnon]
  · have h := logPhase_second_derivative_bound hM hb hb' (a:=0) (by constructor <;> norm_num) ht
    have hs : 0 < Real.sqrt |τ| := Real.sqrt_pos.mpr ht
    have hs' := Real.sq_sqrt ht.le
    have hrt : Real.sqrt (|τ|/(9*(M:ℝ)^2)) = Real.sqrt |τ|/(3*M) := by
      rw [Real.sqrt_div ht.le,show 9*(M:ℝ)^2 = (3*M)^2 by ring,Real.sqrt_sq (by positivity)]
    rw [hrt] at h
    have hi : (Real.sqrt |τ|/(3*M))⁻¹ ≤ 6*Real.sqrt |τ| := by
      rw [inv_div,div_le_iff₀ hs]; nlinarith only [hs',hlo]
    have hlen : (b:ℝ)-M ≤ M := by
      have hbd : (b:ℝ) ≤ 2*M := by exact_mod_cast hb'
      linarith
    have hterm : ((b:ℝ)-M)*(Real.sqrt |τ|/(3*M)) ≤ Real.sqrt |τ| := by
      apply (mul_le_mul_of_nonneg_right hlen (by positivity : 0≤Real.sqrt |τ|/(3*M))).trans
      rw [←mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith only [mul_nonneg hs.le hM0.le]
    have hwide := Real.sqrt_le_sqrt (show |τ|≤1+|τ| by linarith)
    have hnon : 0≤(M:ℝ)/(1+|τ|) := by positivity
    linarith only [h,hi,hterm,hwide,hs.le,hnon]

/-- Nonnegative decreasing weights transfer a uniform bound for initial
segments to the weighted block at the cost of the initial weight. -/
theorem norm_sum_Ioc_antitone_weight {a b : ℕ} (hab : a≤b) {c : ℕ → ℂ} {w : ℕ → ℝ}
    (hw : AntitoneOn w (Set.Icc a b)) (hw₀ : 0 ≤ w b) {H : ℝ}
    (hpartial : ∀ k, a≤k → k≤b → ‖∑ n∈Ioc a k, c n‖ ≤ H) :
    ‖∑ n∈Ioc a b, c n*(w n:ℂ)‖ ≤ H*w a := by
  rw [AnalyticNumberTheory.AnalyticTools.Summation.abel_discrete_Ioc_from c (fun k => (w k:ℂ)) hab]
  apply (norm_sub_le ..).trans
  have htop : ‖(∑ n∈Ioc a b,c n)*(w b:ℂ)‖ ≤ H*w b := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw₀]
    exact mul_le_mul_of_nonneg_right (hpartial b hab le_rfl) hw₀
  have hn (k : ℕ) (hk : k∈Ico a b) :
      ‖(∑ n∈Ioc a k, c n)*((w (k+1):ℂ)-(w k:ℂ))‖ ≤ H*(w k-w (k+1)) := by
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hk
    have hd : w (k+1) ≤ w k := hw ⟨h₁,h₂.le⟩ ⟨by omega,by omega⟩ (by omega)
    rw [norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hd)]
    simpa only [neg_sub] using mul_le_mul_of_nonneg_right (hpartial k h₁ h₂.le) (sub_nonneg.mpr hd)
  have htel : ∑ k∈Ico a b, (w k-w (k+1)) = w a-w b := by
    clear hw hw₀ hpartial htop hn
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hb ih => rw [sum_Ico_succ_top hb,ih]; ring
  apply (add_le_add htop ((norm_sum_le ..).trans (sum_le_sum hn))).trans_eq
  rw [←mul_sum,htel]; ring

/-- The dyadic Dirichlet kernel on a right half-plane. The estimate is uniform
in the real part and in the upper endpoint of the block. -/
theorem dirichlet_dyadic_correlation {M b : ℕ} (hM : 1≤M) (hb : M≤b) (hb' : b≤2*M)
    {β : ℝ} (hβ : 0≤β) (t : ℝ) :
    ‖∑ n∈Ioc M b, (n:ℂ)^(-((β:ℂ)+(t:ℂ)*I))‖ ≤
      (4000*π)*(M/(1+|t|)+Real.sqrt (1+|t|))*(M:ℝ)^(-β) := by
  let τ := -t/(2*π)
  let c (n : ℕ) := Complex.exp (2*π*(logPhase τ 0 n:ℂ)*I)
  have hτ : |τ|=|t|/(2*π) := by dsimp [τ]; rw [abs_div,abs_neg,abs_of_pos (by positivity : 0<2*π)]
  have hπ : 1 ≤ 2*π := by linarith [Real.pi_gt_three]
  have heq (n : ℕ) (hn : n ∈ Ioc M b) :
      (n:ℂ)^(-((β:ℂ)+(t:ℂ)*I)) = c n*((n:ℝ)^(-β):ℝ) := by
    have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr (by have := (mem_Ioc.mp hn).1; omega)
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n),Complex.ofReal_natCast,Complex.ofReal_neg]
    rw [Complex.cpow_def_of_ne_zero hn0,Complex.cpow_def_of_ne_zero hn0]
    dsimp [c,logPhase,τ]
    rw [←Complex.exp_add,←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n)]
    push_cast
    have hlog : ((Real.log (n:ℝ)):ℂ)=Complex.log (n:ℂ) := by simpa only [Complex.ofReal_natCast] using Complex.ofReal_log (Nat.cast_nonneg n)
    rw [add_zero,hlog]; congr 1; field_simp [Real.pi_ne_zero]; ring
  rw [sum_congr rfl heq]
  have hw : AntitoneOn (fun n : ℕ => (n:ℝ)^(-β)) (Set.Icc M b) := by
    intro n hn k _ hnk
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt hM) hn.1) (by exact_mod_cast hnk) (by linarith)
  apply (norm_sum_Ioc_antitone_weight (c:=c) hb hw (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun k hk hk' => logPhase_correlation_bound hM hk (hk'.trans hb') τ)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [hτ]
  have ht : 0 ≤ |t| := abs_nonneg _
  have hs := Real.sqrt_le_sqrt (show 1+|t|/(2*π)≤1+|t| by linarith [div_le_self ht hπ])
  have hfrac : (M:ℝ)/(1+|t|/(2*π)) ≤ 2*π*(M/(1+|t|)) := by
    rw [div_le_iff₀ (by positivity),mul_assoc,div_mul_eq_mul_div,←mul_div_assoc,
      le_div_iff₀ (by positivity)]
    field_simp; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (sub_nonneg.mpr hπ)]
  nlinarith only [hfrac,hs,mul_nonneg (sub_nonneg.mpr hπ) (Real.sqrt_nonneg (1+|t|))]

/-- Correlation kernel for a complete Dirichlet polynomial, uniformly throughout
the right half-plane. -/
theorem dirichlet_correlation_bound {N : ℕ} (hN : 1≤N) {β : ℝ} (hβ : 0≤β) (t : ℝ) :
    ‖∑ n∈Icc 1 N, (n:ℂ)^(-((β:ℂ)+(t:ℂ)*I))‖ ≤ (1+8000*π)*(1+Real.log N)*
      (N/(1+|t|)+Real.sqrt (1+|t|)) := by
  let J := Nat.log 2 N+1
  let L := 1+Real.log N
  let W := N/(1+|t|)+Real.sqrt (1+|t|)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hNr]
  have hW : 1 ≤ W := by
    have hs := Real.sqrt_le_sqrt (by linarith [abs_nonneg t] : (1:ℝ) ≤ 1+|t|)
    rw [Real.sqrt_one] at hs
    dsimp only [W]; linarith [show 0 ≤ (N:ℝ)/(1+|t|) by positivity]
  have hlog := Nat.pow_log_le_self 2 (by omega : N≠0)
  have hJ : (J:ℝ) ≤ 2*L := by
    have hh := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 N)) (by exact_mod_cast hlog : (2:ℝ)^(Nat.log 2 N)≤N)
    rw [Real.log_pow] at hh
    dsimp [J,L]; push_cast
    nlinarith only [hh, mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9] : (1/2:ℝ)≤Real.log 2)
      (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 N))]
  rw [AnalyticNumberTheory.AnalyticTools.Summation.sum_Icc_eq_dyadic_blocks (K:=J) _ hN
    (Nat.lt_pow_succ_log_self one_lt_two N).le]
  apply (norm_add_le ..).trans
  have each (j : ℕ) (hj : j∈range J) :
      ‖∑ n∈AnalyticNumberTheory.AnalyticTools.Summation.dyadicBlock N j,
        (n:ℂ)^(-((β:ℂ)+(t:ℂ)*I))‖ ≤ (4000*π)*W := by
    have hM : 1≤2^j := Nat.one_le_pow _ _ (by decide)
    have hMN : 2^j≤N := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt_succ (mem_range.mp hj))).trans hlog
    have hM' : 2^j≤2^(j+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h := dirichlet_dyadic_correlation hM (le_min hMN hM') ((min_le_right N (2^(j+1))).trans_eq (by rw [pow_succ]; ring)) hβ t
    have hm : (1:ℝ)≤(2^j:ℕ) := by exact_mod_cast hM
    have hb := Real.rpow_le_one_of_one_le_of_nonpos hm (neg_nonpos.mpr hβ)
    apply h.trans
    apply (mul_le_of_le_one_right (by positivity) hb).trans
    dsimp only [W]; gcongr
  have hsum := (norm_sum_le ..).trans (sum_le_sum each)
  simp only [sum_const,nsmul_eq_mul,card_range] at hsum
  simp only [Nat.cast_one,Complex.one_cpow,norm_one]
  apply (add_le_add_right hsum 1).trans
  have hj := mul_le_mul_of_nonneg_right hJ (by positivity : 0≤4000*π*W)
  have hlw : 1≤L*W := one_le_mul_of_one_le_of_one_le hL hW
  change _ ≤ (1+8000*π)*L*W
  linarith only [hj,hlw]

end AnalyticNumberTheory.ExponentialSums
