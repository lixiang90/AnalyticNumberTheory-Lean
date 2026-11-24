import AnalyticNumberTheory.PrimeDistribution.BombieriVinogradov

/-!
# Maximal Bombieri–Vinogradov

Each modulus may take its own real endpoint in `[0,x]`. Monotonicity of the
Chebyshev functions interpolates the fixed-endpoint theorem over a logarithmic grid.
-/

noncomputable section

open Finset Filter
open scoped Classical Topology

namespace AnalyticNumberTheory.PrimeDistribution

/-- The supremum over both reduced residue classes and all real endpoints in `[0,x]`. -/
def maximalPsiAPError (x : ℝ) (q : ℕ) : ℝ :=
  sSup ((fun y => maxPsiAPError y q) '' Set.Icc 0 x)

private lemma maxPsiAPError_zero (q : ℕ) : maxPsiAPError 0 q = 0 := by
  by_cases hq : 1 ≤ q <;> simp [maxPsiAPError, hq, psiAP]

private lemma maxPsiAPError_between {a b y : ℝ} (hay : a ≤ y) (hyb : y ≤ b)
    {q : ℕ} (hq : 1 ≤ q) :
    maxPsiAPError y q ≤ maxPsiAPError a q + maxPsiAPError b q + (b-a) / q.totient := by
  rw [maxPsiAPError, dite_eq_left hq, sup'_le_iff]
  intro r hr
  have hcop : r.Coprime q := (mem_filter.mp hr).2
  have ha := abs_psiAP_sub_le_maxPsiAPError a hq hcop
  have hb := abs_psiAP_sub_le_maxPsiAPError b hq hcop
  have hya := psiAP_mono (q:=q) (a:=r) hay
  have hyb' := psiAP_mono (q:=q) (a:=r) hyb
  have hya' := div_le_div_of_nonneg_right hay (Nat.cast_nonneg (α:=ℝ) q.totient)
  have hyb₂ := div_le_div_of_nonneg_right hyb (Nat.cast_nonneg (α:=ℝ) q.totient)
  rw [sub_div]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp ha).1, maxPsiAPError_nonneg b q],
    by linarith [(abs_le.mp hb).2, maxPsiAPError_nonneg a q]⟩

private lemma maxPsiAPError_trivial {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    maxPsiAPError y q ≤ (Real.log 4 + 5)*x := by
  rw [maxPsiAPError, dite_eq_left hq, sup'_le_iff]
  intro r _
  have hψ := (psiAP_le_psi y q r).trans (Chebyshev.psi_le_const_mul_self hy)
  have hφ : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hdiv := div_le_self hy hφ
  have hp : 0 ≤ Real.log 4 + 4 := by positivity
  have hp' := mul_le_mul_of_nonneg_left hyx hp
  exact abs_le.mpr ⟨by linarith [psiAP_nonneg y q r, mul_nonneg hp (hy.trans hyx)],
    by linarith [div_nonneg hy (Nat.cast_nonneg (α:=ℝ) q.totient), hy.trans hyx]⟩

/-- The value at every endpoint is bounded by the maximal progression error. -/
theorem maxPsiAPError_le_maximalPsiAPError {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    {q : ℕ} (hq : 1 ≤ q) : maxPsiAPError y q ≤ maximalPsiAPError x q := by
  unfold maximalPsiAPError
  apply le_csSup (s := (fun t : ℝ => maxPsiAPError t q) '' Set.Icc 0 x) _ ⟨y, ⟨hy, hyx⟩, rfl⟩
  refine ⟨(Real.log 4+5)*x, ?_⟩
  rintro z ⟨t, ht, he⟩
  rw [← he]
  exact maxPsiAPError_trivial ht.1 ht.2 hq

private lemma maximalPsiAPError_trivial {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 1 ≤ q) :
    maximalPsiAPError x q ≤ (Real.log 4+5)*x := by
  unfold maximalPsiAPError
  apply csSup_le ((Set.nonempty_Icc.mpr hx).image _)
  rintro z ⟨t, ht, he⟩
  rw [← he]
  exact maxPsiAPError_trivial ht.1 ht.2 hq

/-- A finite grid controls all real endpoints. The interpolation cost is the mesh
width divided by `φ(q)`, independently of the number of grid points. -/
theorem maximalPsiAPError_le_grid {h : ℝ} (hh : 0 < h) {J q : ℕ} (hJ : 1 ≤ J) (hq : 1 ≤ q) :
    maximalPsiAPError ((J:ℝ)*h) q ≤
      2 * (∑ j ∈ Icc 1 J, maxPsiAPError (j*h) q) + h/q.totient := by
  unfold maximalPsiAPError
  apply csSup_le ((Set.nonempty_Icc.mpr (by positivity : (0:ℝ) ≤ J*h)).image _)
  rintro _ ⟨y, hy, rfl⟩
  let k := max 1 ⌈y/h⌉₊
  have hk : 1 ≤ k := le_max_left ..
  have hkJ : k ≤ J := max_le hJ (Nat.ceil_le.mpr ((div_le_iff₀ hh).mpr hy.2))
  have hhi : y ≤ k*h := (div_le_iff₀ hh).mp ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..)))
  have hlo : (k-1:ℕ)*h ≤ y := by
    by_cases h1 : k = 1
    · simpa [h1] using hy.1
    · have hk' : k = ⌈y/h⌉₊ := by dsimp [k] at *; omega
      have h := Nat.ceil_lt_add_one (div_nonneg hy.1 hh.le)
      rw [← hk'] at h
      apply (le_div_iff₀ hh).mp
      rw [Nat.cast_sub hk, Nat.cast_one]; linarith
  have hp := maxPsiAPError_between hlo hhi hq
  have hi (i : ℕ) (hi : i ≤ J) : maxPsiAPError ((i:ℝ)*h) q ≤
      ∑ j ∈ Icc 1 J, maxPsiAPError (j*h) q := by
    obtain rfl | hpos := Nat.eq_zero_or_pos i
    · simpa [maxPsiAPError_zero] using sum_nonneg (s:=Icc 1 J) (fun j _ => maxPsiAPError_nonneg ((j:ℝ)*h) q)
    · exact single_le_sum (s := Icc 1 J) (fun (j:ℕ) _ => maxPsiAPError_nonneg ((j:ℝ)*h) q) (mem_Icc.mpr ⟨hpos, hi⟩)
  have heq : (k:ℝ)*h-(k-1:ℕ)*h = h := by rw [Nat.cast_sub hk, Nat.cast_one]; ring
  rw [heq] at hp
  linarith only [hp, hi k hkJ, hi (k-1) (by omega)]

private lemma eventually_grid_le_sqrt (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, 2*(Real.log x)^k ≤ Real.sqrt x := by
  have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have ht := ((tendsto_const_nhds (x := (2:ℝ))).mul ho).eventually
    (gt_mem_nhds (by norm_num : (2:ℝ)*0 < 1))
  filter_upwards [ht, eventually_gt_atTop (0:ℝ)] with x h hx
  change 2*(Real.log x^(k:ℝ) / x^(1/2:ℝ)) < 1 at h
  rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow, ← mul_div_assoc, div_lt_one (Real.sqrt_pos.mpr hx)] at h
  exact h.le

private theorem grid_bound_eventually (a : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ᶠ x : ℝ in atTop, ∀ {Q : ℝ}, 1 ≤ Q →
      Q ≤ Real.sqrt x / Real.log x^B →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, maximalPsiAPError x q ≤ C*x/(Real.log x)^a := by
  let k := a+2
  let H := 2*k
  obtain ⟨b, C₀, hC₀, hfixed⟩ := bombieriVinogradov (H:ℝ)
  obtain ⟨P,hP,hφ⟩ := sum_inv_totient_le_mul_log
  let b' := max b 0
  let B := b' + (k+1:ℕ)
  let K := C₀ * 2^H
  have hB : 0 ≤ B := by dsimp [B,b']; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨B,hB,4*K+2*P,by positivity,?_⟩
  filter_upwards [eventually_grid_le_sqrt k, Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop (4:ℝ)] with x hsize hl hx
  intro Q hQ hcut
  let l := Real.log x
  let J := ⌈l^k⌉₊
  let h := x/J
  have hx0 : 0 < x := by linarith
  have hl₁ : 1 ≤ l := by change 2 ≤ l at hl; linarith
  have hl0 : 0 < l := by linarith
  have hp : 1 ≤ l^k := one_le_pow₀ hl₁
  have hJlo : l^k ≤ (J:ℝ) := Nat.le_ceil _
  have hJ : 1 ≤ J := by exact_mod_cast hp.trans hJlo
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  have hJup : (J:ℝ) ≤ 2*l^k := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ l^k)
    change (J:ℝ) < l^k+1 at hceil
    linarith
  have hJx : (J:ℝ) ≤ Real.sqrt x := hJup.trans hsize
  have hJlog : (J:ℝ) ≤ l^(k+1) := by
    apply hJup.trans
    calc
      2*l^k ≤ l*l^k := mul_le_mul_of_nonneg_right hl (zero_le_one.trans hp)
      _ = _ := (pow_succ' l k).symm
  have hh : 0 < h := by dsimp [h]; positivity
  have hJh : (J:ℝ)*h = x := by dsimp [h]; field_simp
  have hroot : Real.sqrt x ≤ h := by
    apply (le_div_iff₀ hJpos).mpr
    exact (mul_le_mul_of_nonneg_left hJx (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hx0.le)
  have hhe : 2 ≤ h := (Real.le_sqrt_of_sq_le (by nlinarith : (2:ℝ)^2 ≤ x)).trans hroot
  have hQx : Q ≤ x := hcut.trans ((div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hl₁ hB)).trans
    (Real.sqrt_le_self_iff.mpr (.inr (by linarith))))
  have hnode (j : ℕ) (hj : j ∈ Icc 1 J) :
      ∑ q ∈ Icc 1 ⌊Q⌋₊, maxPsiAPError ((j:ℝ)*h) q ≤ K*x/l^H := by
    let y := (j:ℝ)*h
    have hyh : h ≤ y := le_mul_of_one_le_left hh.le (by exact_mod_cast (mem_Icc.mp hj).1)
    have hy : 2 ≤ y := hhe.trans hyh
    have hy0 : 0 < y := by linarith
    have hyx : y ≤ x := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mem_Icc.mp hj).2) hh.le).trans_eq hJh
    have hly : l/2 ≤ Real.log y := by
      have hy' := Real.log_le_log (Real.sqrt_pos.mpr hx0) (hroot.trans hyh)
      rwa [Real.log_sqrt hx0.le] at hy'
    have hly₁ : 1 ≤ Real.log y := by change 2 ≤ l at hl; linarith
    have hlyx : Real.log y ≤ l := Real.log_le_log hy0 hyx
    have hden : Real.log y^b ≤ l^b' := (Real.rpow_le_rpow_of_exponent_le hly₁ (le_max_left ..)).trans
      (Real.rpow_le_rpow (by linarith) hlyx (le_max_right ..))
    have hpow : l^B = l^b' * l^(k+1) := by dsimp only [B]; rw [Real.rpow_add hl0, Real.rpow_natCast]
    have hroot' : Real.sqrt x ≤ (J:ℝ) * Real.sqrt y := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hy0.le]
      calc
        x = (J:ℝ)*h := hJh.symm
        _ ≤ (J:ℝ)^2*y := mul_le_mul (by nlinarith [(show (1:ℝ) ≤ J by exact_mod_cast hJ)]) hyh hh.le (sq_nonneg _)
    have hycut : Q ≤ Real.sqrt y / Real.log y^b := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _)).mpr
      have hspan : Q*l^b'*l^(k+1) ≤ Real.sqrt x := by
        rw [mul_assoc, ← hpow]
        exact (le_div_iff₀ (Real.rpow_pos_of_pos hl0 _)).mp hcut
      have hylarge := hspan.trans (hroot'.trans (mul_le_mul_of_nonneg_right hJlog (Real.sqrt_nonneg y)))
      apply (mul_le_mul_of_nonneg_left hden (zero_le_one.trans hQ)).trans
      apply (mul_le_mul_iff_left₀ (by positivity : 0 < l^(k+1))).mp
      convert hylarge using 1; ring
    have h := hfixed hy hQ (by rwa [← Real.sqrt_eq_rpow])
    rw [Real.rpow_natCast] at h
    apply h.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he : l^H ≤ 2^H*(Real.log y)^H := by
      rw [← mul_pow]; gcongr; linarith
    calc
      C₀*y*l^H ≤ C₀*x*(2^H*(Real.log y)^H) := by gcongr
      _ = _ := by dsimp [K]; ring
  have hgrid (q : ℕ) (hq : q ∈ Icc 1 ⌊Q⌋₊) := maximalPsiAPError_le_grid hh hJ (mem_Icc.mp hq).1
  have hlogQ : Real.log ((⌊Q⌋₊:ℝ)+2) ≤ 2*l := by
    have harg : (⌊Q⌋₊:ℝ)+2 ≤ x^2 := by
      have hf := (Nat.floor_le (by linarith : 0 ≤ Q)).trans hQx
      nlinarith
    have h := Real.log_le_log (by positivity) harg
    simpa [Real.log_pow, l] using h
  have hsum : ∑ q ∈ Icc 1 ⌊Q⌋₊, maximalPsiAPError x q ≤
      2*((J:ℝ)*(K*x/l^H)) + h*(P*(2*l)) := by
    have h := sum_le_sum (s := Icc 1 ⌊Q⌋₊) hgrid
    rw [hJh] at h
    simp_rw [sum_add_distrib, ← mul_sum] at h
    rw [sum_comm (s:=Icc 1 ⌊Q⌋₊) (t:=Icc 1 J)] at h
    apply h.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa [Nat.card_Icc] using (sum_le_sum hnode)
    · simp_rw [div_eq_mul_inv, ← mul_sum]
      exact mul_le_mul_of_nonneg_left ((hφ _).trans (mul_le_mul_of_nonneg_left hlogQ hP.le)) hh.le
  apply hsum.trans
  have h1 : (J:ℝ)*(K*x/l^H) ≤ 2*K*x/l^a := by
    calc
      _ ≤ (2*l^k)*(K*x/l^H) := mul_le_mul_of_nonneg_right hJup (by positivity)
      _ = 2*K*x/l^k := by dsimp only [H]; rw [mul_comm 2 k, pow_mul]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hl₁ (by dsimp [k]; omega))
  have h2 : h*(P*(2*l)) ≤ 2*P*x/l^a := by
    have hh' : h ≤ x/l^k := div_le_div_of_nonneg_left hx0.le (by positivity) hJlo
    calc
      _ ≤ (x/l^k)*(P*(2*l)) := mul_le_mul_of_nonneg_right hh' (by positivity)
      _ ≤ _ := by
        dsimp only [k]
        rw [show a+2=a+1+1 by omega, pow_succ, pow_succ]
        field_simp
        exact hl₁
  calc
    _ ≤ 2*(2*K*x/l^a) + 2*P*x/l^a := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
    _ = _ := by ring

/-- The maximal Bombieri–Vinogradov theorem. The supremum in the summand
includes every real `y ∈ [0,x]` and every reduced class of the modulus. -/
theorem bombieriVinogradov_maximal (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ Real.sqrt x / Real.log x^B →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, maximalPsiAPError x q ≤ C*x/Real.log x^A := by
  let a := ⌈A⌉₊
  obtain ⟨B, hB, C, hC, hlarge⟩ := grid_bound_eventually a
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlarge.and (Real.tendsto_log_atTop.eventually_ge_atTop 1))
  let X := max T 3
  let Y := Real.sqrt X/(Real.log 2)^B
  let L := max (Real.log X ^ A) (Real.log 2 ^ A)
  let K := Y*(Real.log 4+5)*L
  have hX : 3 ≤ X := le_max_right ..
  have hL : 0 ≤ L := (Real.rpow_nonneg (Real.log_nonneg (by linarith : 1 ≤ X)) A).trans (le_max_left ..)
  refine ⟨B,hB,max C K, hC.trans_le (le_max_left ..),?_⟩
  intro x Q hx hQ hcut
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hl₂ : 0 < Real.log 2 := Real.log_pos one_lt_two
  by_cases hTx : T ≤ x
  · obtain ⟨hb,hlog⟩ := hT x hTx
    apply (hb hQ hcut).trans
    have ha : Real.log x^A ≤ Real.log x^a := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hlog (Nat.le_ceil _)
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left ..) hx0.le)
      (Real.rpow_pos_of_pos hl _) ha
  · have hxX : x ≤ X := (le_of_not_ge hTx).trans (le_max_left ..)
    have hqY : Q ≤ Y := hcut.trans <| div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hxX)
      (Real.rpow_pos_of_pos hl₂ _) (Real.rpow_le_rpow hl₂.le (Real.log_le_log (by norm_num) hx) hB)
    have hLx : Real.log x ^ A ≤ L := by
      by_cases hA : 0 ≤ A
      · exact (Real.rpow_le_rpow hl.le (Real.log_le_log hx0 hxX) hA).trans (le_max_left ..)
      · exact (Real.rpow_le_rpow_of_nonpos hl₂ (Real.log_le_log (by norm_num) hx) (le_of_not_ge hA)).trans (le_max_right ..)
    have hsum : (∑ q ∈ Icc 1 ⌊Q⌋₊, maximalPsiAPError x q) ≤ Y*((Real.log 4+5)*x) := by
      calc
        _ ≤ ∑ _q ∈ Icc 1 ⌊Q⌋₊, ((Real.log 4+5)*x) :=
          sum_le_sum fun q hq => maximalPsiAPError_trivial hx0.le (mem_Icc.mp hq).1
        _ ≤ _ := by
          simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right ((Nat.floor_le (by linarith : 0 ≤ Q)).trans hqY) (by positivity)
    apply hsum.trans
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hl A)]
    calc
      _ ≤ Y*((Real.log 4+5)*x)*L := mul_le_mul_of_nonneg_left hLx (by
        dsimp [Y]; positivity)
      _ = K*x := by dsimp [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) hx0.le

/-- An error dominated by a constant multiple of the maximal Chebyshev error plus
`sqrt x` has the same level of distribution. -/
theorem bombieriVinogradov_of_le_maximal_add_sqrt {F : ℝ → ℕ → ℝ} {D : ℝ} (hD : 0 < D)
    (hF : ∀ {x : ℝ}, 2 ≤ x → ∀ {q : ℕ}, 1 ≤ q → F x q ≤ D*(maximalPsiAPError x q + Real.sqrt x))
    (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ Real.sqrt x / Real.log x^B → ∑ q ∈ Icc 1 ⌊Q⌋₊, F x q ≤ C*x/Real.log x^A := by
  obtain ⟨b,hb,C,hC,hmax⟩ := bombieriVinogradov_maximal A
  let B := max b A
  let Y := Real.sqrt (Real.exp 1)/(Real.log 2)^B
  let L := max 1 (Real.log 2 ^ A)
  let K := Y*D*(Real.log 4+6)*L
  have hB : 0 ≤ B := hb.trans (le_max_left ..)
  refine ⟨B,hB,max (D*(C+1)) K,(by positivity : 0 < D*(C+1)).trans_le (le_max_left ..),?_⟩
  intro x Q hx hQ hcut
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hfq := Nat.floor_le (by linarith : 0 ≤ Q)
  have htot := sum_le_sum (s := Icc 1 ⌊Q⌋₊) (fun q hq => hF hx (mem_Icc.mp hq).1)
  by_cases hlog : 1 ≤ Real.log x
  · have hpow (c : ℝ) (hc : c ≤ B) := Real.rpow_le_rpow_of_exponent_le hlog hc
    have hcut' (c : ℝ) (hc : c ≤ B) : Q ≤ Real.sqrt x/Real.log x^c :=
      hcut.trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hl _) (hpow c hc))
    have he := hmax hx hQ (hcut' b (le_max_left ..))
    have hsqrt : (⌊Q⌋₊:ℝ)*Real.sqrt x ≤ x/Real.log x^A := by
      calc
        _ ≤ (Real.sqrt x/Real.log x^A)*Real.sqrt x :=
          mul_le_mul_of_nonneg_right (hfq.trans (hcut' A (le_max_right ..))) (Real.sqrt_nonneg _)
        _ = _ := by rw [div_mul_eq_mul_div, Real.mul_self_sqrt hx0.le]
    apply htot.trans
    simp only [← mul_sum, sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    calc
      _ ≤ D*(C*x/Real.log x^A + x/Real.log x^A) :=
        mul_le_mul_of_nonneg_left (add_le_add he hsqrt) hD.le
      _ = (D*(C+1))*x/Real.log x^A := by ring
      _ ≤ _ := by gcongr; exact le_max_left ..
  · have hlog' := le_of_not_ge hlog
    have hlog₂ : Real.log 2 ≤ Real.log x := Real.log_le_log zero_lt_two hx
    have he : x ≤ Real.exp 1 := (Real.log_le_iff_le_exp hx0).mp hlog'
    have hY : Q ≤ Y := hcut.trans (div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt he)
      (Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _) (Real.rpow_le_rpow (Real.log_pos one_lt_two).le hlog₂ hB))
    have hY0 : 0 ≤ Y := (by linarith : 0 ≤ Q).trans hY
    have hL : Real.log x^A ≤ L := by
      by_cases hA : 0 ≤ A
      · exact (Real.rpow_le_one hl.le hlog' hA).trans (le_max_left ..)
      · exact (Real.rpow_le_rpow_of_nonpos (Real.log_pos one_lt_two) hlog₂ (le_of_not_ge hA)).trans (le_max_right ..)
    have hbound (q : ℕ) (hq : q ∈ Icc 1 ⌊Q⌋₊) : F x q ≤ D*((Real.log 4+6)*x) := by
      apply (hF hx (mem_Icc.mp hq).1).trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      linarith only [maximalPsiAPError_trivial hx0.le (mem_Icc.mp hq).1, Real.sqrt_le_self_iff.mpr (.inr (by linarith : 1 ≤ x))]
    apply (sum_le_sum hbound).trans
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hl _)]
    calc
      _ ≤ (Y*(D*((Real.log 4+6)*x)))*L := mul_le_mul (mul_le_mul_of_nonneg_right (hfq.trans hY) (by positivity))
        hL (Real.rpow_nonneg hl.le _) (by positivity)
      _ = K*x := by dsimp [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) hx0.le

/-- The corresponding maximum for the first Chebyshev function over all real endpoints. -/
def maximalThetaAPError (x : ℝ) (q : ℕ) : ℝ :=
  sSup ((fun y => maxThetaAPError y q) '' Set.Icc 0 x)

/-- Pointwise conversion of a maximal `ψ` bound to a `θ` bound. -/
theorem abs_thetaAP_sub_le_maximalPsiAPError {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x)
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) :
    |thetaAP t q a - t/q.totient| ≤ maximalPsiAPError x q + ((Real.log 4+4)*3)*Real.sqrt x := by
  have he := (abs_psiAP_sub_le_maxPsiAPError t hq ha).trans (maxPsiAPError_le_maximalPsiAPError ht htx hq)
  have hminor := (abs_psiAP_sub_thetaAP_le t q a).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htx) (by positivity))
  have htriangle := abs_sub (psiAP t q a - t/q.totient) (psiAP t q a - thetaAP t q a)
  rw [show psiAP t q a - t/q.totient - (psiAP t q a - thetaAP t q a) =
      thetaAP t q a - t/q.totient by ring] at htriangle
  exact htriangle.trans (add_le_add he hminor)

/-- Maximal Bombieri–Vinogradov for `θ`. -/
theorem bombieriVinogradov_maximal_theta (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C > 0, ∀ {x Q : ℝ}, 2 ≤ x → 1 ≤ Q →
      Q ≤ Real.sqrt x / Real.log x^B →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, maximalThetaAPError x q ≤ C*x/Real.log x^A := by
  let D := (Real.log 4+4)*3
  apply bombieriVinogradov_of_le_maximal_add_sqrt (D:=D) (by dsimp [D]; positivity) _ A
  intro x hx q hq
  have hx0 : 0 ≤ x := by linarith
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  have hpos := (maxPsiAPError_nonneg _ q).trans (maxPsiAPError_le_maximalPsiAPError hx0 le_rfl hq)
  unfold maximalThetaAPError
  apply csSup_le ((Set.nonempty_Icc.mpr hx0).image _)
  rintro _ ⟨t, ht, rfl⟩
  change maxThetaAPError t q ≤ _
  rw [maxThetaAPError, dite_eq_left hq, sup'_le_iff]
  intro a ha
  apply (abs_thetaAP_sub_le_maximalPsiAPError ht.1 ht.2 hq (mem_filter.mp ha).2).trans
  change _ + D*Real.sqrt x ≤ _
  nlinarith only [mul_le_mul_of_nonneg_right hD hpos]

end AnalyticNumberTheory.PrimeDistribution
