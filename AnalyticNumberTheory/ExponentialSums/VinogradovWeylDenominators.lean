import AnalyticNumberTheory.ExponentialSums.VinogradovBilinearBounds

/-!
# Denominator windows for Vinogradov's Weyl estimate

For denominators between `P^β` and `P^(n+1-β)` the highest-frequency
kernel saves `β-1/32` in the power of the length. The other factors
contribute the volume of the lower-degree moment box.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- Lower-frequency volume in a box of radii `s N^j`. -/
theorem vinogradov_lower_frequency_volume (d : ℕ) {s N : ℕ} (hs : 0<s) (hN : 0<N) :
    (∏ j : Fin d, (2*(s*N^(j.val+1):ℕ)+1:ℝ)) ≤
      (3*(s:ℝ))^d * (N:ℝ)^((d:ℝ)*(d+1)/2) := by
  have hN' : 0<(N:ℝ) := by positivity
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    have h1 : (1:ℝ)≤(s*N^(d+1):ℕ) := by exact_mod_cast Nat.mul_pos hs (pow_pos hN _)
    have H : (2*(s*N^(d+1):ℕ)+1:ℝ)≤(3*(s:ℝ))*(N:ℝ)^(d+1) := by push_cast at h1 ⊢; linarith only [h1]
    apply (mul_le_mul ih H (by positivity) (by positivity)).trans_eq
    rw [show ((d:ℝ)+1)*(d+1+1)/2=(d:ℝ)*(d+1)/2+((d+1:ℕ):ℝ) by push_cast; ring,
      Real.rpow_add hN',Real.rpow_natCast,pow_succ]; ring

/-- Arithmetic estimate for the highest retained frequency. The dependence
of the constant on the degree and moment is explicit. -/
theorem vinogradov_top_kernel_window {P Y q n s β : ℝ}
    (hP : 1≤P) (hn : 1≤n) (hs : 1≤s) (hβ : 0≤β) (hβ' : β≤1/4)
    (hY : P^(63/64:ℝ)≤2*Y) (hq : P^β≤q) (hq' : q≤P^(n+1-β)) :
    let L := 2*s*P^n+1
    let D := 2+64*(n+1)
    let C := 6*s + 18*((n+1)*D+2*D+3*(n+1)*s)
    L+18*(((n+1)*Y+q)*Real.log (2*q)+(n+1)*Y*L/q) ≤ Y*C*P^(n-β+1/32) := by
  intro L D C
  let V := P^(1/64:ℝ)
  let U := P^(63/64:ℝ)
  let G := P^(n-β+1/32)
  have hP0 : 0<P := by linarith
  have hV : 1≤V := Real.one_le_rpow hP (by norm_num)
  have hU0 : 0<U := Real.rpow_pos_of_pos hP0 _
  have hG0 : 0<G := Real.rpow_pos_of_pos hP0 _
  have hD : 0≤D := by dsimp [D]; linarith
  have hq0 := (Real.rpow_pos_of_pos hP0 β).trans_le hq
  have hY0 : 0≤Y := by change U≤2*Y at hY; linarith only [hY,hU0]
  have hl : Real.log (2*q)≤D*V := by
    rw [Real.log_mul (by norm_num) hq0.ne']
    have HH := Real.log_le_log hq0 hq'
    rw [Real.log_rpow hP0] at HH
    have hp := Real.log_le_rpow_div hP0.le (by norm_num : (0:ℝ)<1/64)
    dsimp only [V,D]
    nlinarith only [HH,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ)),hV,
      mul_le_mul_of_nonneg_left hp (show 0≤n+1 by linarith),mul_nonneg hβ (Real.log_nonneg hP)]
  have hLG : P^n≤U*G := by
    dsimp only [U,G]; rw [←Real.rpow_add hP0]; apply Real.rpow_le_rpow_of_exponent_le hP; linarith
  have hVG : V≤G := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hqV : q*V≤U*G := by
    apply (mul_le_mul_of_nonneg_right hq' (Real.rpow_pos_of_pos hP0 _).le).trans_eq
    dsimp only [U,V,G]; rw [←Real.rpow_add hP0,←Real.rpow_add hP0]; congr 1; ring
  have hL : L≤3*s*P^n := by
    have hPn : 1≤P^n := Real.one_le_rpow hP (by linarith)
    dsimp [L]; nlinarith only [one_le_mul_of_one_le_of_one_le hs hPn]
  have hYg : U*G≤2*Y*G := mul_le_mul_of_nonneg_right hY hG0.le
  have hL' : L≤6*s*Y*G := by
    apply hL.trans
    have H := mul_le_mul_of_nonneg_left (hLG.trans hYg) (show 0≤3*s by linarith)
    linarith only [H]
  have hqG : P^n≤G*q := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hq hG0.le)
    dsimp only [G]; rw [←Real.rpow_add hP0]; apply Real.rpow_le_rpow_of_exponent_le hP; linarith
  have hLq : L/q ≤ 3*s*G := by
    apply (div_le_iff₀ hq0).mpr
    apply hL.trans
    linarith only [mul_le_mul_of_nonneg_left hqG (show 0≤3*s by linarith)]
  have hlin : ((n+1)*Y+q)*Real.log (2*q) ≤ ((n+1)*D+2*D)*Y*G := by
    apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans
    have h1 := mul_le_mul_of_nonneg_left hVG (show 0≤(n+1)*Y*D by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hqV.trans hYg) hD
    linarith only [h1,h2]
  have htail : (n+1)*Y*L/q ≤ 3*(n+1)*s*Y*G := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hLq (show 0≤(n+1)*Y by positivity)).trans_eq (by ring)
  change _ ≤ Y*C*G
  dsimp only [C]; linarith only [hL',hlin,htail]

/-- An integral shift length within a factor of two of `P^(63/64)`. -/
theorem exists_weyl_shift_length {P : ℝ} (hP : 1≤P) :
    ∃ Y : ℕ, 1≤Y ∧ (Y:ℝ)≤P^(63/64:ℝ) ∧ P^(63/64:ℝ)≤2*Y := by
  let A := P^(63/64:ℝ)
  have hA : 1≤A := Real.one_le_rpow hP (by norm_num)
  let Y := ⌊A⌋₊
  have hY : 1≤Y := Nat.le_floor (by simpa using hA)
  have hY1 : (1:ℝ)≤Y := by exact_mod_cast hY
  have H := Nat.lt_floor_add_one A
  change A<(Y:ℝ)+1 at H
  exact ⟨Y,hY,Nat.floor_le (by linarith : 0≤A),by change A≤2*(Y:ℝ); linarith⟩

end AnalyticNumberTheory.ExponentialSums
