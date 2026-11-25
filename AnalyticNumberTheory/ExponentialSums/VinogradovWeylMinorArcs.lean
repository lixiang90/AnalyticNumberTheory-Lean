import AnalyticNumberTheory.ExponentialSums.VinogradovWeylDenominators
import AnalyticNumberTheory.ExponentialSums.VinogradovWeylShifts
import AnalyticNumberTheory.ExponentialSums.VinogradovDegreeBounds

/-!
# Vinogradov's Weyl sum estimate on the minor arcs

For a polynomial of degree `n+1`, the mean value in degree `n` yields a
saving of order `1/(n² log n)` throughout the rational-approximation
window. Both exponents of the denominator window are kept explicit.
-/

open Real Finset Polynomial
open scoped Polynomial
namespace AnalyticNumberTheory.ExponentialSums

/-- A finite moment of order at most `16 n² log n` with exponent defect
at most `1/64`. -/
theorem exists_vinogradov_weyl_moment {n : ℕ} (hn : 2≤n) :
    ∃ s : ℕ, 4≤s ∧ (s:ℝ)≤16*(n:ℝ)^2*Real.log n ∧ ∃ C : ℝ, 0<C ∧
      ∀ {N : ℕ}, 1≤N → vinogradovJ s n N ≤ C*(N:ℝ)^(2*(s:ℝ)-(n:ℝ)*(n+1)/2+1/64) := by
  let d := ⌈6*Real.log ((n:ℝ)+1)⌉₊
  let s := (d+1)*n^2
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := by linarith
  have hn1 : 0<(n:ℝ)+1 := by positivity
  have hl0 : 0≤Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
  have hl : 1/2≤Real.log (n:ℝ) := by
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at H; linarith only [H,Real.log_le_log (by norm_num : 0<(2:ℝ)) hn']
  have hdl : 6*Real.log ((n:ℝ)+1)≤(d:ℝ) := Nat.le_ceil _
  have hdu : (d:ℝ)≤6*Real.log ((n:ℝ)+1)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hlog : Real.log ((n:ℝ)+1)≤2*Real.log (n:ℝ) := by
    have H := Real.log_le_log hn1 (show (n:ℝ)+1≤(n:ℝ)^2 by nlinarith [sq_nonneg ((n:ℝ)-2)])
    simpa [Real.log_pow] using H
  have hs : (s:ℝ)=((d:ℝ)+1)*(n:ℝ)^2 := by dsimp [s]; push_cast; rfl
  have h4 : 4≤s := by dsimp [s]; nlinarith [Nat.mul_le_mul_right (n^2) (Nat.le_add_left 1 d)]
  have hδ : vinogradovWeight n*Real.exp (-(d:ℝ)) ≤ 1/64 := by
    have he := Real.exp_le_exp.mpr (neg_le_neg hdl)
    rw [Real.exp_neg,Real.exp_neg,show (6:ℝ)=((6:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hn1] at he
    unfold vinogradovWeight
    rw [Real.exp_neg]
    apply (mul_le_mul_of_nonneg_left he (by positivity : 0≤(n:ℝ)*(n+1)/2)).trans
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos hn1 6)).mpr
    have hx : (3:ℝ)^4≤((n:ℝ)+1)^4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    nlinarith only [mul_le_mul_of_nonneg_right hx (sq_nonneg ((n:ℝ)+1)),hn0.le]
  refine ⟨s,h4,?_,Real.exp (200*((d:ℝ)+2)^3*(n:ℝ)^4),Real.exp_pos _,?_⟩
  · rw [hs]
    have H : (d:ℝ)+1≤16*Real.log n := by linarith only [hl,hdu,hlog]
    linarith only [mul_le_mul_of_nonneg_right H (sq_nonneg (n:ℝ))]
  · intro N hN
    apply (vinogradov_mean_value_degree_multiple hn hN d).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    dsimp only [vinogradovMeanExponent,vinogradovWeight,s] at *
    linarith only [hδ]

private theorem polynomialWeylSum_power_bound {d s N Y : ℕ} (P : ℝ[X]) (hP : P.natDegree≤d+2)
    (hN : 1≤N) (hs : 1≤s) (hY : 1≤Y) {C A β : ℝ} (hC : 0<C) (hA : 0≤A)
    (hlarge : A+2*Y≤‖polynomialWeylSum P N‖) (hβ : 0≤β) (hβ' : β≤1/4)
    (hPY : (N:ℝ)^(63/64:ℝ)≤2*Y) {a : ℤ} {q : ℕ}
    (hq : 1≤q) (hcop : a.natAbs.Coprime q) (hθ : |P.coeff (d+2)-(a:ℝ)/q|≤1/(q:ℝ)^2)
    (hl : (N:ℝ)^β≤q) (hu : (q:ℝ)≤(N:ℝ)^(((d+1:ℕ):ℝ)+1-β))
    (hJ : vinogradovJ s (d+1) N ≤ C*(N:ℝ)^(2*(s:ℝ)-((d+1:ℕ):ℝ)*(((d+1:ℕ):ℝ)+1)/2+1/64)) :
    let n := ((d+1:ℕ):ℝ)
    let D := 2+64*(n+1)
    let K := 6*(s:ℝ)+18*((n+1)*D+2*D+3*(n+1)*s)
    A^(4*s)≤(C*(3*(s:ℝ))^d*K)*(N:ℝ)^(4*(s:ℝ)-β+3/64) := by
  intro n D K
  let p := (N:ℝ)
  let E := 2*(s:ℝ)-n*(n+1)/2+1/64
  let V := (d:ℝ)*(d+1)/2
  let G := n-β+1/32
  let I := ∏ j : Fin d, (2*(s*N^(j.val+1):ℕ)+1:ℝ)
  let L := 2*(s:ℝ)*p^n+1
  have hpn : 1≤p := by dsimp [p]; exact_mod_cast hN
  have hp0 : 0<p := by linarith
  have hs' : (1:ℝ)≤s := by exact_mod_cast hs
  have hK : 0≤K := by dsimp [K,D,n]; positivity
  have hQ : 0<(q:ℝ) := by exact_mod_cast hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hU : 0≤Real.log (2*(q:ℝ)) := Real.log_nonneg (by linarith)
  have HK := vinogradov_top_kernel_window hpn (show 1≤n by dsimp [n]; simp) hs' hβ hβ' hPY hl hu
  let T := L+18*(((n+1)*Y+q)*Real.log (2*(q:ℝ))+(n+1)*Y*L/q)
  change T≤Y*K*p^G at HK
  have HW := polynomialWeylSum_shift_bound (s:=s) P hP N Y hA hlarge hq hcop hθ
  have hW : (Y:ℝ)^2*A^(4*s) ≤ p^(2*s)*vinogradovJ s (d+1) N*I*Y*T := by
    simpa only [p,I,L,T,n,Fin.val_last,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      Nat.cast_pow,←Real.rpow_natCast (N:ℝ) (d+1),Fin.val_castSucc,mul_assoc,add_assoc,one_add_one_eq_two] using HW
  have hv : I≤(3*(s:ℝ))^d*p^V := vinogradov_lower_frequency_volume d hs hN
  have hz : 0≤I := by dsimp [I]; positivity
  have hT : 0≤T := by dsimp [T,L]; positivity
  have hj0 := vinogradovJ_nonneg s (d+1) N
  have hp := (Real.rpow_pos_of_pos hp0 E).le
  have hy0 : 0<(Y:ℝ) := by exact_mod_cast hY
  have hres : (Y:ℝ)^2*A^(4*s) ≤
      p^(2*s)*(C*p^E)*((3*(s:ℝ))^d*p^V)*Y*(Y*K*p^G) := by
    apply hW.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hJ (by positivity)) hv hz (by positivity)) hy0.le) HK hT (by positivity)
  have he : (2*(s:ℝ))+E+V+G=4*(s:ℝ)-β+3/64 := by dsimp [E,V,G,n]; push_cast; ring
  have hres' : (Y:ℝ)^2*A^(4*s) ≤ (Y:ℝ)^2*((C*(3*(s:ℝ))^d*K)*p^(4*(s:ℝ)-β+3/64)) := by
    apply hres.trans_eq
    have hh : p^(4*(s:ℝ)-β+3/64) = p^(2*s)*p^E*p^V*p^G := by
      rw [←he,Real.rpow_add hp0 _ G,Real.rpow_add hp0 _ V,Real.rpow_add hp0 _ E]
      congr 3
      rw [←Real.rpow_natCast p (2*s)]; push_cast; rfl
    rw [hh]; ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hy0)).mp hres'

private theorem weylWindow_root {A P M β : ℝ} {s : ℕ} (hM : 0≤M) (hP : 0<P)
    (hs : 1≤s) (h : A^(4*s)≤M*P^(4*(s:ℝ)-β+3/64)) :
    A ≤ (1+M)*P^(1-(β-3/64)/(4*(s:ℝ))) := by
  have hs0 : 0<(s:ℝ) := by exact_mod_cast hs
  apply le_of_pow_le_pow_left₀ (n:=4*s) (by omega) (by positivity)
  rw [mul_pow,←Real.rpow_natCast (P^(1-(β-3/64)/(4*(s:ℝ)))) (4*s),←Real.rpow_mul hP.le]
  have he : (1-(β-3/64)/(4*(s:ℝ)))*((4*s:ℕ):ℝ)=4*(s:ℝ)-β+3/64 := by
    push_cast; field_simp; ring
  rw [he]
  have hM' : M≤(1+M)^(4*s) := by
    apply (show M≤1+M by linarith).trans
    simpa using pow_le_pow_right₀ (show 1≤1+M by linarith) (show 1≤4*s by omega)
  exact h.trans (mul_le_mul_of_nonneg_right hM' (Real.rpow_pos_of_pos hP _).le)

/-- A single denominator-window estimate, uniform in `1/10 ≤ β ≤ 1/4`.
The degree-dependent constant is independent of the coefficients and `β`. -/
theorem vinogradov_weyl_denominator_window {n : ℕ} (hn : 2≤n) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ[X]) (N : ℕ) {β : ℝ} {a : ℤ} {q : ℕ},
      P.natDegree≤n+1 → 1≤N → 1/10≤β → β≤1/4 → 1≤q → a.natAbs.Coprime q →
      |P.coeff (n+1)-(a:ℝ)/q|≤1/(q:ℝ)^2 → (N:ℝ)^β≤q → (q:ℝ)≤(N:ℝ)^((n:ℝ)+1-β) →
      ‖polynomialWeylSum P N‖ ≤ C*(N:ℝ)^(1-(β-3/64)/(64*(n:ℝ)^2*Real.log n)) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  let n := d+1
  obtain ⟨s,h4,hsu,C,hC,H⟩ := exists_vinogradov_weyl_moment hn
  let D := 2+64*((n:ℝ)+1)
  let K := 6*(s:ℝ)+18*(((n:ℝ)+1)*D+2*D+3*((n:ℝ)+1)*s)
  let M := C*(3*(s:ℝ))^d*K
  have hM : 0≤M := by dsimp [M,K,D]; positivity
  have hs : 0<s := by omega
  have hs' : 0<(s:ℝ) := by positivity
  have h4' : (4:ℝ)≤s := by exact_mod_cast h4
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := by linarith
  have hlog : 0<Real.log n := Real.log_pos (by linarith)
  refine ⟨4+2*(1+M),by positivity,?_⟩
  intro P N β a q hdeg hN hβ hβ' hq hcop hθ hlo hup
  let p := (N:ℝ)
  have hp : 1≤p := by dsimp [p]; exact_mod_cast hN
  have hp0 : 0<p := by linarith
  let κ := (β-3/64)/(4*(s:ℝ))
  let γ := (β-3/64)/(64*(n:ℝ)^2*Real.log n)
  have hγκ : γ≤κ := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    change (s:ℝ)≤16*(n:ℝ)^2*Real.log n at hsu; linarith only [hsu]
  have hκ : κ≤1/64 := by apply (div_le_iff₀ (by positivity)).mpr; linarith only [hβ',h4']
  have hpow := Real.rpow_le_rpow_of_exponent_le hp (sub_le_sub_left hγκ 1)
  obtain ⟨Y,hY,hY',hPY⟩ := exists_weyl_shift_length hp
  let W := ‖polynomialWeylSum P N‖
  change W≤(4+2*(1+M))*p^(1-γ)
  by_cases hsmall : W≤4*Y
  · have hp' := Real.rpow_le_rpow_of_exponent_le hp (show (63/64:ℝ)≤1-γ by linarith)
    have hh := hY'.trans hp'
    apply hsmall.trans
    exact mul_le_mul (by linarith) hh (Nat.cast_nonneg Y) (by positivity)
  · have hA : 0≤W/2 := by dsimp [W]; positivity
    have he : W/2+2*Y≤W := by linarith only [lt_of_not_ge hsmall]
    have hw := polynomialWeylSum_power_bound P hdeg hN hs hY hC hA he (by linarith : 0≤β)
      hβ' hPY hq hcop hθ hlo hup (H hN)
    change (W/2)^(4*s)≤M*p^(4*(s:ℝ)-β+3/64) at hw
    have hh := weylWindow_root hM hp0 hs hw
    change W/2≤(1+M)*p^(1-κ) at hh
    have hH := hh.trans (mul_le_mul_of_nonneg_left hpow (by linarith : 0≤1+M))
    linarith only [hH,(Real.rpow_pos_of_pos hp0 (1-γ)).le]

/-- The quarter-power denominator window, with Vinogradov's classical
`1/(400 n² log n)` saving for degree `n+1`. -/
theorem vinogradov_weyl_quarter_window {n : ℕ} (hn : 2≤n) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ[X]) (N : ℕ) {a : ℤ} {q : ℕ},
      P.natDegree≤n+1 → 1≤N → 1≤q → a.natAbs.Coprime q →
      |P.coeff (n+1)-(a:ℝ)/q|≤1/(q:ℝ)^2 → (N:ℝ)^(1/4:ℝ)≤q → (q:ℝ)≤(N:ℝ)^((n:ℝ)+1-1/4) →
      ‖polynomialWeylSum P N‖ ≤ C*(N:ℝ)^(1-1/(400*(n:ℝ)^2*Real.log n)) := by
  obtain ⟨C,hC,H⟩ := vinogradov_weyl_denominator_window hn
  refine ⟨C,hC,?_⟩
  intro P N a q hP hN hq hcop hθ hlo hu
  apply (H P N hP hN (by norm_num : (1/10:ℝ)≤1/4) le_rfl hq hcop hθ hlo hu).trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) _) hC.le
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hl : 0<Real.log n := Real.log_pos (by linarith)
  apply sub_le_sub_left _ 1
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_nonneg (sq_nonneg (n:ℝ)) hl.le]

end AnalyticNumberTheory.ExponentialSums
