import AnalyticNumberTheory.PrimeDistribution.LeastPrimeFamilyMoments
import AnalyticNumberTheory.PrimeDistribution.LeastPrimeSubexponential

/-!
# From high moments of Dirichlet zeros to Linnik's bound

A logarithmic moment order makes all truncation errors smaller than the
gap in the zero sum. The resulting prime lies below an absolute power of
the modulus. Finitely many small moduli are absorbed in the leading constant.
-/
noncomputable section
open Finset Real
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

private theorem geometric_error_log_order {r : ℝ} (hr : 0<r) (hr' : r<1) :
    ∃ B : ℝ, 0<B ∧ ∀ {x : ℝ}, 2≤x → ∀ m : ℕ, B*log (3*x)≤m → r^m ≤ 1/x^4 := by
  have hl : 0 < -log r := neg_pos.mpr (log_neg hr hr')
  refine ⟨4/(-log r),by positivity,fun {x} hx m hm => ?_⟩
  have hx' : 0<x := by linarith
  rw [div_mul_eq_mul_div,(div_le_iff₀ hl)] at hm
  have hxlog := Real.log_le_log hx' (show x≤3*x by linarith)
  have he := Real.exp_le_exp.mpr (show log r*(m:ℝ) ≤ -(4*log x) by nlinarith)
  rw [←Real.rpow_def_of_pos hr,Real.rpow_natCast,Real.exp_neg,
    show (4:ℝ)*log x=(4:ℕ)*log x by norm_num,Real.exp_nat_mul,Real.exp_log hx'] at he
  simpa [one_div] using he

private theorem geometric_error_total {q m : ℕ} {E D r κ : ℝ}
    (hq : 2≤(q:ℝ)) (hE : 0<E) (hD : 0<D)
    (hr : r^m≤1/(q:ℝ)^4) (hs : (1/256:ℝ)^m≤1/(q:ℝ)^4)
    (hκ : E+72+D < κ*q) :
    E*r^m+(q:ℝ)*24*log ((q:ℝ)+2)*(1/256:ℝ)^m+
      (q.totient:ℝ)*D*(1/256:ℝ)^m < κ/q := by
  have hq' : 0<(q:ℝ) := by linarith
  have hq2 : 1≤(q:ℝ)^2 := by nlinarith
  have hq3 : (q:ℝ)≤(q:ℝ)^2 := by nlinarith
  have ht : (q.totient:ℝ) ≤ (q:ℝ)^2 := (by exact_mod_cast Nat.totient_le q : (q.totient:ℝ) ≤ q).trans hq3
  have hl := (Real.log_le_sub_one_of_pos (show 0<(q:ℝ)+2 by linarith))
  have hs' : 0≤(1/256:ℝ)^m := by positivity
  have h1 : E*r^m ≤ E/(q:ℝ)^2 := calc
    _ ≤ E*(1/(q:ℝ)^4) := mul_le_mul_of_nonneg_left hr hE.le
    _ ≤ E/(q:ℝ)^2 := by field_simp; nlinarith [mul_nonneg hE.le (sub_nonneg.mpr hq2)]
  have h2 : (q:ℝ)*24*log ((q:ℝ)+2)*(1/256:ℝ)^m ≤ 72/(q:ℝ)^2 := calc
    _ ≤ (q:ℝ)*24*(3*q)*(1/256:ℝ)^m := by gcongr; linarith
    _ ≤ (q:ℝ)*24*(3*q)*(1/(q:ℝ)^4) := by gcongr
    _ = 72/(q:ℝ)^2 := by field_simp; ring
  have h3 : (q.totient:ℝ)*D*(1/256:ℝ)^m ≤ D/(q:ℝ)^2 := calc
    _ ≤ (q:ℝ)^2*D*(1/256:ℝ)^m := by gcongr
    _ ≤ (q:ℝ)^2*D*(1/(q:ℝ)^4) := by gcongr
    _ = D/(q:ℝ)^2 := by field_simp
  have hlast : (E+72+D)/(q:ℝ)^2 < κ/q := by
    rw [div_lt_div_iff₀ (sq_pos_of_pos hq') hq']
    nlinarith only [mul_lt_mul_of_pos_right hκ hq']
  linarith [show (E+72+D)/(q:ℝ)^2= E/(q:ℝ)^2+72/(q:ℝ)^2+D/(q:ℝ)^2 by ring]

/-- Sufficient high-moment zero bound for a uniform power bound on the
least prime in every reduced residue class. -/
theorem leastPrimeAP_polynomial_of_high_moment_zero_sum
    (hZ : ∃ κ>0, ∃ M>0, ∃ q₀ : ℕ, ∀ {q : ℕ}, q₀≤q → ∀ m : ℕ,
      M*log (3*(q:ℝ))≤m →
      (∑ j ∈ linnikZeroFamily q 0,(characterZeroMultiplicity j.1.2 j.2:ℝ)*
        ‖leastPrimeZeroRatio j.2‖^(m+1)) ≤ 1-κ/(q:ℝ)) :
    ∃ C L : ℝ, 0<C ∧ 0<L ∧ ∀ {q a : ℕ} (hq : q≠0) (ha : a.Coprime q),
      (leastPrimeAP hq ha:ℝ) ≤ C*(q:ℝ)^L := by
  obtain ⟨κ,hκ,M₀,hM₀,q₀,hzeros⟩ := hZ
  obtain ⟨D,hD,hcut⟩ := leastPrimeAP_le_of_primitivePrimeMoment
  obtain ⟨E,r,hE,hr,hr',hmom⟩ := primitivePrimeMoment_family_lower
  obtain ⟨Br,_,hBr⟩ := geometric_error_log_order hr hr'
  obtain ⟨Bs,_,hBs⟩ := geometric_error_log_order (show (0:ℝ)<1/256 by norm_num) (by norm_num)
  let M := max M₀ (max 1 (max Br Bs))
  have hM0 : M₀≤M := le_max_left ..
  have hM1 : 1≤M := (le_max_left ..).trans (le_max_right ..)
  have hMr : Br≤M := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have hMs : Bs≤M := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  let N := max (max q₀ 2) (⌈(E+72+D)/κ⌉₊+1)
  let L := 65536*(3*M+2)
  have hL : 0<L := by dsimp [L]; linarith
  obtain ⟨K,hK,hsmall⟩ := leastPrimeAP_le_exp_rpow (ε:=1) (by norm_num)
  let C := max 1 (exp (K*N))
  have hC : 1≤C := le_max_left ..
  refine ⟨C,L,by linarith,hL,fun {q a} hq ha => ?_⟩
  have hq1 : (1:ℝ)≤q := by exact_mod_cast Nat.pos_of_ne_zero hq
  by_cases hN : N≤q
  · letI : NeZero q := ⟨hq⟩
    have hn2 : 2≤N := (le_max_right ..).trans (le_max_left ..)
    have hn0 : q₀≤N := (le_max_left ..).trans (le_max_left ..)
    have hq2 : (2:ℝ)≤q := by exact_mod_cast hn2.trans hN
    have hx : 0<(q:ℝ) := by positivity
    have hlog : 0≤log (3*(q:ℝ)) := Real.log_nonneg (by linarith)
    let m := ⌈M*log (3*(q:ℝ))⌉₊
    have hm : M*log (3*(q:ℝ))≤m := Nat.le_ceil _
    have hord {b : ℝ} (hb : b≤M) : b*log (3*(q:ℝ))≤m :=
      (mul_le_mul_of_nonneg_right hb hlog).trans hm
    have hz := hzeros (hn0.trans hN) m (hord hM0)
    have hM := hmom ha m
    have hcN : ⌈(E+72+D)/κ⌉₊+1≤q := (le_max_right ..).trans hN
    have hcN' : (⌈(E+72+D)/κ⌉₊:ℝ)<q := by exact_mod_cast (by omega : ⌈(E+72+D)/κ⌉₊<q)
    have hkq := (div_lt_iff₀ hκ).mp ((Nat.le_ceil _).trans_lt hcN')
    have herr := geometric_error_total hq2 hE hD (hBr hq2 m (hord hMr)) (hBs hq2 m (hord hMs)) (by linarith : E+72+D<κ*q)
    have hlogsmall : log (q:ℝ)≤(m:ℝ) :=
      (Real.log_le_log hx (show (q:ℝ)≤3*q by linarith)).trans (by simpa using hord hM1)
    have hprime := hcut ha m hlogsmall (by linarith)
    have hlog2 := Real.one_sub_inv_le_log_of_pos (show 0<(2:ℝ) by norm_num)
    have hloglower := Real.log_le_log (show 0<(2:ℝ) by norm_num) hq2
    have hlog3 := Real.log_le_log (show 0<(3:ℝ) by norm_num) (show 3≤(q:ℝ)^2 by nlinarith)
    rw [Real.log_pow] at hlog3
    have hmupper := Nat.ceil_lt_add_one (mul_nonneg (by linarith : 0≤M) hlog)
    change (m:ℝ)<M*log (3*(q:ℝ))+1 at hmupper
    rw [Real.log_mul (by norm_num) hx.ne'] at hmupper
    have hlarge : exp (65536*m)≤(q:ℝ)^L := by
      rw [Real.rpow_def_of_pos hx]; apply Real.exp_le_exp.mpr
      dsimp only [L]; norm_num at hlog2 hlog3
      nlinarith only [hmupper,hlog2,hloglower,mul_le_mul_of_nonneg_left hlog3 (show 0≤M by linarith)]
    exact hprime.trans (hlarge.trans (le_mul_of_one_le_left (Real.rpow_nonneg hx.le _) hC))
  · have hqN : (q:ℝ)≤N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hN))
    have hs := hsmall hq ha
    rw [Real.rpow_one] at hs
    exact hs.trans ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hqN hK.le)).trans
      ((le_max_right ..).trans (le_mul_of_one_le_right (by linarith : 0≤C) (Real.one_le_rpow hq1 hL.le))))

/-- For moduli at least two, the implicit multiplicative constant can be
absorbed into the exponent. -/
theorem leastPrimeAP_power_of_polynomial
    (h : ∃ C L : ℝ, 0<C ∧ 0<L ∧ ∀ {q a : ℕ} (hq : q≠0) (ha : a.Coprime q),
      (leastPrimeAP hq ha:ℝ) ≤ C*(q:ℝ)^L) :
    ∃ A : ℝ, 0<A ∧ ∀ {q a : ℕ} (hq : 2≤q) (ha : a.Coprime q),
      (leastPrimeAP (by omega : q≠0) ha:ℝ) ≤ (q:ℝ)^A := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨2*C+L,by positivity,fun {q a} hq ha => ?_⟩
  have hx : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have hq2 : (2:ℝ)≤q := by exact_mod_cast hq
  have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
  norm_num at hlog2
  have hlog := (Real.log_le_log (show (0:ℝ)<2 by norm_num) hq2)
  have hconst : C ≤ (q:ℝ)^(2*C) := by
    rw [Real.rpow_def_of_pos hx]
    exact (Real.add_one_le_exp C |>.trans' (by linarith : C≤C+1)).trans
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hC.le (show 0≤Real.log (q:ℝ)-1/2 by linarith)]))
  rw [Real.rpow_add hx]
  exact (h (by omega) ha).trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hx.le _))

end AnalyticNumberTheory.PrimeDistribution
