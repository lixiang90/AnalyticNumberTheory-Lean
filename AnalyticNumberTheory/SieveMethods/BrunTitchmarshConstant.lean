import AnalyticNumberTheory.SieveMethods.SelbergSharpInterval
import AnalyticNumberTheory.SieveMethods.SelbergMonotonicity

/-!
# The Brun–Titchmarsh coefficient two for large interval-to-modulus ratios

Selberg's translation principle removes the primes dividing the modulus
from the analytic part of the estimate. Thus the threshold is absolute,
uniform in the initial point, the modulus and the residue.
-/

open Filter Finset Real
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

/-- Selberg's unrestricted weights give an upper bound uniform in the modulus.
The initial z accounts for small primes omitted before translating the remaining candidates. -/
theorem brun_titchmarsh_selberg_monotonicity {x y z : ℝ} {q a : ℕ} (hx : 0≤x) (hy : 0<y)
    (hq : 1≤q) (hz : 1≤z) :
    (piAP (x+y) q a-piAP x q a)*(q.totient:ℝ) ≤
      q*(z+(y/q)/selbergDenominator z+(selbergIntervalWeightMass z/selbergDenominator z)^2) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let C := (Ioc ⌊x⌋₊ ⌊x+y⌋₊).filter (fun n : ℕ => n.Prime ∧ n ≡ a [MOD q])
  let Sm := C.filter (fun n : ℕ => (n:ℝ)≤z)
  let Lg := C.filter (fun n : ℕ => z<(n:ℝ))
  let b := a%q
  let A := Lg.image (fun n => n/q)
  let w := (x-(b:ℝ))/q
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hbr : (b:ℝ)<q := by exact_mod_cast Nat.mod_lt a hq
  have hrec (n : ℕ) (hn : n∈Lg) : q*(n/q)+b=n := by
    have h := (mem_filter.mp (mem_filter.mp hn).1).2.2
    rw [show b=n%q from h.symm,add_comm,Nat.mod_add_div]
  have hcard : A.card=Lg.card := by
    dsimp only [A]
    apply card_image_of_injOn
    intro m hm n hn h
    simpa only [hrec m hm,hrec n hn] using congrArg (fun k => q*k+b) h
  have hsplit : C.card=Sm.card+Lg.card := by
    simpa only [Sm,Lg,not_le] using (C.card_filter_add_card_filter_not (fun n : ℕ => (n:ℝ)≤z)).symm
  have hsm : (Sm.card:ℝ)≤z := by
    have hsub : Sm⊆Icc 1 ⌊z⌋₊ := by
      intro n hn
      have h := mem_filter.mp hn
      exact mem_Icc.mpr ⟨(mem_filter.mp h.1).2.1.one_lt.le,Nat.le_floor h.2⟩
    have h := card_le_card hsub
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at h
    exact (show (Sm.card:ℝ)≤(⌊z⌋₊:ℝ) by exact_mod_cast h).trans (Nat.floor_le (by linarith))
  have hI (k : ℕ) (hk : k∈A) : w<k ∧ (k:ℝ)≤w+y/q := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
    have hr : (q:ℝ)*(↑(n/q):ℝ)+b=n := by exact_mod_cast hrec n hn
    have hnl := (Nat.floor_lt hx).mp hl
    have hnu := (Nat.le_floor_iff (by linarith : 0≤x+y)).mp hu
    dsimp [w]
    constructor
    · rw [div_lt_iff₀ hqr]; linarith
    · rw [←add_div,le_div_iff₀ hqr]; linarith
  have hp (k : ℕ) (hk : k∈A) : (q*k+b).Prime ∧ z<(q*k+b:ℕ) := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    rw [hrec n hn]
    exact ⟨(mem_filter.mp (mem_filter.mp hn).1).2.1,(mem_filter.mp hn).2⟩
  have hw : -1≤w := by dsimp [w]; rw [le_div_iff₀ hqr]; linarith
  have H := selberg_progression_interval_bound (a:=b) A hw (div_pos hy hqr) hz hI hp
  change (A.card:ℝ)*q.totient≤q*((y/q)/selbergDenominator z+(selbergIntervalWeightMass z/selbergDenominator z)^2) at H
  rw [hcard] at H
  have hφ : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  have hsmall := mul_le_mul hsm hφ (Nat.cast_nonneg _) (by linarith)
  rw [piAP_sub_eq_card_interval q a hy.le]
  change (C.card:ℝ)*q.totient≤_
  rw [hsplit,Nat.cast_add]
  nlinarith

/-- For all sufficiently large y/q the coefficient is exactly two, with an absolute threshold. -/
theorem brun_titchmarsh_two_eventually :
    ∃ U : ℝ, 1<U ∧ ∀ {x y : ℝ} {q a : ℕ}, 0≤x → 1≤q → U≤y/(q:ℝ) →
      piAP (x+y) q a-piAP x q a ≤ 2*y/(q.totient*log (y/(q:ℝ))) := by
  obtain ⟨Z,hZ⟩ := (eventually_atTop.1 (eventually_selberg_interval_majorant.and (eventually_ge_atTop (1:ℝ))))
  let T := max Z 1
  have hT : 1≤T := le_max_right ..
  refine ⟨4*T^2,by nlinarith [sq_nonneg (T-1)],?_⟩
  intro x y q a hx hq hU
  let u := y/(q:ℝ)
  let z := Real.sqrt u/2
  have hu : 1<u := by change 4*T^2≤u at hU; nlinarith [sq_nonneg (T-1)]
  have hs : (Real.sqrt u)^2=u := Real.sq_sqrt (by linarith)
  have hzT : T≤z := by dsimp [z]; nlinarith [Real.sqrt_nonneg u,sq_nonneg (Real.sqrt u+2*T)]
  obtain ⟨H,hz⟩ := hZ z ((le_max_left ..).trans hzT)
  have hz' : 0<z := by linarith
  have he : 4*z^2=u := by dsimp [z]; nlinarith
  have hl : log u=2*(log z+log 2) := by
    rw [←he,show 4*z^2=(z*2)^2 by ring,Real.log_pow,Real.log_mul hz'.ne' (by norm_num)]; norm_num
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hyd : 0<y := by
    have hh : 1<y/(q:ℝ) := hu
    rw [lt_div_iff₀ hq',one_mul] at hh
    linarith
  have hM := brun_titchmarsh_selberg_monotonicity (a:=a) hx hyd hq hz
  rw [he] at H
  change (piAP (x+y) q a-piAP x q a)*q.totient≤q*(z+u/selbergDenominator z+(selbergIntervalWeightMass z/selbergDenominator z)^2) at hM
  have hfinal := hM.trans (mul_le_mul_of_nonneg_left H hq'.le)
  change _ ≤ 2*y/(q.totient*log u)
  have hlog : 0<log u := Real.log_pos hu
  rw [le_div_iff₀ (mul_pos hφ hlog)]
  have hlog' : 0<log z+log 2 := by linarith
  have hfinal' : (piAP (x+y) q a-piAP x q a)*q.totient*(log z+log 2)≤q*u := by
    rw [←mul_div_assoc] at hfinal
    exact (le_div_iff₀ hlog').mp hfinal
  have hy' : (q:ℝ)*u=y := by dsimp [u]; field_simp
  rw [hl]; nlinarith

end AnalyticNumberTheory.SieveMethods
