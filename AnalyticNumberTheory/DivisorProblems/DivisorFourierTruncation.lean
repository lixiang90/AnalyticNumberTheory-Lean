import AnalyticNumberTheory.DivisorProblems.SharpSawtoothFourier
import AnalyticNumberTheory.DivisorProblems.SawtoothErrors
import AnalyticNumberTheory.ExponentialSums.ShiftedHarmonicSums

/-!
# Variable Fourier truncation in the divisor problem

The cutoff at the divisor `d` is the largest nonnegative integer strictly
less than `d/R`. The discarded Fourier tails are collected according to
the multiple of `d` nearest to `x`.
-/

open Real Complex Finset
open AnalyticNumberTheory.AnalyticTools.Summation AnalyticNumberTheory.ExponentialSums
namespace AnalyticNumberTheory.DivisorProblems

/-- Number of positive Fourier harmonics strictly below `d/R`. -/
noncomputable def divisorFourierCutoff (d : ℕ) (R : ℝ) := ⌈(d:ℝ)/R⌉₊-1

theorem le_divisorFourierCutoff_iff {h d : ℕ} (hh : 0<h) {R : ℝ} (hR : 0<R) :
    h≤divisorFourierCutoff d R ↔ (h:ℝ)*R<d := by
  rw [←lt_div_iff₀ hR,←Nat.lt_ceil]; unfold divisorFourierCutoff; omega

/-- Total error of the variable cutoff, uniformly in the real argument
and in every scale `R≥1`. -/
theorem sum_abs_divisor_sawtooth_truncation {ε : ℝ} (hε : 0<ε) :
    ∃ C>0, ∀ {x R : ℝ},1≤x → 1≤R →
      (∑ d∈Finset.Icc 1 ⌊Real.sqrt x⌋₊,
        |sawtooth (x/d)+sawtoothSineSum (divisorFourierCutoff d R) (x/d)|) ≤
      C*R*(2*x)^ε*(1+Real.log (4+2*x)) := by
  classical
  obtain ⟨C,hC,hdiv⟩ := card_divisors_le_rpow hε
  refine ⟨48*C,by positivity,?_⟩
  intro x R hx hR
  have hx0 : 0<x := by linarith
  have hR0 : 0<R := by linarith
  let S := Finset.Icc 1 ⌊Real.sqrt x⌋₊
  let T := Finset.Icc 1 ⌊2*x⌋₊
  let p (d : ℕ) := d*(round (x/d)).toNat
  let w (n : ℕ) := 1/(1+|(n:ℝ)-x|)
  have hsd {d : ℕ} (hd : d∈S) : 1≤d ∧ (d:ℝ)≤x := by
    have hu := Finset.mem_Icc.mp hd
    exact ⟨hu.1,(Nat.cast_le.mpr hu.2).trans ((Nat.floor_le (Real.sqrt_nonneg _)).trans (by nlinarith only [Real.sq_sqrt hx0.le,Real.one_le_sqrt.mpr hx,mul_nonneg (sub_nonneg.mpr (Real.one_le_sqrt.mpr hx)) (Real.sqrt_nonneg x)]))⟩
  have hq {d : ℕ} (hd : d∈S) : 1≤round (x/d) := by
    obtain ⟨h₁,h₂⟩ := hsd hd
    have hd' : 0<(d:ℝ) := by exact_mod_cast h₁
    have hy := (le_div_iff₀ hd').mpr (by simpa using h₂ : 1*(d:ℝ)≤x)
    have he := (abs_le.mp (abs_sub_round (x/(d:ℝ)))).2
    by_contra! h
    have H : (round (x/d):ℝ)≤0 := by exact_mod_cast (show round (x/d)≤0 by omega)
    linarith
  have hid {d : ℕ} (hd : d∈S) : |(p d:ℝ)-x|=(d:ℝ)*distToInt (x/d) := by
    have hd' : 0<(d:ℝ) := by exact_mod_cast (hsd hd).1
    have hr := Int.toNat_of_nonneg (show 0≤round (x/d) by linarith [hq hd])
    have hr' : ((round (x/d)).toNat:ℝ)=(round (x/d):ℝ) := by exact_mod_cast hr
    have H : x-(p d:ℝ)=(d:ℝ)*(x/d-(round (x/d):ℝ)) := by
      dsimp [p]; push_cast; rw [hr']; field_simp [hd'.ne']
    rw [abs_sub_comm (p d:ℝ),H,abs_mul,abs_of_pos hd']; rfl
  have hmap {d : ℕ} (hd : d∈S) : p d∈T := by
    have ⟨hd',hxd⟩ := hsd hd
    have h₁ : 1≤p d := Nat.mul_pos hd' (by have := hq hd; omega)
    refine Finset.mem_Icc.mpr ⟨h₁,Nat.le_floor ?_⟩
    have h := (le_abs_self ((p d:ℝ)-x)).trans ((hid hd).le.trans
      (mul_le_mul_of_nonneg_left (distToInt_le_half _) (Nat.cast_nonneg d)))
    linarith
  have hfiber {n : ℕ} (hn : n∈T) :
      ((S.filter (fun d => p d=n)).card:ℝ) ≤ C*(2*x)^ε := by
    have hn' := Finset.mem_Icc.mp hn
    have hsub : S.filter (fun d => p d=n) ⊆ n.divisors := by
      intro d hd
      obtain ⟨hd,he⟩ := Finset.mem_filter.mp hd
      exact Nat.mem_divisors.mpr ⟨he ▸ dvd_mul_right d _,by omega⟩
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ((hdiv n hn'.1).trans ?_)
    gcongr
    exact (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by positivity))
  have hnear {d : ℕ} (hd : d∈S) :
      |sawtooth (x/d)+sawtoothSineSum (divisorFourierCutoff d R) (x/d)|≤12*R*w (p d) := by
    let H := divisorFourierCutoff d R
    let y := distToInt (x/d)
    have hy := distToInt_nonneg (x/d)
    have hy' := distToInt_le_half (x/d)
    have hH : (d:ℝ)/R ≤ (H:ℝ)+1 := by
      apply (Nat.le_ceil _).trans
      have hh : ⌈(d:ℝ)/R⌉₊ ≤ H+1 := by dsimp [H,divisorFourierCutoff]; omega
      exact_mod_cast hh
    have hD : (d:ℝ)≤((H:ℝ)+1)*R := (div_le_iff₀ hR0).mp hH
    apply (abs_sawtooth_add_sineSum_le H _).trans
    dsimp only [w]; rw [hid hd, mul_one_div]
    change 6/(1+(H:ℝ)*y)≤12*R/(1+(d:ℝ)*y)
    have hy₀ : 0≤y := hy
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hD hy₀,
      mul_le_mul_of_nonneg_left hy' hR0.le,hR,
      mul_nonneg hR0.le (mul_nonneg (Nat.cast_nonneg H) hy₀)]
  let K : ℕ := ⌈2*x⌉₊
  have hsum : (∑ n∈T,w n)≤4*(1+Real.log (4+2*x)) := by
    let Z := T.image (fun n : ℕ => (n:ℤ))
    have HH := sum_shifted_inv_one_add_abs_le Z (y:=x) (K:=K) (fun n hn => by
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      have hm' := Finset.mem_Icc.mp hm
      have hmm := (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by positivity : 0≤2*x))
      have hK : 2*x≤K := Nat.le_ceil _
      push_cast; apply abs_le.mpr; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) m])
    dsimp only [Z] at HH
    rw [Finset.sum_image (by intro m hm n hn he; exact Int.ofNat.inj he)] at HH
    simp only [Int.cast_natCast] at HH
    apply HH.trans
    have H := Nat.ceil_lt_add_one (by positivity : 0≤2*x)
    have hk : (K:ℝ)+2≤4+2*x := by dsimp [K]; linarith
    gcongr
  calc
    _ ≤ ∑ d∈S,12*R*w (p d) := Finset.sum_le_sum (fun d hd => hnear hd)
    _ = 12*R*(∑ n∈T,((S.filter (fun d => p d=n)).card:ℝ)*w n) := by
      rw [←Finset.mul_sum,←Finset.sum_fiberwise_of_maps_to (fun d hd => hmap hd) (fun d => w (p d))]
      congr 1; apply Finset.sum_congr rfl; intro n hn
      calc _ = ∑ d∈S.filter (fun d => p d=n),w n := Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.mp hd).2])
           _ = _ := by simp
    _ ≤ 12*R*(C*(2*x)^ε*(∑ n∈T,w n)) := by
      rw [Finset.mul_sum T w (C*(2*x)^ε)]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hfiber hn) (by dsimp [w]; positivity))) (by positivity)
    _ ≤ _ := by
      apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)).trans_eq
      ring

end AnalyticNumberTheory.DivisorProblems
