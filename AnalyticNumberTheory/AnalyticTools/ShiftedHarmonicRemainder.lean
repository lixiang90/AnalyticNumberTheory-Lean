import AnalyticNumberTheory.AnalyticTools.HarmonicRemainder
import AnalyticNumberTheory.AnalyticTools.Gamma.Basic

/-!
# Shifted harmonic sums and the digamma constant

The tail of the difference between shifted and unshifted terms is
bounded by a telescoping series. In particular the error at a real
cutoff is uniform down to arbitrarily small positive shifts.
-/
open Real Finset
open AnalyticNumberTheory.AnalyticTools.Gamma
namespace AnalyticNumberTheory.AnalyticTools

/-- The shifted harmonic polynomial with exactly N terms differs from
the usual harmonic number by its limiting digamma constant, up to 1/N. -/
theorem shifted_harmonic_finite_error {a : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) {N : ℕ} (hN : 1≤N) :
    |(∑n∈range N,1/((n:ℝ)+a))-(harmonic N:ℝ)+realDigamma a+Real.eulerMascheroniConstant|≤1/(N:ℝ) := by
  let f (n : ℕ) := 1/((n:ℝ)+a)-1/((n:ℝ)+1)
  have hn' : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hf (n : ℕ) : 0≤f n := sub_nonneg.mpr (one_div_le_one_div_of_le
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) ha.1) (by linarith [ha.2]))
  have htel (M : ℕ) : (∑k∈range M,f (k+N))≤1/(N:ℝ)-1/((M:ℝ)+N) := by
    induction M with
    | zero => simp
    | succ M ih =>
      have hp : 0<(M:ℝ)+N := by positivity
      have hh := one_div_le_one_div_of_le hp (show (M:ℝ)+N≤M+N+a by linarith [ha.1])
      rw [sum_range_succ,Nat.cast_succ]
      dsimp only [f] at *
      push_cast at ih ⊢
      rw [show (M:ℝ)+1+N=M+N+1 by ring]
      linarith only [ih,hh]
  have hsum (M : ℕ) : ∑k∈range M,f (k+N)≤1/(N:ℝ) := (htel M).trans
    (sub_le_self _ (by positivity))
  have hs' : Summable (fun k => f (k+N)) := summable_of_sum_range_le (fun k=>hf _) hsum
  have hs := (summable_nat_add_iff N).mp hs'
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail := hs'.tsum_le_of_sum_range_le hsum
  have hdiag := real_digamma_eq_neg_eulerMascheroni_add_tsum (x:=a) (fun m => ne_of_gt (by linarith [ha.1,Nat.cast_nonneg (α:=ℝ) m]))
  have hz : (∑'n : ℕ,(1/((n:ℝ)+1)-1/((n:ℝ)+a)))= -(∑'n : ℕ,f n) := by
    rw [←tsum_neg];apply tsum_congr;intro n;dsimp [f];ring
  rw [hz] at hdiag
  have hpartial : (∑n∈range N,f n)=(∑n∈range N,1/((n:ℝ)+a))-(harmonic N:ℝ) := by
    dsimp [f,harmonic]
    rw [sum_sub_distrib,Rat.cast_sum]
    congr 1
    apply sum_congr rfl;intro n _
    push_cast;ring
  rw [hpartial] at hsplit
  have he : (∑n∈range N,1/((n:ℝ)+a))-(harmonic N:ℝ)+realDigamma a+Real.eulerMascheroniConstant=
      -(∑'k : ℕ,f (k+N)) := by linarith only [hsplit,hdiag]
  rw [he,abs_neg,abs_of_nonneg (tsum_nonneg (fun n => hf _))]
  exact htail

/-- At the real cutoff x the diagonal has constant −ψ(a) and error at
most 4/x, independently of 0<a≤1 and x≥2. -/
theorem shifted_harmonic_floor_remainder {a x : ℝ} (ha : a∈Set.Ioc (0:ℝ) 1) (hx : 2≤x) :
    |(∑n∈range (⌊x-a⌋₊+1),1/((n:ℝ)+a))-Real.log x+realDigamma a|≤4/x := by
  let N := ⌊x-a⌋₊+1
  let y := x-a+1
  have hx' : 0<x := by linarith
  have hxy : x≤y := by dsimp [y];linarith [ha.2]
  have hy : 0<y := hx'.trans_le hxy
  have hN : 1≤N := by dsimp [N];omega
  have hNy : ⌊y⌋₊=N := Nat.floor_add_one (by linarith [ha.2] : 0≤x-a)
  have hNx : x/2≤(N:ℝ) := by
    dsimp [N];push_cast;linarith [Nat.lt_floor_add_one (x-a),ha.2]
  have hN' : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hinv : 1/(N:ℝ)≤2/x := (div_le_div_iff₀ hN' hx').mpr (by linarith)
  have H := shifted_harmonic_finite_error ha hN
  have H' := harmonic_floor_remainder hy
  rw [hNy] at H'
  have hlog : 0≤Real.log y-Real.log x := sub_nonneg.mpr (Real.log_le_log hx' hxy)
  have hlog' : Real.log y-Real.log x≤1/x := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hy hx')
    rw [Real.log_div hy.ne' hx'.ne'] at hh
    apply hh.trans
    rw [sub_le_iff_le_add,div_le_iff₀ hx']
    dsimp [y];field_simp;linarith [ha.1]
  have hyx := one_div_le_one_div_of_le hx' hxy
  let S := ∑n∈range N,1/((n:ℝ)+a)
  change |S-(harmonic N:ℝ)+realDigamma a+Real.eulerMascheroniConstant|≤_ at H
  change |S-Real.log x+realDigamma a|≤_
  rw [abs_le] at H H' ⊢
  have hxinv := one_div_pos.mpr hx'
  simp only [div_eq_mul_inv,one_mul] at H H' hinv hlog' hyx hxinv ⊢
  constructor <;> linarith only [hxinv,H.1,H.2,H'.1,H'.2,hinv,hlog,hlog',hyx]

end AnalyticNumberTheory.AnalyticTools
