import AnalyticNumberTheory.DirichletLFunctions.CharacterFamilySecondMoment
import AnalyticNumberTheory.DirichletLFunctions.PeriodicApproximateFunctionalEquation

/-!
# A two-term harmonic sum over the reduced residue classes

The constant is a finite digamma sum. A numerical O(1/x) remainder
is obtained by adding the uniform shifted harmonic estimates.
-/
noncomputable section
open Real Complex Finset Set
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.AnalyticTools.Gamma
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.DirichletLFunctions

def reducedHarmonicConstant (q : ℕ) [NeZero q] : ℝ :=
  -(∑r∈characterUnitIndices q,realDigamma (((r+1:ℕ):ℝ)/q))/q

/-- Weighted reciprocal sum for a character, with the cutoff qx.
The weight is its squared absolute value and hence depends only on q. -/
theorem reduced_harmonic_sum_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 2≤x) :
    |(∑n∈Finset.Icc 1 ⌊(q:ℝ)*x⌋₊,‖χ n‖^2/(n:ℝ))-
      ((q.totient/q:ℝ)*Real.log x+reducedHarmonicConstant q)|≤4*(q.totient/q:ℝ)/x := by
  let S := characterUnitIndices q
  let a := fun r : ℕ => ((r+1:ℕ):ℝ)/q
  let F := fun r : ℕ => ∑m∈range (⌊x-a r⌋₊+1),1/((m:ℝ)+a r)
  let L := ∑n∈Finset.Icc 1 ⌊(q:ℝ)*x⌋₊,‖χ n‖^2/(n:ℝ)
  let Φ := fun r : ZMod q => ((‖χ r‖^2:ℝ):ℂ)
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hw (r : ℕ) : Φ ((r+1:ℕ):ZMod q)=(if IsUnit ((r+1:ℕ):ZMod q) then 1 else 0) := by
    dsimp [Φ];split_ifs with h
    · rw [norm_char_eq_one_of_isUnit χ h];norm_num
    · rw [MulChar.map_nonunit _ h];norm_num
  have hs (r : ℕ) : hurwitzDirectSum (a r) x 1=(F r:ℂ) := by
    unfold F hurwitzDirectSum;rw [Nat.range_succ_eq_Icc_zero,Complex.ofReal_sum];apply sum_congr rfl
    intro n _;push_cast;simp [Complex.cpow_neg_one]
  have hd : dirichletPoly (fun n : ℕ => Φ n) ⌊(q:ℝ)*x⌋₊ 1=(L:ℂ) := by
    unfold dirichletPoly L;rw [Complex.ofReal_sum];apply sum_congr rfl;intro n _
    dsimp [Φ];push_cast;simp [div_eq_mul_inv,Complex.cpow_neg_one]
  have H := periodic_directSum Φ (by linarith : 1≤x) (1:ℂ)
  rw [hd] at H
  have he : L=(q:ℝ)⁻¹*∑r∈S,F r := by
    have hh (r : ℕ) : Φ ((r+1:ℕ):ZMod q)*hurwitzDirectSum (((r+1:ℕ):ℝ)/q) x 1=
        (if IsUnit ((r+1:ℕ):ZMod q) then (F r:ℂ) else 0) := by rw [hw,hs];split_ifs <;>simp
    simp_rw [hh] at H;rw [←sum_filter] at H
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.cpow_neg_one,S,characterUnitIndices] using H
  let c := fun r => realDigamma (a r)
  have hc (r : ℕ) (hr : r∈S) : |F r-Real.log x+c r|≤4/x := by
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    exact shifted_harmonic_floor_remainder ⟨div_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) hq,
      (div_le_one hq).mpr (by exact_mod_cast h)⟩ hx
  have hcard : S.card=q.totient := card_characterUnitIndices q
  have hsum : |∑r∈S,(F r-Real.log x+c r)|≤q.totient*(4/x) := by
    apply (abs_sum_le_sum_abs ..).trans
    apply (sum_le_sum hc).trans_eq
    simp [hcard]
  change |L-_|≤_
  rw [he]
  have hmain : (q:ℝ)⁻¹*∑r∈S,(F r-Real.log x+c r)=
      (q:ℝ)⁻¹*(∑r∈S,F r)-((q.totient/q:ℝ)*Real.log x+reducedHarmonicConstant q) := by
    simp only [sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,hcard]
    dsimp only [reducedHarmonicConstant,c,a,S];ring
  rw [←hmain,abs_mul,abs_of_nonneg (inv_nonneg.mpr hq.le)]
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)).trans_eq;ring

end AnalyticNumberTheory.DirichletLFunctions
