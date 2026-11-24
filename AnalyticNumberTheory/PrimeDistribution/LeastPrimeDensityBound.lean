import AnalyticNumberTheory.PrimeDistribution.LogFreeZeroDensity
import AnalyticNumberTheory.PrimeDistribution.DensityPowerSums
import AnalyticNumberTheory.PrimeDistribution.LeastPrimeFamilyMoments

/-!
# High zero moments from log-free density

For a subfamily of primitive zeros of height at most one, the weighted
moment of the least-prime kernel inherits an exponential saving from a
common lower bound for the scaled zero gap.
-/

noncomputable section

open Finset Complex
open scoped Classical

namespace AnalyticNumberTheory.PrimeDistribution

/-- The conductor scale for the entire family at height one. -/
def linnikScale (Q : ℕ) : ℝ := Real.log (3*(Q:ℝ))

/-- The distance of a zero from the line one in units of the conductor scale. -/
def linnikScaledGap (Q : ℕ) (j : LinnikZeroIndex) : ℝ := (1-j.2.re)*linnikScale Q

/-- The multiplicity used in a least-prime moment. -/
abbrev linnikZeroWeight (j : LinnikZeroIndex) : ℝ := (characterZeroMultiplicity j.1.2 j.2:ℝ)

theorem linnikScale_pos {Q : ℕ} (hQ : 1≤Q) : 0 < linnikScale Q := by
  apply Real.log_pos
  have : 1≤(Q:ℝ) := by exact_mod_cast hQ
  linarith

theorem linnik_zero_level {Q : ℕ} {σ : ℝ} {j : LinnikZeroIndex}
    (hj : j∈linnikZeroFamily Q σ) : 1≤j.1.1 ∧ j.1.1≤Q :=
  mem_Icc.mp (mem_sigma.mp (mem_linnikZeroFamily.mp hj).1).1

theorem linnik_zero_properties {Q : ℕ} {σ : ℝ} {j : LinnikZeroIndex} [NeZero j.1.1]
    (hj : j∈linnikZeroFamily Q σ) :
    j.1.2.IsPrimitive ∧ j.1.2≠1 ∧ DirichletCharacter.LFunction j.1.2 j.2=0 ∧
      0<j.2.re ∧ σ≤j.2.re ∧ j.2.re<1 ∧ |j.2.im|≤1 := by
  obtain ⟨hF,hz⟩ := mem_linnikZeroFamily.mp hj
  exact ⟨(mem_filter.mp (mem_sigma.mp hF).2).2,(mem_nonprincipalDensityFinset j.1.2).mp hz⟩

/-- Each additional block of orders, of length `b log(3Q)`, contributes the
factor `exp(-b r)` when the subfamily has scaled zero gap at least `r`. -/
theorem linnik_zero_moment_of_gap :
    ∃ A > 0, ∃ K > 0, ∀ {Q : ℕ}, 1≤Q → ∀ (S : Finset LinnikZeroIndex),
    S ⊆ linnikZeroFamily Q 0 → ∀ {r b : ℝ} {m : ℕ}, 0≤b →
    (∀ j ∈ S,r≤linnikScaledGap Q j) → (A+1+b)*linnikScale Q ≤ m+1 →
    ∑ j ∈ S,linnikZeroWeight j*‖leastPrimeZeroRatio j.2‖^(m+1) ≤ K*Real.exp (-b*r) := by
  obtain ⟨C,hC,A,hA,HD⟩ := primitiveFamilyZeroCount_log_free
  have hex : Real.exp (-1)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨A,hA,C*Real.exp A/(1-Real.exp (-1)),by positivity,?_⟩
  intro Q hQ S hS r b m hb hr hm
  let L := linnikScale Q
  have hL : 0<L := linnikScale_pos hQ
  have hw (j : LinnikZeroIndex) : 0 ≤ linnikZeroWeight j := Nat.cast_nonneg _
  have hre (j : LinnikZeroIndex) (hj : j∈S) : 0<j.2.re ∧ j.2.re<1 := by
    have hℓ := linnik_zero_level (hS hj)
    let : NeZero j.1.1 := ⟨by omega⟩
    have hd := linnik_zero_properties (hS hj)
    exact ⟨hd.2.2.2.1,hd.2.2.2.2.2.1⟩
  have hcnt (t : ℝ) (ht : 0≤t) :
      (∑ j ∈ S.filter (fun j => linnikScaledGap Q j≤t),linnikZeroWeight j) ≤ C*Real.exp (A*t) := by
    let σ := max 0 (1-t/L)
    have hσ : σ∈Set.Icc (0:ℝ) 1 := ⟨le_max_left ..,max_le (by norm_num) (by linarith [div_nonneg ht hL.le])⟩
    have hsub : S.filter (fun j => linnikScaledGap Q j≤t) ⊆ linnikZeroFamily Q σ := by
      intro j hj
      obtain ⟨hj,hgap⟩ := mem_filter.mp hj
      obtain ⟨hF,hz⟩ := mem_linnikZeroFamily.mp (hS hj)
      have hℓ := linnik_zero_level (hS hj)
      let : NeZero j.1.1 := ⟨by omega⟩
      obtain ⟨hn,hz',hre,_,hr1,ht1⟩ := (mem_nonprincipalDensityFinset j.1.2).mp hz
      refine mem_linnikZeroFamily.mpr ⟨hF,(mem_nonprincipalDensityFinset j.1.2).mpr ⟨hn,hz',hre,?_,hr1,ht1⟩⟩
      apply max_le hre.le
      have hh := (le_div_iff₀ hL).mpr (show (1-j.2.re)*L≤t from hgap)
      linarith
    apply (sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)).trans
    rw [show (∑ j ∈ linnikZeroFamily Q σ,linnikZeroWeight j) = _ from sum_linnikZeroMultiplicity Q σ]
    have hh := HD hQ (T:=1) zero_le_one hσ
    apply hh.trans
    have hV : 0<3*(Q:ℝ) := by positivity
    rw [show (Q:ℝ)*((1:ℝ)+2) = 3*(Q:ℝ) by ring,Real.rpow_def_of_pos hV]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
    change L*(A*(1-σ)) ≤ A*t
    have hs : 1-t/L ≤ σ := le_max_right ..
    have hst := (le_div_iff₀ hL).mp (show 1-σ≤t/L by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left hst hA.le]
  apply le_trans _ (finite_density_exponential_moment S linnikZeroWeight (linnikScaledGap Q)
    hA.le hC.le hb (fun j _ => hw j) (fun j hj => mul_nonneg (sub_nonneg.mpr (hre j hj).2.le) hL.le) hr hcnt)
  apply sum_le_sum; intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j)
  have hz := hre j hj
  calc
    _ ≤ (Real.exp (-(1-j.2.re)))^(m+1) := pow_le_pow_left₀ (norm_nonneg _) (norm_leastPrimeZeroRatio_le_exp hz.1.le hz.2.le) _
    _ ≤ _ := by
      rw [←Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
      dsimp only [linnikScaledGap]
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hz.2.le)]

end AnalyticNumberTheory.PrimeDistribution
