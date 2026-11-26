import AnalyticNumberTheory.RiemannZeta.CenteredPartialFractions

/-! # Summing over distinct zeros with analytic multiplicity -/

noncomputable section

open Filter Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.EntireFunctions

namespace AnalyticNumberTheory.RiemannZeta

/-- Any convergent series in a multiplicity-respecting zero enumeration can be regrouped
over distinct critical-strip zeros, with each summand weighted by the analytic order. -/
theorem ZetaZeroEnumeration.hasSum_distinct (Z : ZetaZeroEnumeration) {f : ℂ → ℂ} {s : ℂ}
    (h : HasSum (fun n => f (Z.zero n)) s) :
    HasSum (fun ρ : CriticalStripZeros => (analyticOrderNatAt riemannZeta (ρ:ℂ) : ℂ)*f ρ) s := by
  classical
  let g (n : ℕ) : CriticalStripZeros := ⟨Z.zero n, Z.mem_strip n⟩
  apply (h.tsum_fiberwise g).congr_fun
  intro ρ
  have hset : g ⁻¹' {ρ} = {n | Z.zero n = (ρ : ℂ)} :=
    Set.ext fun n => Subtype.ext_iff
  have hfin : (g ⁻¹' {ρ}).Finite := by
    rw [hset]
    exact (Z.finite_norm_le ‖(ρ:ℂ)‖).subset fun n hn => by
      change ‖Z.zero n‖ ≤ ‖(ρ:ℂ)‖
      rw [show Z.zero n = (ρ:ℂ) from hn]
  let := hfin.fintype
  have he (n : g ⁻¹' {ρ}) : Z.zero n = (ρ:ℂ) := congrArg Subtype.val (show g n = ρ from n.property)
  simp_rw [he]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Set.fintypeCard_eq_ncard, hset, Z.count_fiber ρ ρ.property]

/-- Centering at zero expresses −ζ'/ζ intrinsically as a sum over the distinct
nontrivial zeros, weighted by their orders, and over the negative even integers. -/
theorem neg_logDeriv_riemannZeta_eq_distinct_centered {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s = -Complex.log (2*(Real.pi:ℂ)) + centeredPole 1 s -
      (∑' ρ : CriticalStripZeros, (analyticOrderNatAt riemannZeta (ρ:ℂ) : ℂ)*centeredPole ρ s) -
      ∑' n, centeredPole (trivialZetaZero n) s := by
  obtain ⟨Z,H⟩ := exists_centered_logDeriv_riemannZeta
  rw [H hs hζ, (Z.hasSum_distinct (f := fun ρ => centeredPole ρ s) (Z.summable_centered s).hasSum).tsum_eq]

end AnalyticNumberTheory.RiemannZeta
