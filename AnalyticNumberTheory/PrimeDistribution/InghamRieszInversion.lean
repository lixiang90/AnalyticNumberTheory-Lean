import AnalyticNumberTheory.PrimeDistribution.ZetaZeroDetector
import AnalyticNumberTheory.DirichletSeries.Perron
import AnalyticNumberTheory.DirichletSeries.Operations

/-!
# Riesz means of the mollified zeta function

A finite Möbius polynomial multiplied by zeta has a Dirichlet coefficient
which vanishes between 2 and the mollifier length. Riesz inversion then
turns a vertical integral into a compactly supported detector.
-/
noncomputable section
open Complex Real Finset MeasureTheory
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

private def mobiusCutoff (X : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n≤X then (μ n:ℂ) else 0,by simp⟩

/-- The Dirichlet coefficient of ζ times the length-X Möbius polynomial. -/
def inghamDetectorCoeff (X : ℕ) : ArithmeticFunction ℂ :=
  mobiusCutoff X*(ζ : ArithmeticFunction ℂ)

theorem inghamDetectorCoeff_eq (X n : ℕ) :
    inghamDetectorCoeff X n = ∑ d∈n.divisors,if d≤X then (μ d:ℂ) else 0 := by
  rw [inghamDetectorCoeff,ArithmeticFunction.coe_mul_zeta_apply]; rfl

theorem inghamDetectorCoeff_small {X n : ℕ} (hn : n≤X) :
    inghamDetectorCoeff X n = if n=1 then 1 else 0 := by
  rw [←zetaDetectorCoeff_of_le hn,inghamDetectorCoeff_eq,zetaDetectorCoeff]
  refine sum_congr rfl fun d _ => ?_
  simp [(Nat.div_le_self ..).trans hn]

theorem norm_inghamDetectorCoeff (X n : ℕ) : ‖inghamDetectorCoeff X n‖≤n.divisors.card := by
  rw [inghamDetectorCoeff_eq]; apply (norm_sum_le ..).trans
  calc _ ≤ ∑ _d∈n.divisors,(1:ℝ) := by
          apply sum_le_sum; intro d _; split_ifs; exact norm_moebius_complex_le d; simp
       _ = _ := by simp

private theorem cutoff_term (X : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (mobiusCutoff X) s n = if n∈Icc 1 X then (μ n:ℂ)*(n:ℂ)^(-s) else 0 := by
  by_cases hn : n=0
  · subst n; simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,←Complex.cpow_neg]
  simp only [mem_Icc,show 1≤n from Nat.pos_of_ne_zero hn,true_and,mobiusCutoff,ArithmeticFunction.coe_mk,ite_mul,zero_mul]

private theorem mollified_series {X : ℕ} {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (inghamDetectorCoeff X) s ∧
    LSeries (inghamDetectorCoeff X) s = riemannZeta s*dirichletPoly (fun d => (μ d:ℂ)) X s := by
  have hm : LSeriesSummable (mobiusCutoff X) s := summable_of_ne_finset_zero (s:=Icc 1 X)
    (fun n hn => by rw [cutoff_term,ite_eq_right hn])
  have hζ : LSeriesSummable (ζ : ArithmeticFunction ℂ) s := by
    change LSeriesSummable (fun n : ℕ => (ζ : ArithmeticFunction ℂ) n) s
    simpa [ArithmeticFunction.natCoe_apply] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have he : LSeries (mobiusCutoff X) s=dirichletPoly (fun d => (μ d:ℂ)) X s := by
    rw [LSeries,tsum_eq_sum (s:=Icc 1 X) (fun n hn => by rw [cutoff_term,ite_eq_right hn])]
    exact sum_congr rfl (fun n hn => by rw [cutoff_term,ite_eq_left hn])
  have hz : LSeries (ζ : ArithmeticFunction ℂ) s=riemannZeta s := by
    change LSeries (fun n : ℕ => (ζ : ArithmeticFunction ℂ) n) s=_
    simpa [ArithmeticFunction.natCoe_apply] using ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  exact ⟨ArithmeticFunction.LSeriesSummable_mul hm hζ,(ArithmeticFunction.LSeries_mul' hm hζ).trans (by rw [he,hz,mul_comm])⟩

private theorem twisted_term (X : ℕ) (ρ w : ℂ) (n : ℕ) :
    LSeries.term (fun n : ℕ => inghamDetectorCoeff X n*(n:ℂ)^(-ρ)) w n =
      LSeries.term (inghamDetectorCoeff X) (ρ+w) n := by
  by_cases hn : n=0
  · subst n; simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,div_eq_mul_inv,div_eq_mul_inv,
    ←Complex.cpow_neg,←Complex.cpow_neg,mul_assoc,←Complex.cpow_add _ _ (by exact_mod_cast hn : (n:ℂ)≠0),neg_add]

/-- Compactly supported Riesz weight on positive integers up to Y. -/
def inghamRieszWeight (k : ℕ) (Y : ℝ) (n : ℕ) : ℝ := (1-n/Y)^k

/-- Integrand on the absolutely convergent line with real part two. -/
def inghamRieszLine (X k : ℕ) (ρ : ℂ) (Y v : ℝ) : ℂ :=
  let w := (2:ℂ)+(v:ℂ)*I
  riemannZeta (ρ+w)*dirichletPoly (fun n => (μ n:ℂ)) X (ρ+w)*(Y:ℂ)^w/rieszDenom k w

/-- The right-hand Mellin integral of the mollified zeta function, with
a Riesz kernel of any positive integral order. The normalization cancels
the factorial in Riesz inversion. -/
theorem ingham_riesz_inversion (X k : ℕ) (hk : 1≤k) {ρ : ℂ} (hρ : 0≤ρ.re) {Y : ℝ} (hY : 0<Y) :
    Integrable (inghamRieszLine X k ρ Y) ∧
    ((k.factorial:ℂ)/(2*π))*(∫ v : ℝ, inghamRieszLine X k ρ Y v) =
      ∑ n∈Icc 1 ⌊Y⌋₊,inghamDetectorCoeff X n*(n:ℂ)^(-ρ)*(inghamRieszWeight k Y n:ℂ) := by
  let a (n : ℕ) := inghamDetectorCoeff X n*(n:ℂ)^(-ρ)
  have hsum : LSeriesSummable a (2:ℂ) := by
    have hre : 1<(ρ+2).re := by rw [Complex.add_re]; norm_num; linarith
    exact ((mollified_series (X:=X) hre).1).congr (fun n => (twisted_term X ρ 2 n).symm)
  have h := riesz_perron_formula hk hY (c:=2) (by norm_num) hsum
  have hz (v : ℝ) : LSeries a ((2:ℂ)+(v:ℂ)*I)=
      riemannZeta (ρ+(2+v*I))*dirichletPoly (fun n => (μ n:ℂ)) X (ρ+(2+v*I)) := by
    have hre : 1<(ρ+(2+v*I)).re := by simp; linarith
    exact (tsum_congr (twisted_term X ρ (2+v*I))).trans (mollified_series (X:=X) hre).2
  let F (v : ℝ) := let w := (2:ℂ)+(v:ℂ)*I
    riemannZeta (ρ+w)*dirichletPoly (fun n => (μ n:ℂ)) X (ρ+w)*(Y:ℂ)^w/rieszDenom k w
  have hYc : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hi (v : ℝ) :
      LSeries a ((2:ℂ)+(v:ℂ)*I)*(Y:ℂ)^((2:ℂ)+(v:ℂ)*I+k)/rieszDenom k ((2:ℂ)+(v:ℂ)*I) =
      (Y:ℂ)^k*F v := by
    dsimp [F]; rw [hz,Complex.cpow_add _ _ hYc,Complex.cpow_natCast]; ring
  simp only [Complex.ofReal_ofNat] at h
  simp_rw [hi] at h; rw [integral_const_mul] at h
  constructor
  · have hI := integrable_LSeries_riesz hk hY (c:=2) (by norm_num) hsum
    simp only [Complex.ofReal_ofNat] at hI
    simp_rw [hi] at hI
    exact (integrable_const_mul_iff (pow_ne_zero k hYc).isUnit F).mp hI
  change (k.factorial:ℂ)/(2*π)*(∫ v,F v)=_
  apply (mul_left_cancel₀ (pow_ne_zero k hYc))
  calc (Y:ℂ)^k*((k.factorial:ℂ)/(2*π)*(∫ v,F v)) =
        (k.factorial:ℂ)*(1/(2*π)*((Y:ℂ)^k*∫ v,F v)) := by ring
       _ = _ := by rw [h,Finset.mul_sum,Finset.mul_sum]; apply sum_congr rfl; intro n hn
                   dsimp only [a,inghamRieszWeight]; push_cast
                   rw [show (Y:ℂ)^k*(inghamDetectorCoeff X n*(n:ℂ)^(-ρ)*(1-(n:ℂ)/Y)^k) =
                     inghamDetectorCoeff X n*(n:ℂ)^(-ρ)*((Y:ℂ)-(n:ℂ))^k by
                       rw [show (Y:ℂ)-(n:ℂ)=(Y:ℂ)*(1-(n:ℂ)/Y) by field_simp, mul_pow]; ring]
                   field_simp [show (k.factorial:ℂ)≠0 by exact_mod_cast Nat.factorial_ne_zero k]

end AnalyticNumberTheory.PrimeDistribution
