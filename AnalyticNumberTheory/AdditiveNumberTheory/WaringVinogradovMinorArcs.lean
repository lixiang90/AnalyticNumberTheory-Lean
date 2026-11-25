import AnalyticNumberTheory.ExponentialSums.VinogradovWeylMinorArcs
import AnalyticNumberTheory.AdditiveNumberTheory.WaringMinorArcs

/-!
# Vinogradov's minor-arc saving for Waring's problem

For fixed degree `k ≥ 3`, the entire minor arc complementary to
denominators up to `P^β` has a power saving of order `1/(k² log k)`.
The result applies in particular to the fixed-width major arcs with
`β=1/10` used in the diminishing-ranges argument.
-/

open Finset Real Polynomial
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem waringSum_eq_polynomial {k : ℕ} (hk : 1≤k) (N : ℕ) (α : ℝ) :
    waringSum k N α = 1 + ExponentialSums.polynomialWeylSum (monomial k α) N := by
  rw [waringSum_eq_one_add hk]
  congr 1
  unfold ExponentialSums.polynomialWeylSum
  apply sum_bij' (s:=Icc 1 N) (t:=Icc 1 (N:ℤ)) (fun (x:ℕ) _ => (x:ℤ)) (fun (x:ℤ) _ => x.toNat)
  · intro x hx; obtain ⟨h,h'⟩ := mem_Icc.mp hx; apply mem_Icc.mpr; omega
  · intro x hx; obtain ⟨h,h'⟩ := mem_Icc.mp hx; apply mem_Icc.mpr; omega
  · intro x _; simp
  · intro x hx; have := (mem_Icc.mp hx).1; omega
  · intro x _; simp [eval_monomial,e,ExponentialSums.e]

/-- On all denominator windows from the tenth to the quarter power, the
Waring sum saves at least `1/(1600 k² log k)` in the exponent. -/
theorem waringSum_vinogradov_minorArcs {k : ℕ} (hk : 3≤k) :
    ∃ C : ℝ, 0<C ∧ ∀ {P : ℕ}, 2≤P → ∀ {β α : ℝ}, 1/10≤β → β≤1/4 →
      α∈minorArcs ((P:ℝ)^β) ((P:ℝ)^((k:ℝ)-β)) →
      ‖waringSum k P α‖ ≤ C*(P:ℝ)^(1-1/(1600*(k:ℝ)^2*Real.log k)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hn : 2≤n := by omega
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hlogn : 0<Real.log (n:ℝ) := Real.log_pos (by linarith)
  let k := n+1
  have hk' : (3:ℝ)≤k := by exact_mod_cast hk
  have hkr : (k:ℝ)=(n:ℝ)+1 := by dsimp [k]; push_cast; rfl
  have hlogk : 0<Real.log (k:ℝ) := Real.log_pos (by linarith)
  obtain ⟨C,hC,H⟩ := ExponentialSums.vinogradov_weyl_denominator_window hn
  refine ⟨1+C,by positivity,?_⟩
  intro P hP β α hβ hβ' hα
  have hp2 : (2:ℝ)≤P := by exact_mod_cast hP
  have hp1 : (1:ℝ)≤P := by linarith
  have hp0 : (0:ℝ)<P := by linarith
  let Q := (P:ℝ)^β
  let T := (P:ℝ)^((k:ℝ)-β)
  have hQ : 1≤Q := Real.one_le_rpow hp1 (by linarith)
  have hT : 2*Q≤T := by
    have hl : (P:ℝ)≤(P:ℝ)^((k:ℝ)-2*β) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1 (show 1≤(k:ℝ)-2*β by linarith)
    calc _ ≤ Q*(P:ℝ)^((k:ℝ)-2*β) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hp2.trans hl) (by linarith)
         _ = _ := by dsimp [Q,T]; rw [←Real.rpow_add hp0]; congr 1; ring
  obtain ⟨a,q,hl,hu,hcop,happ⟩ := mem_minorArcs_approx hQ hT hα
  have hq : 1≤q := by exact_mod_cast hQ.trans hl.le
  have hq0 : (0:ℝ)<q := by exact_mod_cast hq
  have ha : |α-(a:ℝ)/q|≤1/(q:ℝ)^2 := by apply happ.trans; rw [sq]; gcongr
  have hw := H (monomial k α) P (natDegree_monomial_le _) (by omega) hβ hβ' hq hcop
    (by simpa [k] using ha) hl.le (by simpa only [T,hkr] using hu)
  let γ := 1/(1600*(k:ℝ)^2*Real.log k)
  have h1 : γ≤1 := by
    have hmin := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at hmin
    have hlog : 1/2≤Real.log k := by linarith only [hmin,Real.log_le_log (by norm_num : 0<(2:ℝ)) (by linarith : (2:ℝ)≤k)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hsqr := pow_le_pow_left₀ (by norm_num : 0≤(3:ℝ)) hk' 2
    nlinarith only [mul_le_mul hsqr hlog (by norm_num) (sq_nonneg (k:ℝ))]
  have hγ : γ ≤ (β-3/64)/(64*(n:ℝ)^2*Real.log n) := by
    have hnk : (n:ℝ)≤k := by rw [hkr]; linarith
    have hprod := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg n) hnk 2)
      (Real.log_le_log (by linarith : (0:ℝ)<n) hnk) hlogn.le (sq_nonneg (k:ℝ))
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have H' := mul_le_mul_of_nonneg_right hβ (mul_nonneg (sq_nonneg (k:ℝ)) hlogk.le)
    nlinarith only [H',hprod,mul_nonneg (sq_nonneg (k:ℝ)) hlogk.le]
  rw [waringSum_eq_polynomial (by omega)]
  apply (norm_add_le ..).trans
  simp only [norm_one]
  change 1+_ ≤ (1+C)*(P:ℝ)^(1-γ)
  have hpow := Real.rpow_le_rpow_of_exponent_le hp1 (sub_le_sub_left hγ 1)
  have hOne := Real.one_le_rpow hp1 (sub_nonneg.mpr h1)
  linarith only [hw,mul_le_mul_of_nonneg_left hpow hC.le,hOne]

/-- The fixed-width minor arcs used in the Waring major-arc dissection. -/
theorem waringSum_vinogradov_fixed_minorArcs {k : ℕ} (hk : 3≤k) :
    ∃ C : ℝ, 0<C ∧ ∀ {P : ℕ}, 2≤P → ∀ {α : ℝ},
      α∈minorArcsFixed ((P:ℝ)^(1/10:ℝ)) ((P:ℝ)^((k:ℝ)-1/10)) →
      ‖waringSum k P α‖ ≤ C*(P:ℝ)^(1-1/(1600*(k:ℝ)^2*Real.log k)) := by
  obtain ⟨C,hC,H⟩ := waringSum_vinogradov_minorArcs hk
  refine ⟨C,hC,?_⟩; intro P hP α hα
  exact H hP le_rfl (by norm_num) (minorArcsFixed_subset_minorArcs _ (by positivity) hα)

end AnalyticNumberTheory.AdditiveNumberTheory
