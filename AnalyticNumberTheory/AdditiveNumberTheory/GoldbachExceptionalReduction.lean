import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachAsymptotic

/-!
# Removing exceptional denominators in ternary Goldbach integrals

Only the actual cubic integrals on the exceptional arcs need a separate
estimate. The lost arithmetic main terms form a tail of an absolutely
convergent series and cost at most a constant times the inverse square root
of the exceptional conductor.
-/

noncomputable section
open Finset MeasureTheory Real
open scoped Classical ArithmeticFunction.Moebius
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Absolute arithmetic mass of all multiples of a conductor among the major denominators. -/
theorem singularTermTernary_exceptional_sum (N M d : ℕ) :
    ∑ q ∈ (Icc 1 M).filter (d∣·), |singularTermTernary q N| ≤ 48 / sqrt d := by
  classical
  let B := (Icc 1 M).filter (d∣·)
  by_cases hd : d=0
  · subst d
    have h : B=∅ := by ext q; simp [B]; omega
    change ∑ q ∈ B, _ ≤ _; rw [h]; simp
  have hd1 : 1≤d := Nat.one_le_iff_ne_zero.mpr hd
  have hp : 0<(d:ℝ) := by exact_mod_cast hd1
  let t (q : ℕ) := if d<q then |singularTermTernary q N| else 0
  have ht (q : ℕ) : 0 ≤ t q := by dsimp only [t]; split_ifs <;> positivity
  have hs : Summable t := (summable_abs_singularTermTernary N).of_nonneg_of_le ht
    (fun q => by dsimp only [t];split_ifs <;> simp)
  have htail := (hs.sum_le_tsum B (fun q _ => ht q)).trans (tsum_tail_abs_singularTermTernary_le hd1 N)
  have hhead : ∑ q ∈ B, (if q=d then |singularTermTernary d N| else 0) ≤ |singularTermTernary d N| := by
    simp only [sum_ite_eq',sum_const_zero,add_zero];split_ifs <;> simp [abs_nonneg]
  have he : ∑ q ∈ B, |singularTermTernary q N| =
      (∑ q ∈ B, if q=d then |singularTermTernary d N| else 0) + ∑ q ∈ B, t q := by
    rw [← sum_add_distrib];apply sum_congr rfl;intro q hq
    have hdq := Nat.le_of_dvd (mem_Icc.mp (mem_filter.mp hq).1).1 (mem_filter.mp hq).2
    by_cases h : q=d
    · simp [h,t]
    · simp [h,t,show d<q by omega]
  have hpow : (d:ℝ)^(-1/2:ℝ) = (sqrt d)⁻¹ := by rw [show (-1/2:ℝ)=-(1/2) by ring,rpow_neg hp.le,←sqrt_eq_rpow]
  have hterm := @abs_singularTermTernary_le d N hd1
  have hle : (d:ℝ)^(-(3:ℝ)/2) ≤ (d:ℝ)^(-1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) (by norm_num)
  change ∑ q ∈ B, _ ≤ _
  rw [he,div_eq_mul_inv,←hpow]
  linarith only [hhead,htail,hterm,hle]

/-- Separating the denominators in a cubic major-arc integral. The term `B`
bounds the sum of norms of the actual integrals over the exceptional arcs. -/
theorem norm_goldbach_major_exceptional_le {M N d : ℕ} (hM : 1≤M) {Q D B : ℝ}
    (hMQ : 2*(M:ℝ)≤Q) (hD : 0≤D)
    (hgood : ∀ q∈Icc 1 M, ¬d∣q → ∀ a∈coprimeResidues q, ∀ α∈majorArc q a Q,
      ‖primeExpSum N α - (μ q:ℂ)/q.totient*mainExpSum N (α-a/q)‖≤D)
    (hbad : ∑ q ∈ (Icc 1 M).filter (d∣·), ∑ a ∈ coprimeResidues q,
      ‖∫ α in majorArc q a Q, primeExpSum N α^3*e (-α*N)‖ ≤ B) :
    ‖majorArcIntegral (fun α => primeExpSum N α^3*e (-α*N)) M Q -
      (goldbachTernarySingularSeries N:ℂ)*((N-1).choose 2:ℕ)‖ ≤
      ((∑ q∈Icc 1 M, (q.totient:ℝ)*(D*(43*N^2)*(2/(q*Q)))) +
        (2*Q^2*M*sqrt M+32*(M:ℝ)^(-1/2:ℝ)*((N-1).choose 2:ℕ))) +
      (B+(48/sqrt d)*((N-1).choose 2:ℕ)) := by
  classical
  let S := Icc 1 M
  let F (q : ℕ) := ∑ a∈coprimeResidues q, ∫ α in majorArc q a Q, primeExpSum N α^3*e (-α*N)
  let W (q : ℕ) := (singularTermTernary q N:ℂ)*((N-1).choose 2:ℕ)
  let E (q : ℕ) := (q.totient:ℝ)*(D*(43*N^2)*(2/(q*Q)))
  let C := (((N-1).choose 2:ℕ):ℝ)
  have hQ : 2≤Q := by
    have : (1:ℝ)≤M := by exact_mod_cast hM
    linarith
  have hgood' : ∑ q ∈ S.filter (fun q => ¬d∣q), ‖F q-W q‖ ≤
      (∑ q∈S, E q) + 2*Q^2*M*sqrt M := by
    calc
      _ ≤ ∑ q ∈ S.filter (fun q => ¬d∣q), (E q+2*Q^2*sqrt M) := by
        apply sum_le_sum;intro q hq
        obtain ⟨hI,hn⟩ := mem_filter.mp hq
        obtain ⟨h₁,h₂⟩ := mem_Icc.mp hI
        exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
          (norm_ternary_arc_denominator_error h₁ N (by linarith) (hgood q hI hn))
          (norm_ternary_model_truncation h₁ h₂ N hQ))
      _ ≤ ∑ q ∈ S, (E q+2*Q^2*sqrt M) := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun q _ _ => by dsimp [E];positivity)
      _ = _ := by simp [S,sum_add_distrib,nsmul_eq_mul];ring
  have hbad' : ∑ q ∈ S.filter (d∣·), ‖F q-W q‖ ≤ B+(48/sqrt d)*C := by
    calc
      _ ≤ ∑ q ∈ S.filter (d∣·), ((∑ a∈coprimeResidues q,
          ‖∫ α in majorArc q a Q, primeExpSum N α^3*e (-α*N)‖)+|singularTermTernary q N| * C) := by
        apply sum_le_sum;intro q _
        apply (norm_sub_le _ _).trans
        exact add_le_add (norm_sum_le ..) (by simp [W,C,Real.norm_eq_abs])
      _ ≤ _ := by
        rw [sum_add_distrib,←sum_mul]
        exact add_le_add hbad (mul_le_mul_of_nonneg_right (singularTermTernary_exceptional_sum N M d) (by positivity))
  have hrest : ‖(∑ q ∈ S, W q) - (goldbachTernarySingularSeries N:ℂ)*((N-1).choose 2:ℕ)‖ ≤
      32*(M:ℝ)^(-1/2:ℝ)*C := by
    rw [show (∑ q∈S, W q)=(∑ q∈S,(singularTermTernary q N:ℂ))*((N-1).choose 2:ℕ) by rw [sum_mul],
      ← sub_mul,norm_mul,← Complex.ofReal_sum,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (abs_singularSeries_sub_sum_le hM N) (by positivity)
  have hcont : Continuous (fun α : ℝ => primeExpSum N α^3*e (-α*N)) :=
    ((continuous_primeExpSum N).pow 3).mul (continuous_e.comp (continuous_neg.mul continuous_const))
  rw [majorArcIntegral_eq_sum_of_continuous hcont hMQ,show majorArcDenoms (M:ℝ)=S by simp [S,majorArcDenoms]]
  change ‖(∑ q∈S,F q)-_‖≤_
  apply (norm_sub_le_norm_sub_add_norm_sub _ (∑ q∈S,W q) _).trans
  rw [←sum_sub_distrib]
  have htotal := (sum_filter_add_sum_filter_not S (d∣·) (fun q => ‖F q-W q‖))
  linarith only [norm_sum_le S (fun q => F q-W q),htotal,hgood',hbad',hrest]

/-- Complementary major-arc parameters for the weighted three-prime problem with a
single possibly exceptional conductor. The case `d = 0` has no exceptional arcs. -/
theorem goldbachTernary_normalized_exceptional {M N d : ℕ} (hM : 1≤M)
    (hNM : 2*(M:ℝ)^2≤N) {D B : ℝ} (hD : 0≤D)
    (hgood : ∀ q∈Icc 1 M, ¬d∣q → ∀ a∈coprimeResidues q, ∀ α∈majorArc q a ((N:ℝ)/M),
      ‖primeExpSum N α-(μ q:ℂ)/q.totient*mainExpSum N (α-a/q)‖≤D)
    (hbad : ∑ q∈(Icc 1 M).filter (d∣·), ∑ a∈coprimeResidues q,
      ‖∫ α in majorArc q a ((N:ℝ)/M), primeExpSum N α^3*e (-α*N)‖≤B) :
    |goldbachTernaryWeighted N-goldbachTernarySingularSeries N*((N-1).choose 2:ℕ)|/(N:ℝ)^2 ≤
      86*M^2*(D/N)+34/sqrt M+
        70000*(2/sqrt M+(N:ℝ)^(-(1/5:ℝ)))*(log N)^5 + B/(N:ℝ)^2 + 48/sqrt d := by
  have hm : 1≤(M:ℝ) := by exact_mod_cast hM
  have hm0 : 0<(M:ℝ) := by linarith
  have hn : 0<(N:ℝ) := by nlinarith
  have hMQ : 2*(M:ℝ)≤N/M := (le_div_iff₀ hm0).mpr (by nlinarith only [hNM])
  apply (abs_goldbachTernary_normalized_le_of_major hM hNM hD
    (norm_goldbach_major_exceptional_le hM hMQ hD hgood hbad)).trans
  have hc : (((N-1).choose 2:ℕ):ℝ)≤(N:ℝ)^2 := by
    exact_mod_cast (Nat.choose_le_pow (N-1) 2).trans (Nat.pow_le_pow_left (Nat.sub_le N 1) 2)
  rw [add_div,←add_assoc]
  apply add_le_add le_rfl
  exact (div_le_iff₀ (sq_pos_of_pos hn)).mpr (mul_le_mul_of_nonneg_left hc (by positivity))

end AnalyticNumberTheory.AdditiveNumberTheory
