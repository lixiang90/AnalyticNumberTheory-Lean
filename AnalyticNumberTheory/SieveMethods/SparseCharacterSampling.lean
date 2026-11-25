import AnalyticNumberTheory.SieveMethods.SparseCharacterBound
import AnalyticNumberTheory.SieveMethods.SparseCharacterGram

/-!
# Sparse hybrid mean squares for characters

Removing the exponential majorant on a dyadic interval costs an absolute
factor. This yields the same constant for all fixed moduli and for all
families of primitive characters with bounded modulus.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
open AnalyticNumberTheory.PrimeDistribution
namespace AnalyticNumberTheory.SieveMethods

private def dyadicUnsmoothing (M n : ℕ) : ℂ :=
  (M:ℂ)^(3/2:ℂ)*(n:ℂ)^(-(3/2):ℂ)*(Real.exp ((n:ℝ)/(2*M)):ℂ)

private lemma unsmoothed_term {M n : ℕ} (hM : 1≤M) (hn : n∈Icc M (2*M))
    (f : ℕ→ℂ) (u : ℂ) :
    dyadicUnsmoothing M n * characterGramVector M f u n =
      (M:ℂ)^u*(f n*(n:ℂ)^(-u)) := by
  have hm : M≠0 := by omega
  have hn₀ : n≠0 := by have := (mem_Icc.mp hn).1;omega
  have hm' : (M:ℂ)≠0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn₀
  have he : (Real.exp ((n:ℝ)/(2*M)):ℂ)*(Real.exp (-(n:ℝ)/(2*M)):ℂ)=1 := by
    rw [←Complex.ofReal_mul,←Real.exp_add];simp [neg_div]
  dsimp only [dyadicUnsmoothing,characterGramVector]
  rw [if_neg hn₀,Complex.ofReal_natCast]
  calc _ = ((M:ℂ)^(3/2:ℂ)*(M:ℂ)^(u-3/2))*((n:ℂ)^(-(3/2):ℂ)*(n:ℂ)^(3/2-u))*
          ((Real.exp ((n:ℝ)/(2*M)):ℂ)*(Real.exp (-(n:ℝ)/(2*M)):ℂ))*f n := by ring
       _ = _ := by rw [he,←Complex.cpow_add _ _ hm',←Complex.cpow_add _ _ hn',
         show 3/2+(u-3/2)=u by ring,show -(3/2)+(3/2-u)= -u by ring];ring

private lemma norm_dyadicUnsmoothing {M n : ℕ} (hM : 1≤M) (hn : n∈Icc M (2*M)) :
    ‖dyadicUnsmoothing M n‖≤Real.exp 1 := by
  obtain ⟨hmn,hnm⟩ := mem_Icc.mp hn
  have hm : 0<M := hM
  have hn₀ : 0<n := hM.trans hmn
  have hm' : 0<(M:ℝ) := by exact_mod_cast hm
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn₀
  rw [dyadicUnsmoothing,norm_mul,norm_mul,Complex.norm_natCast_cpow_of_pos hm,
    Complex.norm_natCast_cpow_of_pos hn₀,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  norm_num only [Complex.neg_re,Complex.div_ofNat_re,Complex.re_ofNat]
  have hh := Real.rpow_le_rpow hm'.le (by exact_mod_cast hmn : (M:ℝ)≤n) (by norm_num : 0≤(3/2:ℝ))
  rw [Real.rpow_neg hn'.le,←div_eq_mul_inv]
  have hdiv := (div_le_one (Real.rpow_pos_of_pos hn' _)).mpr hh
  have hrat : (n:ℝ)/(2*M)≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hnm)
  apply (mul_le_mul hdiv (Real.exp_le_exp.mpr hrat) (Real.exp_nonneg _) zero_le_one).trans_eq
  ring

set_option maxHeartbeats 700000 in
/-- Dyadic sparse sampling retaining the saving from the logarithmic shift.
Any subset of a dyadic interval can serve as the frequency support. -/
theorem sparse_character_dyadic_decay :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D L : ℕ},1≤D →
      CharacterCorrelationFamily F f D → ∀(S : ι→Finset ℂ) {K : ℝ},0≤K →
      (∀i∈F,∀z∈S i,0≤z.im ∧ z.im<L) →
      (∀i∈F,∀j<L,(((S i).filter fun z => ⌊z.im⌋₊=j).card:ℝ)≤K) →
      ∀(u : ℂ→ℂ),(∀i∈F,∀z∈S i,(u z).re∈Set.Icc (0:ℝ) 1 ∧ (u z).im=z.im) →
      ∀{M : ℕ},1≤M → ∀J : Finset ℕ,J⊆Icc M (2*M) → ∀a : ℕ→ℂ,
      let H := (D:ℝ)*((L:ℝ)+2)
      let R := ∑i∈F,((S i).card:ℝ)
      (∑i∈F,∑z∈S i,‖∑n∈J,a n*f i n*(n:ℂ)^(-u z)‖^2) ≤
        C*(K*M+R*Real.sqrt H*(1+Real.log H)*(M:ℝ)^(-(1/(4+Real.log H))))*(∑n∈J,‖a n‖^2) := by
  obtain ⟨A,hA,HA⟩ := sparse_character_gram_decay
  refine ⟨A*(Real.exp 1)^2,by positivity,?_⟩
  intro ι F f D L hD hF S K hK him hcount u hu M hM J hJ a
  dsimp only
  let b (n:ℕ) := a n*dyadicUnsmoothing M n
  have hm : 1≤(M:ℝ) := by exact_mod_cast hM
  have hs (p) (hp:p∈F) (z) (hz:z∈S p) :
      ‖∑ n∈J,a n*f p n*(n:ℂ)^(-u z)‖^2 ≤ ‖∑n∈J,b n*characterGramVector M (f p) (u z) n‖^2 := by
    have ht : ∑n∈J,b n*characterGramVector M (f p) (u z) n =
        (M:ℂ)^(u z)*∑n∈J,a n*f p n*(n:ℂ)^(-u z) := by
      rw [mul_sum];apply sum_congr rfl;intro n hn
      dsimp only [b];rw [mul_assoc,unsmoothed_term hM (hJ hn)];ring
    rw [ht,norm_mul,Complex.norm_natCast_cpow_of_pos (by omega : 0<M),mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (Real.one_le_rpow hm (hu p hp z hz).1.1))
  have he : ∑n∈J,‖b n‖^2≤(Real.exp 1)^2*∑n∈J,‖a n‖^2 := by
    rw [mul_sum];apply sum_le_sum;intro n hn
    dsimp only [b];rw [norm_mul,mul_pow,mul_comm]
    gcongr;exact norm_dyadicUnsmoothing hM (hJ hn)
  let H := (D:ℝ)*((L:ℝ)+2)
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD : (1:ℝ)≤D)
    (by linarith [Nat.cast_nonneg (α:=ℝ) L])
  let R := ∑i∈F,((S i).card:ℝ)
  have hR : 0≤R := sum_nonneg fun _ _ => Nat.cast_nonneg _
  let B := K*M+R*Real.sqrt H*(1+Real.log H)*(M:ℝ)^(-(1/(4+Real.log H)))
  have hB : 0≤B := add_nonneg (mul_nonneg hK (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg H)) (by linarith [Real.log_nonneg hH])) (Real.rpow_nonneg (Nat.cast_nonneg M) _))
  have h := HA hF hD S hK hm him hcount u hu J b
  apply (sum_le_sum (fun p hp => sum_le_sum (hs p hp))).trans (h.trans ?_)
  change A*B*_ ≤ A*(Real.exp 1)^2*B*_
  exact (mul_le_mul_of_nonneg_left he (mul_nonneg hA.le hB)).trans_eq (by ring)

set_option maxHeartbeats 700000 in
/-- Sparse character sampling on dyadic coefficients, for any family with a common
bound on the moduli of its pairwise character correlations. -/
theorem sparse_character_bound_of_correlation :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} {F : Finset ι} {f : ι→ℕ→ℂ} {D L : ℕ},1≤D →
      CharacterCorrelationFamily F f D → SparseCharacterBound F f L ((D:ℝ)*((L:ℝ)+2)) C := by

  obtain ⟨C,hC,HC⟩ := sparse_character_dyadic_decay
  refine ⟨C,hC,?_⟩
  intro ι F f D L hD hF S K hK him hc u hu M hM a
  have hh := HC hD hF S hK him hc u hu hM (Icc M (2*M)) (fun _ h => h) a
  let H := (D:ℝ)*((L:ℝ)+2)
  have hH : 1≤H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD) (by linarith [Nat.cast_nonneg (α:=ℝ) L])
  have hl := Real.log_nonneg hH
  have hdec : (M:ℝ)^(-(1/(4+Real.log H)))≤1 :=
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM : (1:ℝ)≤M) (neg_nonpos.mpr (by positivity))).trans_eq (Real.rpow_zero _)
  have hr : 0≤∑i∈F,((S i).card:ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  apply mul_le_mul_of_nonneg_left (add_le_add le_rfl _) hC.le
  exact mul_le_of_le_one_right (mul_nonneg (mul_nonneg hr (Real.sqrt_nonneg H)) (by linarith)) hdec

/-- The sparse dyadic mean square with a single absolute constant for every fixed
modulus and every cutoff Q in the family of primitive characters. -/
theorem sparse_character_family_mean :
    ∃C : ℝ,0<C ∧
      (∀(q L : ℕ) [NeZero q],SparseCharacterBound (univ : Finset (DirichletCharacter ℂ q))
        (fun χ n => χ n) L ((q:ℝ)*((L:ℝ)+2)) C) ∧
      (∀(Q L : ℕ),1≤Q → SparseCharacterBound (primitiveCharacterFamily Q) (fun p n => p.2 n)
        L ((Q:ℝ)^2*((L:ℝ)+2)) C) := by
  obtain ⟨C,hC,HC⟩ := sparse_character_bound_of_correlation
  refine ⟨C,hC,fun q L _ => HC (NeZero.one_le : 1≤q) (fixed_modulus_correlation_family q),?_⟩
  intro Q L hQ
  simpa only [Nat.cast_pow] using HC (L:=L) (Nat.one_le_pow _ _ hQ) (primitive_correlation_family Q)

end AnalyticNumberTheory.SieveMethods
