import AnalyticNumberTheory.ExponentialSums.VinogradovMeanValue
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Diagonal solutions of Vinogradov's system

The first `s` power sums determine the multiset of entries of an
`s`-tuple. Thus, when the number of equations is at least the length of
each tuple, all solutions are diagonal up to a permutation.
-/

open Finset MvPolynomial
namespace AnalyticNumberTheory.ExponentialSums

private theorem eval_esymm_eq_of_power_sums {s : ℕ} {R : Type*} [CommRing R]
    (hc : ∀ j : ℕ, 1≤j → j≤s → IsUnit (j:R))
    (x y : Fin s → R)
    (h : ∀ j : ℕ, 1≤j → j≤s → ∑ i,x i^j=∑ i,y i^j) (n : ℕ) (hn : n≤s) :
    aeval x (esymm (Fin s) R n) = aeval y (esymm (Fin s) R n) := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hz : n=0
    · subst n; simp
    have hr (z : Fin s → R) := congrArg (aeval z : MvPolynomial (Fin s) R →ₐ[R] R)
      (mul_esymm_eq_sum (Fin s) R n)
    simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at hr
    apply (hc n (by omega) hn).mul_right_inj.mp
    rw [hr x,hr y]
    congr 1
    apply sum_congr rfl
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := mem_filter.mp hp
    have hp₃ := Finset.mem_antidiagonal.mp hp₁
    rw [ih p.1 hp₂ (by omega)]
    have he : aeval x (psum (Fin s) R p.2) = aeval y (psum (Fin s) R p.2) := by
      simpa [psum] using h p.2 (by omega) (by omega)
    rw [he]

/-- Newton's identities determine the monic polynomial with the entries as roots
whenever the integers through the tuple length are units in the coefficient ring. -/
theorem prod_X_sub_C_eq_of_power_sums {s : ℕ} {R : Type*} [CommRing R]
    (hc : ∀ j : ℕ, 1≤j → j≤s → IsUnit (j:R)) (x y : Fin s → R)
    (h : ∀ j : ℕ, 1≤j → j≤s → ∑ i,x i^j=∑ i,y i^j) :
    (∏ i, (Polynomial.X-Polynomial.C (x i))) = ∏ i, (Polynomial.X-Polynomial.C (y i)) := by
  classical
  let a := univ.val.map x
  let b := univ.val.map y
  have ha : a.card=s := by simp [a]
  have hb : b.card=s := by simp [b]
  have he (n : ℕ) (hn : n≤s) : a.esymm n=b.esymm n := by
    simpa only [aeval_esymm_eq_multiset_esymm,a,b] using eval_esymm_eq_of_power_sums hc x y h n hn
  change ((univ.val.map (fun i => Polynomial.X-Polynomial.C (x i))).prod) = _
  change _ = ((univ.val.map (fun i => Polynomial.X-Polynomial.C (y i))).prod)
  change (univ.val.map ((fun v : R => Polynomial.X-Polynomial.C v) ∘ x)).prod =
    (univ.val.map ((fun v : R => Polynomial.X-Polynomial.C v) ∘ y)).prod
  rw [←Multiset.map_map,←Multiset.map_map]
  change (a.map _).prod = (b.map _).prod
  rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,ha,hb]
  exact sum_congr rfl fun n hn => by rw [he n (by have := mem_range.mp hn; omega)]

/-- Newton's identities recover an unordered tuple from its first power sums. -/
theorem multiset_eq_of_power_sums {s : ℕ} {R : Type*} [Field R] [CharZero R]
    (x y : Fin s → R) (h : ∀ j : ℕ, 1≤j → j≤s → ∑ i,x i^j=∑ i,y i^j) :
    univ.val.map x = univ.val.map y := by
  classical
  rw [← Polynomial.roots_multiset_prod_X_sub_C (univ.val.map x),
    ← Polynomial.roots_multiset_prod_X_sub_C (univ.val.map y)]
  congr 1
  simpa only [Multiset.map_map,Function.comp_def,Finset.prod] using
    prod_X_sub_C_eq_of_power_sums (fun j hj _ => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) x y h

/-- Every solution in the diagonal range is obtained by permuting a tuple,
including when some of its entries coincide. -/
theorem exists_perm_of_equal_power_sums {s : ℕ} (x y : Fin s → ℕ)
    (h : ∀ j : ℕ, 1≤j → j≤s → ∑ i,x i^j=∑ i,y i^j) :
    ∃ e : Equiv.Perm (Fin s), ∀ i, x (e i)=y i := by
  classical
  let X (i : Fin s) := (x i:ℚ)
  let Y (i : Fin s) := (y i:ℚ)
  have he := multiset_eq_of_power_sums Y X (fun j hj hjs => by
    dsimp [X,Y]; exact_mod_cast (h j hj hjs).symm)
  have hc (v : ℚ) : Fintype.card {i // Y i=v} = Fintype.card {i // X i=v} := by
    have hv := congrArg (Multiset.count v) he
    simp only [Multiset.count_map] at hv
    simp only [Fintype.card_subtype,Finset.card,Finset.filter_val]
    simpa only [eq_comm] using hv
  let E (v : ℚ) := Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E,fun i => ?_⟩
  have hi : X (Equiv.ofFiberEquiv E i)=Y i := (E (Y i) ⟨i,rfl⟩).property
  dsimp [X,Y] at hi
  exact_mod_cast hi

/-- The elementary diagonal family supplies `N^s` solutions at every degree. -/
theorem pow_le_vinogradovSolutionCount (s k N : ℕ) :
    N^s ≤ vinogradovSolutionCount s k N := by
  classical
  let P := Fintype.piFinset (fun _ : Fin s => Icc 1 N)
  let S := (P ×ˢ P).filter fun xy =>
    ∀ j : Fin k, ∑ i : Fin s, (xy.1 i:ℕ)^(j.val+1) = ∑ i : Fin s, (xy.2 i:ℕ)^(j.val+1)
  have h := card_le_card_of_injOn (s:=P) (t:=S) (fun x => (x,x))
    (fun x hx => mem_filter.mpr ⟨mem_product.mpr ⟨hx,hx⟩,fun _ => rfl⟩)
    (fun _ _ _ _ hh => congrArg Prod.fst hh)
  simpa [P,S,Fintype.card_piFinset,vinogradovSolutionCount] using h

/-- In the diagonal range the number of solutions is at most `s! N^s`. -/
theorem vinogradovSolutionCount_le_factorial_mul_pow {s k : ℕ} (hsk : s≤k) (N : ℕ) :
    vinogradovSolutionCount s k N ≤ s.factorial*N^s := by
  classical
  let P := Fintype.piFinset (fun _ : Fin s => Icc 1 N)
  let S := (P ×ˢ P).filter fun xy =>
    ∀ j : Fin k, ∑ i : Fin s, (xy.1 i:ℕ)^(j.val+1) = ∑ i : Fin s, (xy.2 i:ℕ)^(j.val+1)
  let F (p : Equiv.Perm (Fin s) × (Fin s → ℕ)) := (p.2,p.2 ∘ p.1)
  have h := card_le_card_of_surjOn (s:=(univ : Finset (Equiv.Perm (Fin s))) ×ˢ P) (t:=S) F (by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hm,hs⟩ := mem_filter.mp hxy
    obtain ⟨e,he⟩ := exists_perm_of_equal_power_sums x y (by
      intro j hj hj'
      have hjk : j-1<k := by omega
      simpa only [Nat.sub_add_cancel hj] using hs (⟨j-1,hjk⟩ : Fin k))
    exact ⟨(e,x),mem_product.mpr ⟨mem_univ _,(mem_product.mp hm).1⟩,Prod.ext rfl (funext he)⟩)
  simpa [P,S,vinogradovSolutionCount,Fintype.card_piFinset,Fintype.card_perm] using h

/-- Sharp order of the Vinogradov mean value when the degree is at least
the number of variables in each tuple. -/
theorem vinogradovJ_diagonal_bounds {s k : ℕ} (hsk : s≤k) (N : ℕ) :
    (N:ℝ)^s ≤ vinogradovJ s k N ∧ vinogradovJ s k N ≤ s.factorial*(N:ℝ)^s := by
  rw [vinogradovJ_eq_card_solutions]
  exact ⟨by exact_mod_cast pow_le_vinogradovSolutionCount s k N,
    by exact_mod_cast vinogradovSolutionCount_le_factorial_mul_pow hsk N⟩

/-- Distinct entries give `s!` different partners for each ordered tuple. -/
theorem factorial_mul_descFactorial_le_vinogradovSolutionCount (s k N : ℕ) :
    s.factorial*N.descFactorial s ≤ vinogradovSolutionCount s k N := by
  classical
  let P := Fintype.piFinset (fun _ : Fin s => Icc 1 N)
  let S := (P ×ˢ P).filter fun xy =>
    ∀ j : Fin k, ∑ i : Fin s, (xy.1 i:ℕ)^(j.val+1) = ∑ i : Fin s, (xy.2 i:ℕ)^(j.val+1)
  let val (a : Fin s ↪ Fin N) (i : Fin s) := (a i).val+1
  let F (p : Equiv.Perm (Fin s) × (Fin s ↪ Fin N)) := (val p.2,val p.2 ∘ p.1)
  have hmem (a : Fin s ↪ Fin N) (i : Fin s) : val a i∈Icc 1 N :=
    mem_Icc.mpr ⟨Nat.succ_pos _,(a i).isLt⟩
  have h := card_le_card_of_injOn (s:=univ) (t:=S) F (by
    rintro ⟨e,a⟩ _
    refine mem_filter.mpr ⟨mem_product.mpr ⟨Fintype.mem_piFinset.mpr (hmem a),
      Fintype.mem_piFinset.mpr (fun i => hmem a (e i))⟩,?_⟩
    intro j
    exact (Equiv.sum_comp e (fun i => val a i^(j.val+1))).symm) (by
    rintro ⟨e,a⟩ _ ⟨f,b⟩ _ he
    have hab : a=b := by
      ext i
      have := congrFun (congrArg Prod.fst he) i
      exact Nat.add_right_cancel this
    subst b
    have hef : e=f := by
      apply Equiv.ext
      intro i
      apply a.injective
      apply Fin.ext
      exact Nat.add_right_cancel (congrFun (congrArg Prod.snd he) i)
    subst f
    rfl)
  simpa [P,S,vinogradovSolutionCount,Fintype.card_perm,Fintype.card_embedding_eq] using h

/-- The leading constant in the diagonal range equals the number of
permutations of the variables. Repeated coordinates contribute lower order. -/
theorem vinogradovJ_diagonal_tendsto {s k : ℕ} (hsk : s≤k) :
    Filter.Tendsto (fun N : ℕ => vinogradovJ s k N/(N:ℝ)^s) Filter.atTop
      (nhds (s.factorial:ℝ)) := by
  have hd : Filter.Tendsto (fun N : ℕ => (N.descFactorial s:ℝ)/(N:ℝ)^s) Filter.atTop (nhds 1) := by
    have h (i : ℕ) : Filter.Tendsto (fun N : ℕ => ((N-i:ℕ):ℝ)/N) Filter.atTop (nhds 1) := by
      have hi := (tendsto_const_nhds.div_atTop (a:=(i:ℝ)) tendsto_natCast_atTop_atTop)
      apply (show Filter.Tendsto (fun N : ℕ => 1-(i:ℝ)/N) Filter.atTop (nhds 1) by
        simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub hi).congr'
      filter_upwards [Filter.eventually_ge_atTop (i+1)] with N hN
      rw [Nat.cast_sub (by omega)]
      have hp : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
      field_simp
    apply (show Filter.Tendsto (fun N : ℕ => ∏ i ∈ range s,((N-i:ℕ):ℝ)/N) Filter.atTop (nhds 1) by
      simpa using tendsto_finsetProd (range s) (fun i _ => h i)).congr
    intro N
    simp [Nat.descFactorial_eq_prod_range,prod_div_distrib]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun N : ℕ => s.factorial*((N.descFactorial s:ℝ)/(N:ℝ)^s))
    (h:=fun _ : ℕ => (s.factorial:ℝ)) (by simpa using hd.const_mul (s.factorial:ℝ)) tendsto_const_nhds
  · filter_upwards with N
    rw [← mul_div_assoc,vinogradovJ_eq_card_solutions]
    exact div_le_div_of_nonneg_right (by exact_mod_cast factorial_mul_descFactorial_le_vinogradovSolutionCount s k N) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN' : 0<(N:ℝ) := by exact_mod_cast hN
    exact (div_le_iff₀ (pow_pos hN' s)).mpr (vinogradovJ_diagonal_bounds hsk N).2

end AnalyticNumberTheory.ExponentialSums
