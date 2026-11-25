import AnalyticNumberTheory.ExponentialSums.VinogradovNonsingular
import Mathlib.Logic.Equiv.Fintype

/-!
# Marking coordinates with distinct residues

When a tuple occupies at least `k` residue classes, choose `k` indices
with distinct residues and put them first by a permutation. The counting
loss only involves the choice of these indices on each side.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem exists_injective_selection {β : Type*} [DecidableEq β] {s k : ℕ} (f : Fin s → β)
    (hk : k≤(univ.image f).card) :
    ∃ e : Fin k ↪ Fin s, Function.Injective (f ∘ e) := by
  classical
  let B := univ.image f
  obtain ⟨u⟩ := Function.Embedding.nonempty_of_card_le (α:=Fin k) (β:=B) (by simpa [B] using hk)
  have h (i : Fin k) : ∃ j, f j=(u i).val := by
    obtain ⟨j,_,hj⟩ := mem_image.mp (u i).property
    exact ⟨j,hj⟩
  choose g hg using h
  have hfg : Function.Injective (f ∘ g) := by
    intro i j hij
    apply u.injective
    exact Subtype.ext ((hg i).symm.trans (hij.trans (hg j)))
  exact ⟨⟨g,hfg.of_comp⟩,hfg⟩

private noncomputable def markingPerm {k s : ℕ} (e : Fin k ↪ Fin (k+s)) : Equiv.Perm (Fin (k+s)) :=
  (Equiv.Perm.exists_extending_pair (Fin.castAdd s) e (Fin.castAdd_injective k s) e.injective).choose

private theorem markingPerm_apply {k s : ℕ} (e : Fin k ↪ Fin (k+s)) (i : Fin k) :
    markingPerm e (Fin.castAdd s i)=e i :=
  (Equiv.Perm.exists_extending_pair (Fin.castAdd s) e (Fin.castAdd_injective k s) e.injective).choose_spec i

/-- The number of nonsingular solutions is bounded by the marked count,
with at most `(k+s)^(2k)` pairs of choices of marked indices. -/
theorem vinogradov_nonsingular_marking_le {p k s : ℕ} (I : Finset ℤ)
    (S : Finset ((Fin (k+s) → ℤ) × (Fin (k+s) → ℤ)))
    (hbox : ∀ z∈S, (∀ i, z.1 i∈I) ∧ (∀ i, z.2 i∈I))
    (hmom : ∀ z∈S, vinogradovMoments k z.1=vinogradovMoments k z.2)
    (hgood : ∀ z∈S, k≤(univ.image (fun i => (z.1 i:ZMod p))).card ∧
      k≤(univ.image (fun i => (z.2 i:ZMod p))).card) :
    S.card ≤ (k+s)^(2*k)*(vinogradovHeadTailPairs (vinogradovDistinctHeads k p I) s I).card := by
  classical
  let E := Fin k ↪ Fin (k+s)
  let V := vinogradovHeadTailPairs (vinogradovDistinctHeads k p I) s I
  let F (e : E) (x : Fin (k+s) → ℤ) :=
    (fun i : Fin k => x (markingPerm e (Fin.castAdd s i)),fun j : Fin s => x (markingPerm e (Fin.natAdd k j)))
  have hF (e : E) (x : Fin (k+s) → ℤ) : Fin.append (F e x).1 (F e x).2=x ∘ markingPerm e := by
    funext i
    exact Fin.addCases (fun j => by simp [F]) (fun j => by simp [F]) i
  have hFinj (e : E) : Function.Injective (F e) := by
    intro x y he
    have hh : x ∘ markingPerm e=y ∘ markingPerm e := by rw [←hF,←hF,he]
    exact (markingPerm e).surjective.injective_comp_right hh
  have hM (e : E) (x : Fin (k+s) → ℤ) :
      vinogradovMoments k (F e x).1+vinogradovMoments k (F e x).2=vinogradovMoments k x := by
    rw [←vinogradovMoments_append,hF]
    funext j
    exact Equiv.sum_comp (markingPerm e) (fun i => x i^(j.val+1))
  let good (e : E) (x : Fin (k+s) → ℤ) := Function.Injective (fun i => (x (e i):ZMod p))
  let U (e : E×E) := S.filter (fun z => good e.1 z.1 ∧ good e.2 z.2)
  have hfib (e : E×E) : (U e).card≤V.card := by
    apply card_le_card_of_injOn (fun z => (F e.1 z.1,F e.2 z.2))
    · intro z hz
      obtain ⟨hz,hgood⟩ := mem_filter.mp hz
      obtain ⟨hx,hy⟩ := hbox z hz
      have hpairs (f : E) (x : Fin (k+s) → ℤ) (hx : ∀ i,x i∈I) (hg : good f x) :
          F f x ∈ vinogradovDistinctHeads k p I ×ˢ vinogradovTuples s I := by
        refine mem_product.mpr ⟨mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => hx _),?_⟩,
          Fintype.mem_piFinset.mpr (fun i => hx _)⟩
        simpa only [F,markingPerm_apply] using hg
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hpairs _ _ hx hgood.1,hpairs _ _ hy hgood.2⟩,
        (hM _ _).trans ((hmom z hz).trans (hM _ _).symm)⟩
    · intro z _ w _ h
      exact Prod.ext (hFinj _ (congrArg Prod.fst h)) (hFinj _ (congrArg Prod.snd h))
  have hsub : S⊆univ.biUnion U := by
    intro z hz
    obtain ⟨e,he⟩ := exists_injective_selection _ (hgood z hz).1
    obtain ⟨f,hf⟩ := exists_injective_selection _ (hgood z hz).2
    exact mem_biUnion.mpr ⟨(e,f),mem_univ _,mem_filter.mpr ⟨hz,he,hf⟩⟩
  have hE : Fintype.card E≤(k+s)^k := by
    simpa [E] using Fintype.card_le_of_injective (fun e : E => (e : Fin k → Fin (k+s))) DFunLike.coe_injective
  calc S.card ≤ _ := (card_le_card hsub).trans card_biUnion_le
       _ ≤ ∑ _e : E×E, V.card := sum_le_sum fun e _ => hfib e
       _ ≤ (k+s)^(2*k)*V.card := by
          simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul]
          apply Nat.mul_le_mul_right
          rw [show 2*k=k+k by omega,pow_add]
          exact Nat.mul_le_mul hE hE

end AnalyticNumberTheory.ExponentialSums
