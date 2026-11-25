import AnalyticNumberTheory.ExponentialSums.VinogradovMixedMoments
import AnalyticNumberTheory.ExponentialSums.VinogradovAffine

/-!
# The singular contribution in Vinogradov's recursion

A singular tuple uses fewer than `k` residue classes on at least one side.
The number of residue patterns is bounded by choosing a set of `k−1`
residues, and the mixed moment for each pattern is bounded by a pure moment
on one residue class.
-/

open Finset Real Complex
namespace AnalyticNumberTheory.ExponentialSums

/-- The number of maps whose image uses at most `r` values. -/
theorem card_patterns_with_small_image_le {s : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    {r : ℕ} (hr : r ≤ Fintype.card β) :
    ((univ : Finset (Fin s → β)).filter (fun v => (univ.image v).card≤r)).card ≤
      (Fintype.card β).choose r*r^s := by
  classical
  let U := (univ : Finset β).powersetCard r
  let box (B : Finset β) := Fintype.piFinset (fun _ : Fin s => B)
  have hs : ((univ : Finset (Fin s → β)).filter (fun v => (univ.image v).card≤r)) ⊆ U.biUnion box := by
    intro v hv
    have h := (mem_filter.mp hv).2
    obtain ⟨B,hsub,_,hcard⟩ := exists_subsuperset_card_eq (subset_univ (univ.image v)) h (by simpa using hr)
    exact mem_biUnion.mpr ⟨B,mem_powersetCard.mpr ⟨subset_univ _,hcard⟩,
      Fintype.mem_piFinset.mpr (fun i => hsub (mem_image_of_mem _ (mem_univ i)))⟩
  apply (card_le_card hs).trans ((show (U.biUnion box).card ≤ ∑ B ∈ U, (box B).card from card_biUnion_le).trans ?_)
  apply le_of_eq
  calc (∑ B ∈ U, (box B).card) = ∑ _B ∈ U, r^s := by
            apply sum_congr rfl; intro B hB
            dsimp only [box]; rw [Fintype.card_piFinset_const,(mem_powersetCard.mp hB).2]
       _ = _ := by simp [U]

/-- Matching two independently prescribed families of coordinate supports costs at most
the largest pure moment on any one support. -/
theorem card_mixed_vinogradov_box_le {s k : ℕ} (hs : 0<s)
    (A B : Fin s → Finset ℤ) {J : ℕ}
    (hA : ∀ i, (vinogradovShiftedPairs (Fintype.piFinset (fun _ : Fin s => A i)) (0:Fin k → ℤ)).card ≤ J)
    (hB : ∀ i, (vinogradovShiftedPairs (Fintype.piFinset (fun _ : Fin s => B i)) (0:Fin k → ℤ)).card ≤ J) :
    (((Fintype.piFinset A) ×ˢ (Fintype.piFinset B)).filter (fun z => vinogradovMoments k z.1=vinogradovMoments k z.2)).card ≤ J := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  let f : Fin s ⊕ Fin s → (Fin k → ℝ) → ℂ :=
    Sum.elim (fun i => vinogradovTorusSum k (A i)) (fun i => vinogradovTorusSum k (B i))
  have hf (i) : Continuous (f i) := by cases i <;> exact continuous_torusCharSum ..
  have hcard : Fintype.card (Fin s ⊕ Fin s) = 2*s := by simp; omega
  have hm := torusIntegral_prod_norm_le f hf (H:=(J:ℝ)) (by
    intro i; rw [hcard]; cases i with
    | inl i => change torusIntegral k (fun α => ‖vinogradovTorusSum k (A i) α‖^(2*s)) ≤ _
               rw [vinogradov_box_moment_eq]; exact_mod_cast hA i
    | inr i => change torusIntegral k (fun α => ‖vinogradovTorusSum k (B i) α‖^(2*s)) ≤ _
               rw [vinogradov_box_moment_eq]; exact_mod_cast hB i)
  apply Nat.cast_le (α:=ℝ) |>.mp
  apply le_trans _ hm
  rw [matching_card_eq_torusIntegral]
  apply torusIntegral_mono k
    (Complex.continuous_re.comp ((continuous_torusCharSum _ _).mul (continuous_torusCharSum _ _).star))
    (continuous_finsetProd _ (fun i _ => (hf i).norm))
  intro α
  apply (Complex.re_le_norm _).trans_eq
  simp only [Pi.mul_apply,Pi.star_apply,norm_mul,norm_star,torusCharSum_moments_pi,norm_prod,Fintype.prod_sum_type,f,Sum.elim_inl,Sum.elim_inr]

/-- Singular solutions in an arbitrary finite integer support, bounded by the
pure moment on a single residue and the number of admissible residue patterns. -/
theorem vinogradov_singular_card_le {p s k J : ℕ} [NeZero p] (hs : 0<s) (hk : k-1≤p)
    (B : Finset ℤ) (S : Finset ((Fin s → ℤ)×(Fin s → ℤ)))
    (hbox : ∀ xy∈S, ∀ i, xy.1 i∈B ∧ xy.2 i∈B)
    (hmom : ∀ xy∈S, vinogradovMoments k xy.1=vinogradovMoments k xy.2)
    (hsing : ∀ xy∈S, (univ.image (fun i => (xy.1 i : ZMod p))).card<k ∨
      (univ.image (fun i => (xy.2 i : ZMod p))).card<k)
    (hJ : ∀ r : ZMod p, (vinogradovShiftedPairs (Fintype.piFinset (fun _ : Fin s =>
      B.filter (fun v => (v:ZMod p)=r))) (0:Fin k → ℤ)).card ≤ J) :
    S.card ≤ 2*(p.choose (k-1))*(k-1)^s*p^s*J := by
  classical
  let res (x : Fin s → ℤ) (i : Fin s) : ZMod p := x i
  let bad := (univ : Finset (Fin s → ZMod p)).filter (fun v => (univ.image v).card≤k-1)
  let all := (univ : Finset (Fin s → ZMod p))
  let W := (bad ×ˢ all) ∪ (all ×ˢ bad)
  let R (xy : (Fin s → ℤ)×(Fin s → ℤ)) := (res xy.1,res xy.2)
  have hmap : (S:Set _).MapsTo R W := by
    intro xy hxy
    rcases hsing xy hxy with h | h
    · exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,by exact Nat.le_pred_of_lt h⟩,mem_univ _⟩)
    · exact mem_union_right _ (mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,by exact Nat.le_pred_of_lt h⟩⟩)
  let C (r : ZMod p) := B.filter (fun v : ℤ => (v:ZMod p)=r)
  have hc (u v : Fin s → ZMod p) : (S.filter (fun xy => R xy=(u,v))).card ≤ J := by
    let A (i : Fin s) := C (u i)
    let B' (i : Fin s) := C (v i)
    refine (card_le_card ?_).trans (card_mixed_vinogradov_box_le hs A B' (fun i => hJ (u i)) (fun i => hJ (v i)))
    intro xy hxy
    obtain ⟨hxy,he⟩ := mem_filter.mp hxy
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    refine mem_filter.mpr ⟨mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i =>
      mem_filter.mpr ⟨(hbox xy hxy i).1,congrFun hx i⟩),Fintype.mem_piFinset.mpr (fun i =>
      mem_filter.mpr ⟨(hbox xy hxy i).2,congrFun hy i⟩)⟩,hmom xy hxy⟩
  have hb : bad.card ≤ p.choose (k-1)*(k-1)^s := by
    simpa [bad,ZMod.card] using card_patterns_with_small_image_le (s:=s) (β:=ZMod p) (r:=k-1) (by rwa [ZMod.card])
  have ha : all.card=p^s := by simp [all,ZMod.card]
  have hw : W.card ≤ 2*(p.choose (k-1))*(k-1)^s*p^s := by
    have h := card_union_le (bad ×ˢ all) (all ×ˢ bad)
    simp only [card_product,ha] at h
    exact h.trans (by nlinarith only [Nat.mul_le_mul_right (p^s) hb])
  rw [card_eq_sum_card_fiberwise hmap]
  calc _ ≤ ∑ _z ∈ W, J := sum_le_sum fun z _ => hc z.1 z.2
       _ ≤ _ := by simpa using Nat.mul_le_mul_right J hw

/-- The singular contribution from the interval `[1,N]` in the classical recursion. -/
theorem vinogradov_singular_interval_le {p s k N : ℕ} (hp : 0<p) (hs : 0<s) (hk : k-1≤p)
    (S : Finset ((Fin s → ℤ)×(Fin s → ℤ)))
    (hbox : ∀ xy∈S, ∀ i, xy.1 i∈Icc 1 (N:ℤ) ∧ xy.2 i∈Icc 1 (N:ℤ))
    (hmom : ∀ xy∈S, vinogradovMoments k xy.1=vinogradovMoments k xy.2)
    (hsing : ∀ xy∈S, (univ.image (fun i => (xy.1 i : ZMod p))).card<k ∨
      (univ.image (fun i => (xy.2 i : ZMod p))).card<k) :
    S.card ≤ 2*(p.choose (k-1))*(k-1)^s*p^s*vinogradovSolutionCount s k (N/p+1) := by
  letI : NeZero p := ⟨hp.ne'⟩
  exact vinogradov_singular_card_le hs hk _ S hbox hmom hsing (vinogradovCountOn_residue_le s k N p hp)

end AnalyticNumberTheory.ExponentialSums
