import AnalyticNumberTheory.ExponentialSums.VinogradovAffine
import AnalyticNumberTheory.ExponentialSums.VinogradovCongruences

/-!
# The nonsingular congruence count in Vinogradov's iteration

After translating a common residue class to zero, the remaining coordinates
are divided by the prime. The head variables then satisfy a system of
congruences with successively increasing moduli. For each pair of heads,
the remaining inhomogeneous count is bounded by the homogeneous mean.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem card_pairs_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α×β)) (B : Finset α) (m : ℕ) (hs : ∀ z∈S,z.1∈B)
    (hm : ∀ x∈B, ((S.filter (fun z => z.1=x)).image Prod.snd).card≤m) :
    S.card≤B.card*m := by
  classical
  have h := card_eq_sum_card_fiberwise (show (S:Set (α×β)).MapsTo Prod.fst B from fun z hz => hs z hz)
  rw [h]
  calc _ ≤ ∑ _ ∈ B, m := by
          apply sum_le_sum
          intro x hx
          have hi : Set.InjOn Prod.snd (↑(S.filter (fun z => z.1=x)) : Set (α×β)) := by
            intro z hz w hw he
            exact Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm) he
          rw [←card_image_of_injOn hi]
          exact hm x hx
       _ = _ := by simp

/-- Head pairs are written in the order `(y,x)`: it suffices that `x`
has pairwise distinct residues. The two tail tuples range over `B`. -/
theorem vinogradov_conditioned_pairs_le {p k s m : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : k<p)
    (A : ℤ) (I B : Finset ℤ) (hI : ∀ t∈I, A<t ∧ t≤A+(m*p^k:ℕ))
    (S : Finset (((Fin k → ℤ) × (Fin k → ℤ)) × ((Fin s → ℤ) × (Fin s → ℤ))))
    (hhead : ∀ z∈S, (∀ i, z.1.1 i∈I) ∧ (∀ i, z.1.2 i∈I))
    (htail : ∀ z∈S, (∀ i, z.2.1 i∈B) ∧ (∀ i, z.2.2 i∈B))
    (hsep : ∀ z∈S, Function.Injective (fun i => (z.1.2 i:ZMod p)))
    (heq : ∀ z∈S, ∀ j : Fin k,
      vinogradovMoments k z.1.2 j+(p:ℤ)^(j.val+1)*vinogradovMoments k z.2.1 j =
      vinogradovMoments k z.1.1 j+(p:ℤ)^(j.val+1)*vinogradovMoments k z.2.2 j) :
    S.card ≤ I.card^k*(k.factorial*m^k*p^(k*(k-1)/2))*vinogradovCountOn s k B := by
  classical
  let H := S.image Prod.fst
  let U := vinogradovTuples k I
  have hH : H.card≤I.card^k*(k.factorial*m^k*p^(k*(k-1)/2)) := by
    have hsize : U.card=I.card^k := by simp [U,vinogradovTuples,Fintype.card_piFinset_const]
    rw [←hsize]
    apply card_pairs_le H U _
    · intro xy hxy
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hxy
      exact Fintype.mem_piFinset.mpr (hhead z hz).1
    · intro y _
      let X := (H.filter (fun v => v.1=y)).image Prod.snd
      have hx (x) (h : x∈X) : ∃ z∈S, z.1.1=y ∧ z.1.2=x := by
        obtain ⟨v,hv,rfl⟩ := mem_image.mp h
        obtain ⟨hv,he⟩ := mem_filter.mp hv
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
        exact ⟨z,hz,he,rfl⟩
      apply vinogradov_congruence_box_le hp hk hkp A (vinogradovMoments k y) X
      · intro x h i; obtain ⟨z,hz,_,rfl⟩ := hx x h; exact hI _ ((hhead z hz).2 i)
      · intro x h; obtain ⟨z,hz,_,rfl⟩ := hx x h; exact hsep z hz
      · intro x h j
        obtain ⟨z,hz,hy,rfl⟩ := hx x h
        rw [←hy,Int.modEq_iff_dvd]
        refine ⟨vinogradovMoments k z.2.1 j-vinogradovMoments k z.2.2 j,?_⟩
        change vinogradovMoments k z.1.1 j-vinogradovMoments k z.1.2 j = _
        push_cast
        linarith only [heq z hz j]
  apply (card_pairs_le S H (vinogradovCountOn s k B) (fun z hz => mem_image_of_mem _ hz) ?_).trans
    (Nat.mul_le_mul_right _ hH)
  intro v hv
  obtain ⟨z₀,h₀,rfl⟩ := mem_image.mp hv
  let d := vinogradovMoments k z₀.2.1-vinogradovMoments k z₀.2.2
  apply le_trans (card_le_card (t:=vinogradovShiftedPairs (vinogradovTuples s B) d) ?_)
    (vinogradovShiftedPairs_card_le _ _)
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  obtain ⟨hz,hv⟩ := mem_filter.mp hz
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨Fintype.mem_piFinset.mpr (htail z hz).1,Fintype.mem_piFinset.mpr (htail z hz).2⟩,?_⟩
  funext j
  have h := heq z hz j
  change z.1=z₀.1 at hv
  rw [hv] at h
  change vinogradovMoments k z.2.1 j=vinogradovMoments k z.2.2 j+
    (vinogradovMoments k z₀.2.1 j-vinogradovMoments k z₀.2.2 j)
  apply mul_left_cancel₀ (pow_ne_zero (n:=j.val+1) (by exact_mod_cast hp.ne_zero : (p:ℤ)≠0))
  linarith only [h,heq z₀ h₀ j]

end AnalyticNumberTheory.ExponentialSums
