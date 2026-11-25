import AnalyticNumberTheory.ExponentialSums.VinogradovConditionedCount
import AnalyticNumberTheory.ExponentialSums.VinogradovMixedMoments

/-!
# Nonsingular moments in a residue class

Hölder's inequality restricts the unmarked coordinates to a common
residue class. Translating that class to zero and dividing by its modulus
gives the shorter Vinogradov mean.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

/-- Tuples of marked coordinates which are pairwise distinct modulo `p`. -/
noncomputable def vinogradovDistinctHeads (k p : ℕ) (I : Finset ℤ) :=
  (vinogradovTuples k I).filter fun x => Function.Injective (fun i => (x i:ZMod p))

/-- Equal moments for two tuples, each split into a marked head and a tail. -/
def vinogradovHeadTailPairs {k : ℕ} (H : Finset (Fin k → ℤ)) (s : ℕ) (B : Finset ℤ) :=
  let P := H ×ˢ vinogradovTuples s B
  (P ×ˢ P).filter fun z => vinogradovMoments k z.1.1+vinogradovMoments k z.1.2 =
    vinogradovMoments k z.2.1+vinogradovMoments k z.2.2

theorem vinogradovMoments_append {k n s : ℕ} (x : Fin n → ℤ) (y : Fin s → ℤ) :
    vinogradovMoments k (Fin.append x y)=vinogradovMoments k x+vinogradovMoments k y := by
  funext j
  simp [vinogradovMoments,Fin.sum_univ_add]

private theorem translated_eq {k n s : ℕ} {x y : Fin n → ℤ} {u v : Fin s → ℤ}
    (h : vinogradovMoments k x+vinogradovMoments k u=vinogradovMoments k y+vinogradovMoments k v) (b : ℤ) :
    vinogradovMoments k (fun i => x i-b)+vinogradovMoments k (fun i => u i-b)=
    vinogradovMoments k (fun i => y i-b)+vinogradovMoments k (fun i => v i-b) := by
  have hh := vinogradovMoments_affine_of_eq (x:=Fin.append x u) (y:=Fin.append y v)
    (by simpa only [vinogradovMoments_append] using h) 1 (-b)
  have he (X : Fin n → ℤ) (Y : Fin s → ℤ) : (fun i => 1*Fin.append X Y i+-b)=
      Fin.append (fun i => X i-b) (fun i => Y i-b) := by
    funext i
    exact Fin.addCases (fun i => by simp [sub_eq_add_neg]) (fun i => by simp [sub_eq_add_neg]) i
  simpa only [he,vinogradovMoments_append] using hh

/-- With all tail variables in one residue class, the marked moment is
bounded by a congruence count times the ordinary shorter mean. -/
theorem vinogradov_marked_residue_le {k s p N m : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : k<p)
    (hN : N≤m*p^k) (r : ZMod p) :
    let I := Icc 1 (N:ℤ)
    let C := I.filter (fun x : ℤ => (x:ZMod p)=r)
    (vinogradovHeadTailPairs (vinogradovDistinctHeads k p I) s C).card ≤
      N^k*(k.factorial*m^k*p^(k*(k-1)/2))*vinogradovSolutionCount s k (N/p+1) := by
  classical
  intro I C
  let b := (r.val:ℤ)-p
  let J := Icc 1 ((N/p+1:ℕ):ℤ)
  let g (v : ℤ) := (v-b)/(p:ℤ)
  have hpz : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have hg (x : ℤ) (hx : x∈C) : g x∈J ∧ (p:ℤ)*g x=x-b := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp (vinogradov_residue_subset N p hp.pos r hx)
    change g ((p:ℤ)*j+b)∈J ∧ (p:ℤ)*g ((p:ℤ)*j+b)=(p:ℤ)*j+b-b
    have he : g ((p:ℤ)*j+b)=j := by dsimp [g]; rw [add_sub_cancel_right,Int.mul_ediv_cancel_left _ hpz]
    rw [he,add_sub_cancel_right]
    exact ⟨hj,rfl⟩
  let A := vinogradovDistinctHeads k p I
  let S := vinogradovHeadTailPairs A s C
  let shift (x : Fin k → ℤ) (i : Fin k) := x i-b
  let tail (u : Fin s → ℤ) (i : Fin s) := g (u i)
  let F (z : ((Fin k → ℤ) × (Fin s → ℤ)) × ((Fin k → ℤ) × (Fin s → ℤ))) :=
    ((shift z.2.1,shift z.1.1),(tail z.1.2,tail z.2.2))
  have hm (z) (hz : z∈S) :
      ((∀ i, z.1.1 i∈I) ∧ Function.Injective (fun i => (z.1.1 i:ZMod p))) ∧
      ((∀ i, z.2.1 i∈I) ∧ Function.Injective (fun i => (z.2.1 i:ZMod p))) ∧
      (∀ i, z.1.2 i∈C) ∧ (∀ i, z.2.2 i∈C) ∧
      vinogradovMoments k z.1.1+vinogradovMoments k z.1.2=vinogradovMoments k z.2.1+vinogradovMoments k z.2.2 := by
    obtain ⟨hxy,he⟩ := mem_filter.mp hz
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    obtain ⟨hx,hu⟩ := mem_product.mp hx
    obtain ⟨hy,hv⟩ := mem_product.mp hy
    exact ⟨⟨Fintype.mem_piFinset.mp (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩,
      ⟨Fintype.mem_piFinset.mp (mem_filter.mp hy).1,(mem_filter.mp hy).2⟩,
      Fintype.mem_piFinset.mp hu,Fintype.mem_piFinset.mp hv,he⟩
  have htail (u v : Fin s → ℤ) (hu : ∀ i, u i∈C) (hv : ∀ i, v i∈C) (he : tail u=tail v) : u=v := by
    funext i
    have hi := congrArg (fun t : ℤ => (p:ℤ)*t) (congrFun he i)
    exact sub_left_inj.mp (((hg _ (hu i)).2.symm.trans hi).trans (hg _ (hv i)).2)
  have hshift (x y : Fin k → ℤ) (h : shift x=shift y) : x=y := by
    funext i; exact sub_left_inj.mp (congrFun h i)
  have hf : Set.InjOn F (↑S : Set _) := by
    intro z hz w hw he
    have hmz := hm z hz
    have hmw := hm w hw
    have hh := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    exact Prod.ext
      (Prod.ext (hshift _ _ (congrArg Prod.snd hh)) (htail _ _ hmz.2.2.1 hmw.2.2.1 (congrArg Prod.fst ht)))
      (Prod.ext (hshift _ _ (congrArg Prod.fst hh)) (htail _ _ hmz.2.2.2.1 hmw.2.2.2.1 (congrArg Prod.snd ht)))
  let W := I.image (fun x => x-b)
  have hW : W.card=N := by
    have hh : W.card=I.card := card_image_of_injective _ (fun _ _ h => sub_left_inj.mp h)
    simpa [I,Int.card_Icc] using hh
  have hb : (S.image F).card≤W.card^k*(k.factorial*m^k*p^(k*(k-1)/2))*vinogradovCountOn s k J := by
    apply vinogradov_conditioned_pairs_le hp hk hkp (-b) W J
    · intro t ht
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
      obtain ⟨hx₁,hx₂⟩ := mem_Icc.mp hx
      exact ⟨by linarith,by linarith [show (N:ℤ)≤(m*p^k:ℕ) by exact_mod_cast hN]⟩
    · intro w hw; obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
      exact ⟨fun i => mem_image_of_mem _ ((hm z hz).2.1.1 i),fun i => mem_image_of_mem _ ((hm z hz).1.1 i)⟩
    · intro w hw; obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
      exact ⟨fun i => (hg _ ((hm z hz).2.2.1 i)).1,fun i => (hg _ ((hm z hz).2.2.2.1 i)).1⟩
    · intro w hw; obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
      intro i j hij
      apply (hm z hz).1.2
      simpa [F,shift] using hij
    · intro w hw j; obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
      have H := hm z hz
      have h := congrFun (translated_eq H.2.2.2.2 b) j
      have ht (u : Fin s → ℤ) (hu : ∀ i,u i∈C) :
          vinogradovMoments k (fun i => u i-b) j = (p:ℤ)^(j.val+1)*vinogradovMoments k (tail u) j := by
        have he (i : Fin s) : u i-b=(p:ℤ)*g (u i) := (hg _ (hu i)).2.symm
        simp only [vinogradovMoments,tail,he,mul_pow,←mul_sum]
      change vinogradovMoments k (shift z.1.1) j+_ = vinogradovMoments k (shift z.2.1) j+_
      simpa only [Pi.add_apply,ht _ H.2.2.1,ht _ H.2.2.2.1,F,shift] using h
  change S.card≤_
  rw [←card_image_of_injOn hf]
  simpa only [hW,J,vinogradovCountOn_interval] using hb

/-- Putting all unmarked tail coordinates into one residue class costs
at most `p^(2s)` in the marked moment. -/
theorem vinogradov_marked_card_le {k s p N m : ℕ} (hp : p.Prime) (hk : 0<k)
    (hs : 0<s) (hkp : k<p) (hN : N≤m*p^k) :
    let I := Icc 1 (N:ℤ)
    (vinogradovHeadTailPairs (vinogradovDistinctHeads k p I) s I).card ≤
      p^(2*s)*(N^k*(k.factorial*m^k*p^(k*(k-1)/2))*vinogradovSolutionCount s k (N/p+1)) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro I
  let A := vinogradovDistinctHeads k p I
  let C (r : ZMod p) := I.filter (fun x : ℤ => (x:ZMod p)=r)
  let f (r : ZMod p) := vinogradovTorusSum k (C r)
  let w (α : Fin k → ℝ) := ‖torusCharSum A (vinogradovMoments k) α‖^2
  let U := N^k*(k.factorial*m^k*p^(k*(k-1)/2))*vinogradovSolutionCount s k (N/p+1)
  have ht (B : Finset ℤ) : ((vinogradovHeadTailPairs A s B).card:ℝ) =
      torusIntegral k (fun α => w α*‖vinogradovTorusSum k B α‖^(2*s)) :=
    matching_product_power_eq A _ B
  have hsum (α : Fin k → ℝ) : ∑ r, f r α=vinogradovTorusSum k I α := by
    dsimp [f,C,vinogradovTorusSum,torusCharSum]
    exact sum_fiberwise I (fun n : ℤ => (n:ZMod p)) (fun x => torusChar k (vinogradovCurve k x) α)
  have h := torusIntegral_weight_norm_sum_pow_le (k:=k) (show 0<2*s by omega) (univ : Finset (ZMod p))
    univ_nonempty f (fun r _ => continuous_torusCharSum ..) w ((continuous_torusCharSum ..).norm.pow 2) (fun _ => sq_nonneg _)
  simp_rw [hsum] at h
  have hlocal (r : ZMod p) : torusIntegral k (fun α => w α*‖f r α‖^(2*s))≤(U:ℝ) := by
    rw [←ht (C r)]
    exact_mod_cast vinogradov_marked_residue_le (s:=s) hp hk hkp hN r
  change (vinogradovHeadTailPairs A s I).card≤p^(2*s)*U
  apply Nat.cast_le (α:=ℝ) |>.mp
  rw [ht]
  apply h.trans
  apply (mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => hlocal r) (by positivity)).trans_eq
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow]
  rw [←mul_assoc,←pow_succ,Nat.sub_add_cancel (by omega : 1≤2*s)]

end AnalyticNumberTheory.ExponentialSums
