import AnalyticNumberTheory.ExponentialSums.VinogradovLowerBounds

/-!
# Inhomogeneous systems of power sums

A prescribed difference of two vectors of power sums occurs no more often
than the zero difference. The estimate follows by counting the fibers of
the two maps to the same lattice.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem card_matching_eq_sum {A C γ : Type*} [DecidableEq γ] (B : Finset γ) (U : Finset A) (V : Finset C) (u : A → γ) (v : C → γ)
      (hu : (U:Set A).MapsTo u B) :
      ((U ×ˢ V).filter fun p => u p.1=v p.2).card =
        ∑ b ∈ B, (U.filter (u · = b)).card*(V.filter (v · = b)).card := by
    classical
    let S := (U ×ˢ V).filter fun p => u p.1=v p.2
    have hs : (S:Set (A×C)).MapsTo (fun p => u p.1) B :=
      fun p hp => hu (mem_product.mp (mem_filter.mp hp).1).1
    have hf (b : γ) : S.filter (fun p => u p.1=b) = U.filter (u · = b) ×ˢ V.filter (v · = b) := by
      ext p
      simp only [S,mem_filter,mem_product]; grind
    simpa only [hf,card_product] using card_eq_sum_card_fiberwise hs

/-- Twice the number of pairs with matching images under two maps is at
most the sum of their respective equal-image pair counts. -/
theorem twice_card_matching_le {α β γ : Type*} [DecidableEq γ]
    (P : Finset α) (Q : Finset β) (f : α → γ) (g : β → γ) :
    2*((P ×ˢ Q).filter fun p => f p.1=g p.2).card ≤
      ((P ×ˢ P).filter fun p => f p.1=f p.2).card +
      ((Q ×ˢ Q).filter fun p => g p.1=g p.2).card := by
  classical
  let B := P.image f ∪ Q.image g
  have hP : (P:Set α).MapsTo f B := fun x hx => mem_union_left _ (mem_image_of_mem f hx)
  have hQ : (Q:Set β).MapsTo g B := fun y hy => mem_union_right _ (mem_image_of_mem g hy)
  rw [card_matching_eq_sum B P Q f g hP,card_matching_eq_sum B P P f f hP,card_matching_eq_sum B Q Q g g hQ,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro b _
  let a := (P.filter (f · = b)).card
  let c := (Q.filter (g · = b)).card
  change 2*(a*c)≤a*a+c*c
  exact_mod_cast (show 2*((a:ℤ)*c)≤a*a+(c:ℤ)*c by nlinarith only [sq_nonneg ((a:ℤ)-c)])

/-- Vector of positive-degree power sums of an integral tuple. -/
def vinogradovMoments {s : ℕ} (k : ℕ) (x : Fin s → ℤ) (j : Fin k) : ℤ :=
  ∑ i, x i^(j.val+1)

/-- Equal-length integral tuples with a prescribed difference of moment
vectors, restricted to an arbitrary finite set of tuples. -/
def vinogradovShiftedPairs {s k : ℕ} (P : Finset (Fin s → ℤ)) (h : Fin k → ℤ) :=
  (P ×ˢ P).filter fun xy => vinogradovMoments k xy.1=vinogradovMoments k xy.2+h

/-- The number of solutions at any prescribed shift is bounded by the
number of homogeneous solutions in the same set. -/
theorem vinogradovShiftedPairs_card_le {s k : ℕ} (P : Finset (Fin s → ℤ)) (h : Fin k → ℤ) :
    (vinogradovShiftedPairs P h).card≤(vinogradovShiftedPairs P (0:Fin k → ℤ)).card := by
  let f := @vinogradovMoments s k
  have H := twice_card_matching_le P P f (fun y => f y+h)
  simp only [add_left_inj] at H
  unfold vinogradovShiftedPairs
  simp only [add_zero]
  dsimp only [f] at H
  omega

/-- Each pair of tuples contributes to exactly one shift. -/
theorem sum_vinogradovShiftedPairs {s k : ℕ} (P : Finset (Fin s → ℤ)) :
    ∑ h ∈ (P ×ˢ P).image (fun xy => vinogradovMoments k xy.1-vinogradovMoments k xy.2),
      (vinogradovShiftedPairs P h).card = P.card^2 := by
  let d (xy : (Fin s → ℤ) × (Fin s → ℤ)) := vinogradovMoments k xy.1-vinogradovMoments k xy.2
  have H := card_eq_sum_card_fiberwise (s:=P ×ˢ P) (t:=(P ×ˢ P).image d)
    (show (↑(P ×ˢ P) : Set ((Fin s → ℤ) × (Fin s → ℤ))).MapsTo d ((P ×ˢ P).image d) from fun p hp => mem_image_of_mem d hp)
  have he (h : Fin k → ℤ) : (P ×ˢ P).filter (fun p => d p=h) = vinogradovShiftedPairs P h := by
    ext p; simp only [mem_filter,d,vinogradovShiftedPairs,sub_eq_iff_eq_add]; rw [add_comm]
  simpa only [he,card_product,sq] using H.symm

end AnalyticNumberTheory.ExponentialSums
