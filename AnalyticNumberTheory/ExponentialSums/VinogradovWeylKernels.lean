import AnalyticNumberTheory.ExponentialSums.VinogradovLinearKernels
import AnalyticNumberTheory.ExponentialSums.VinogradovWeylSampling

/-!
# Rationally spaced samples in Weyl's inequality

After differencing the sample points, the highest retained coefficient runs
through a progression of integer multiples of the leading coefficient.
Summing its one-dimensional kernel gives an explicit denominator bound.
-/

open Real Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem norm_symm_geometric_le (R : ℕ) (θ : ℝ) :
    ‖∑ v∈Icc (-(R:ℤ)) R,e (θ*v)‖ ≤ linearExpBound (2*R+1) θ := by
  have hi : Icc (-(R:ℤ)) R = Ioc (-(R:ℤ)-1) R := by ext u; simp
  rw [hi]
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
    norm_sum_Ioc_int_e_le_linearExpBound θ (A:=-(R:ℤ)-1) (B:=R) (N:=2*R+1)
      (by omega) (by push_cast; omega)

private theorem sum_linear_progression_le {θ : ℝ} {a : ℤ} {q : ℕ} (hq : 1≤q)
    (hcop : a.natAbs.Coprime q) (hθ : |θ-(a:ℝ)/q|≤1/(q:ℝ)^2)
    {d : ℕ} (hd : 0<d) (Y : ℕ) {z : ℤ} (hz : z∈Icc 1 (Y:ℤ)) {L : ℝ} (hL : 0≤L) :
    ∑ u∈Icc 1 (Y:ℤ), linearExpBound L (θ*(d:ℝ)*(u-z)) ≤
      L+18*(((d*Y:ℕ)+q:ℝ)*Real.log (2*(q:ℝ)) + (d*Y:ℕ)*L/q) := by
  let S := Icc 1 (Y:ℤ)
  let f (u : ℤ) := (d:ℤ)*(u-z)
  let g (h : ℤ) := linearExpBound L (θ*h)
  let X := d*Y
  have hsub : S.image f⊆Icc (-(X:ℤ)) X := by
    intro h hh
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hh
    have hz' := mem_Icc.mp hz
    have hu' := mem_Icc.mp hu
    dsimp only [X,f]; push_cast; apply mem_Icc.mpr
    constructor
    · have H := mul_le_mul_of_nonneg_left (show -(Y:ℤ)≤u-z by omega) (Int.natCast_nonneg d)
      linarith only [H]
    · exact mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg d)
  have hf : Function.Injective f := fun u v huv =>
    sub_left_injective (mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d:ℤ)≠0) huv)
  calc _ = ∑ h∈S.image f,g h := by
             rw [sum_image (fun u _ v _ he => hf he)]
             apply sum_congr rfl; intro u _
             dsimp [g,f]; push_cast; congr 1; ring
       _ ≤ ∑ h∈Icc (-(X:ℤ)) X,g h := sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => linearExpBound_nonneg hL _)
       _ ≤ _ := by
             rw [sum_symmetric_Icc_even X g (fun u => by simp [g,linearExpBound_neg])]
             have H := sum_Icc_linearExpBound_le hq hcop hθ X hL
             have H0 : g 0≤L := linearExpBound_le_left _ _
             dsimp only [g,X] at *
             simp only [Int.cast_natCast] at *
             exact (add_le_add H0 (mul_le_mul_of_nonneg_left H (by norm_num : 0≤(2:ℝ)))).trans_eq (by ring)

/-- Rectangular sampling on integer shifts with an affine top coefficient.
All the lower coefficients are unrestricted. -/
theorem vinogradov_sampling_top_coefficient {d : ℕ} (R : Fin (d+1) → ℕ) (Y : ℕ)
    (α : ℤ → Fin (d+1) → ℝ) {θ : ℝ} {b : ℕ} (hb : 0<b)
    (htop : ∀ u v : ℤ, α u (Fin.last d)-α v (Fin.last d)=θ*b*(u-v))
    {a : ℤ} {q : ℕ} (hq : 1≤q) (hcop : a.natAbs.Coprime q) (hθ : |θ-(a:ℝ)/q|≤1/(q:ℝ)^2) :
    let L := (2*R (Fin.last d)+1:ℝ)
    let A := ∏ j : Fin d,(2*R j.castSucc+1:ℝ)
    let B := Icc 1 (Y:ℤ)
    (∑ p ∈ B ×ˢ B, ∏ j, ‖∑ v∈Icc (-(R j:ℤ)) (R j),e ((α p.1 j-α p.2 j)*v)‖) ≤
      A*Y*(L+18*(((b*Y:ℕ)+q:ℝ)*Real.log (2*(q:ℝ))+(b*Y:ℕ)*L/q)) := by
  intro L A B
  have hL : 0≤L := by dsimp [L]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  let g (u v : ℤ) := linearExpBound L (θ*b*(u-v))
  have hp (p : ℤ×ℤ) :
      (∏ j, ‖∑ v∈Icc (-(R j:ℤ)) (R j),e ((α p.1 j-α p.2 j)*v)‖) ≤ A*g p.1 p.2 := by
    rw [Fin.prod_univ_castSucc]
    apply mul_le_mul _ _ (norm_nonneg _) hA
    · apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      exact (norm_symm_geometric_le _ _).trans (linearExpBound_le_left ..)
    · rw [htop]; exact norm_symm_geometric_le _ _
  apply (sum_le_sum (fun p _ => hp p)).trans
  rw [←mul_sum,sum_product,sum_comm]
  change A*(∑ z∈B,∑ u∈B, g u z) ≤ A*Y*_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hA
  apply (sum_le_sum (fun z hz => sum_linear_progression_le hq hcop hθ hb Y hz hL)).trans_eq
  simp [Int.card_Icc]; ring

end AnalyticNumberTheory.ExponentialSums
