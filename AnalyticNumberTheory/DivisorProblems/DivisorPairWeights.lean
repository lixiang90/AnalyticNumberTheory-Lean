import AnalyticNumberTheory.DivisorProblems.DirichletHyperbola

/-!
# Weighted divisor pairs on either side of the diagonal
-/

open Finset
namespace AnalyticNumberTheory.DivisorProblems

/-- Grouping positive divisor pairs by their product. Each off-diagonal
pair occurs twice and the squares supply the diagonal correction. -/
theorem sum_divisor_weights_eq_strict_pairs {R : Type*} [CommSemiring R] (N : ℕ) (f : ℕ→R) :
    (∑ n∈Icc 1 N,(n.divisors.card:R)*f n) =
      2*(∑ h∈Icc 1 N.sqrt,∑ m∈Ioc h (N/h),f (h*m)) +
        ∑ h∈Icc 1 N.sqrt,f (h^2) := by
  classical
  let S := (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ×ℕ => p.1*p.2≤N)
  let g (p : ℕ×ℕ) := f (p.1*p.2)
  let L := S.filter (fun p => p.1<p.2)
  let U := S.filter (fun p => p.2<p.1)
  let D := S.filter (fun p => p.1=p.2)
  have hmaps {p : ℕ×ℕ} (hp : p∈S) : p.1*p.2∈Icc 1 N := by
    simp only [S,mem_filter,mem_product,mem_Icc] at hp
    exact mem_Icc.mpr ⟨Nat.mul_pos hp.1.1.1 hp.1.2.1,hp.2⟩
  have htot : (∑ n∈Icc 1 N,(n.divisors.card:R)*f n)=∑ p∈S,g p := by
    rw [←sum_fiberwise_of_maps_to (fun _ hp => hmaps hp)]
    apply sum_congr rfl; intro n hn
    have hf : S.filter (fun p => p.1*p.2=n)=n.divisorsAntidiagonal := by
      ext ⟨h,m⟩
      simp only [S,mem_filter,mem_product,mem_Icc,Nat.mem_divisorsAntidiagonal]
      have ⟨hn₁,hn₂⟩ := mem_Icc.mp hn
      constructor
      · rintro ⟨_,he⟩; exact ⟨he,by omega⟩
      · rintro ⟨he,hne⟩
        have hh : 1≤h := Nat.pos_of_ne_zero (left_ne_zero_of_mul (he ▸ hne))
        have hm : 1≤m := Nat.pos_of_ne_zero (right_ne_zero_of_mul (he ▸ hne))
        exact ⟨⟨⟨⟨hh,(Nat.le_mul_of_pos_right h hm).trans (he ▸ hn₂)⟩,⟨hm,(Nat.le_mul_of_pos_left m hh).trans (he ▸ hn₂)⟩⟩,he ▸ hn₂⟩,he⟩
    rw [hf]
    calc
      _ = ∑ _p ∈ n.divisorsAntidiagonal,f n := by rw [←Nat.map_div_right_divisors]; simp
      _ = _ := sum_congr rfl (fun p hp => by dsimp [g]; rw [(Nat.mem_divisorsAntidiagonal.mp hp).1])
  have hswap : (∑ p∈U,g p)=∑ p∈L,g p := by
    apply sum_bij (fun p _ => p.swap)
    · rintro ⟨h,m⟩ hp
      simp only [S,U,L,Prod.swap,mem_filter,mem_product,mem_Icc,mul_comm m h] at hp ⊢
      exact ⟨⟨hp.1.1.symm,hp.1.2⟩,hp.2⟩
    · intro p _ q _ he; exact Prod.swap_injective he
    · rintro ⟨h,m⟩ hp; refine ⟨(m,h),?_,rfl⟩
      simp only [S,U,L,mem_filter,mem_product,mem_Icc,mul_comm m h] at hp ⊢
      exact ⟨⟨hp.1.1.symm,hp.1.2⟩,hp.2⟩
    · rintro ⟨h,m⟩ _; dsimp [g]; rw [mul_comm]
  have htri : (∑ p∈L,g p)=∑ h∈Icc 1 N.sqrt,∑ m∈Ioc h (N/h),f (h*m) := by
    rw [sum_sigma']
    apply sum_bij (fun p _ => (⟨p.1,p.2⟩:Σ _h : ℕ,ℕ))
    · rintro ⟨h,m⟩ hp; simp only [L,S,mem_filter,mem_product,mem_Icc] at hp
      exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hp.1.1.1.1,Nat.le_sqrt.mpr ((Nat.mul_le_mul_left h hp.2.le).trans hp.1.2)⟩,
        mem_Ioc.mpr ⟨hp.2,(Nat.le_div_iff_mul_le hp.1.1.1.1).mpr (by simpa [mul_comm] using hp.1.2)⟩⟩
    · rintro ⟨i,j⟩ _ ⟨k,l⟩ _ hh; cases hh; rfl
    · rintro ⟨h,m⟩ hp
      obtain ⟨hh,hm⟩ := mem_sigma.mp hp
      obtain ⟨hh,hh'⟩ := mem_Icc.mp hh
      obtain ⟨hm,hm'⟩ := mem_Ioc.mp hm
      have he : h*m≤N := by simpa [mul_comm] using (Nat.le_div_iff_mul_le hh).mp hm'
      refine ⟨(h,m),?_,rfl⟩
      simp only [L,S,mem_filter,mem_product,mem_Icc]
      exact ⟨⟨⟨⟨hh,hh'.trans (Nat.sqrt_le_self N)⟩,⟨hh.trans hm.le,(Nat.le_mul_of_pos_left m hh).trans he⟩⟩,he⟩,hm⟩
    · intro p _; rfl
  have hdiag : (∑ p∈D,g p)=∑ h∈Icc 1 N.sqrt,f (h^2) := by
    apply sum_bij (fun p _ => p.1)
    · rintro ⟨h,m⟩ hp; simp only [D,S,mem_filter,mem_product,mem_Icc] at hp
      exact mem_Icc.mpr ⟨hp.1.1.1.1,Nat.le_sqrt.mpr (by simpa only [hp.2] using hp.1.2)⟩
    · rintro ⟨i,j⟩ hp ⟨k,l⟩ hq hh
      have hij := (mem_filter.mp hp).2; have hkl := (mem_filter.mp hq).2
      dsimp at hh hij hkl; subst_vars; rfl
    · intro h hh
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hh
      refine ⟨(h,h),?_,rfl⟩
      simp only [D,S,mem_filter,mem_product,mem_Icc]
      exact ⟨⟨⟨⟨h₁,h₂.trans (Nat.sqrt_le_self N)⟩,⟨h₁,h₂.trans (Nat.sqrt_le_self N)⟩⟩,Nat.le_sqrt.mp h₂⟩,trivial⟩
    · rintro ⟨h,m⟩ hp; have he := (mem_filter.mp hp).2; dsimp at he; dsimp [g]; rw [he,pow_two]
  have hsplit (P : Finset (ℕ×ℕ)) :
      (∑ p∈P,g p)=(∑ p∈P.filter (fun p => p.2<p.1),g p)+(∑ p∈P.filter (fun p => p.1<p.2),g p)+∑ p∈P.filter (fun p => p.1=p.2),g p := by
    simp only [sum_filter,←sum_add_distrib]
    apply sum_congr rfl; intro p _; rcases lt_trichotomy p.1 p.2 with h|h|h
    · simp [h,h.not_gt,h.ne]
    · simp [h]
    · simp [h,h.not_gt,h.ne.symm]
  rw [htot,←htri,←hdiag,two_mul]
  calc
    _ = (∑ p∈U,g p)+(∑ p∈L,g p)+∑ p∈D,g p := hsplit S
    _ = _ := by rw [hswap]

end AnalyticNumberTheory.DivisorProblems
