import AnalyticNumberTheory.DivisorProblems.GaussCircle

/-!
# Counting lattice points by the eight octants of a disk

The vertical and horizontal strips up to the diagonal cover the disk. Their
intersection is a square, including its boundary. This gives a counting
formula in which the circular arc stays a fixed distance from the vertical tangent.
-/

noncomputable section
open Finset
open scoped Classical
namespace AnalyticNumberTheory.DivisorProblems

/-- Counting by symmetry through the diagonal, with `x` the squared radius.
The diagonal cutoff and the axis term retain the contributions of all boundary points. -/
theorem gaussCircleCount_eq_octant_slices {x : ℝ} (hx : 0≤x) :
    let M := ⌊Real.sqrt (x/2)⌋₊
    gaussCircleCount x = 4*(⌊Real.sqrt x⌋₊:ℝ)+1+
      8*(∑ n ∈ Icc 1 M,(⌊Real.sqrt (x-(n:ℝ)^2)⌋₊:ℝ))-4*(M:ℝ)^2 := by
  intro M
  let u := Real.sqrt (x/2)
  have hu : 0≤u := Real.sqrt_nonneg _
  have hu2 : u^2=x/2 := Real.sq_sqrt (by linarith)
  have hMu : (M:ℝ)≤u := Nat.floor_le hu
  let I := Icc (-(M:ℤ)) (M:ℤ)
  let A := gaussCircleStrip x M
  let B := A.map (Equiv.prodComm ℤ ℤ).toEmbedding
  have hA (p : ℤ×ℤ) : p∈A ↔ (p.1:ℝ)^2+(p.2:ℝ)^2≤x ∧ p.1.natAbs≤M := by
    simp only [A,gaussCircleStrip,mem_filter,mem_gaussCircleFinset]
  have hB (p : ℤ×ℤ) : p∈B ↔ (p.1:ℝ)^2+(p.2:ℝ)^2≤x ∧ p.2.natAbs≤M := by
    change p∈A.map _ ↔ _
    rw [mem_map]
    constructor
    · rintro ⟨q,hq,rfl⟩; simpa [add_comm] using (hA q).mp hq
    · intro h; exact ⟨p.swap,(hA _).mpr (by simpa [add_comm] using h),by simp⟩
  have hs (a : ℤ) : a.natAbs≤M ↔ (a:ℝ)^2≤x/2 := by
    rw [←int_natAbs_sq_real a]
    change a.natAbs≤⌊u⌋₊ ↔ _
    rw [Nat.le_floor_iff hu,←hu2]
    constructor
    · intro h; gcongr
    · intro h; nlinarith [Nat.cast_nonneg (α:=ℝ) a.natAbs]
  have hUnion : A∪B=gaussCircleFinset x := by
    ext p
    rw [mem_union,hA,hB,mem_gaussCircleFinset,hs,hs]
    constructor
    · rintro (ha|hb); exact ha.1; exact hb.1
    · intro h; by_cases hh : (p.1:ℝ)^2≤x/2
      · exact Or.inl ⟨h,hh⟩
      · exact Or.inr ⟨h,by linarith⟩
  have hInter : A∩B=I×ˢI := by
    ext p
    rw [mem_inter,hA,hB,mem_product]
    constructor
    · rintro ⟨⟨_,ha⟩,_,hb⟩
      exact ⟨mem_Icc.mpr (int_abs_le_of_natAbs_le ha),mem_Icc.mpr (int_abs_le_of_natAbs_le hb)⟩
    · rintro ⟨ha,hb⟩
      have ha' := natAbs_le_of_abs_le (mem_Icc.mp ha)
      have hb' := natAbs_le_of_abs_le (mem_Icc.mp hb)
      have hsum : (p.1:ℝ)^2+(p.2:ℝ)^2≤x := by linarith [(hs _).mp ha',(hs _).mp hb']
      exact ⟨⟨hsum,ha'⟩,hsum,hb'⟩
  have hcard : I.card=2*M+1 := by dsimp only [I]; rw [Int.card_Icc]; omega
  have hadd := card_union_add_card_inter A B
  rw [hUnion,hInter,card_product,hcard,show B.card=A.card from card_map _] at hadd
  have hcount : gaussCircleCount x + (2*(M:ℝ)+1)^2 = 2*(A.card:ℝ) := by
    rw [gaussCircleCount,pow_two,two_mul (A.card:ℝ)]; exact_mod_cast hadd
  let f (t : ℝ) := (⌊Real.sqrt (x-t^2)⌋₊:ℝ)
  have harc := gaussCircleStrip_card_eq_sum_slice hx (hMu.trans (Real.sqrt_le_sqrt (by linarith : x/2≤x)))
  have heven := sum_Icc_neg_self_even M (fun t => 2*f t+1) (fun t => by simp [f])
  change (A.card:ℝ) = ∑ n ∈ I, (2*f n+1) at harc
  rw [heven] at harc
  have hf0 : f 0=(⌊Real.sqrt x⌋₊:ℝ) := by simp [f]
  simp only [sum_add_distrib,←mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one,hf0] at harc
  change _ = 4*(⌊Real.sqrt x⌋₊:ℝ)+1+8*(∑ n ∈ Icc 1 M,f n)-4*(M:ℝ)^2
  linarith only [hcount,harc]

end AnalyticNumberTheory.DivisorProblems
