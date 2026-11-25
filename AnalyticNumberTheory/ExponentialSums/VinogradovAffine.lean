import AnalyticNumberTheory.ExponentialSums.VinogradovShiftedCounts

/-!
# Translation and dilation of Vinogradov systems

Applying the same integral affine map to every coordinate preserves the
homogeneous equations in both directions when the dilation is nonzero.
Thus every full arithmetic progression has the same mean count as its
initial interval of indices.
-/

open Finset
namespace AnalyticNumberTheory.ExponentialSums

private theorem sum_affine_pow {s : ℕ} (x : Fin s → ℤ) (a b : ℤ) (l : ℕ) :
    (∑ i, (a*x i+b)^l) = ∑ j ∈ range (l+1),
      (a^j*b^(l-j)*(l.choose j:ℤ))*(∑ i, x i^j) := by
  simp_rw [add_pow]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_pow]
  ring

/-- All moments up to the degree are preserved by a common affine
change of variables applied to both sides of the equations. -/
theorem vinogradovMoments_affine_of_eq {s k : ℕ} {x y : Fin s → ℤ}
    (h : vinogradovMoments k x=vinogradovMoments k y) (a b : ℤ) :
    vinogradovMoments k (fun i => a*x i+b) = vinogradovMoments k (fun i => a*y i+b) := by
  funext l
  unfold vinogradovMoments
  rw [sum_affine_pow,sum_affine_pow]
  apply sum_congr rfl
  intro j hj
  congr 1
  cases j with
  | zero => simp
  | succ j =>
    have hlt : j<k := by have := mem_range.mp hj; have := l.isLt; omega
    exact congrFun h ⟨j,hlt⟩

/-- A nonconstant common affine change of coordinates gives an
equivalence of the two systems, including reflection and translation. -/
theorem vinogradovMoments_affine_eq_iff {s k : ℕ} (x y : Fin s → ℤ) {a : ℤ} (ha : a≠0) (b : ℤ) :
    vinogradovMoments k (fun i => a*x i+b) = vinogradovMoments k (fun i => a*y i+b) ↔
      vinogradovMoments k x=vinogradovMoments k y := by
  refine ⟨fun h => ?_,fun h => vinogradovMoments_affine_of_eq h a b⟩
  have H := vinogradovMoments_affine_of_eq h 1 (-b)
  simp only [one_mul,add_neg_cancel_right] at H
  funext j
  have h' := congrFun H j
  simp only [vinogradovMoments,mul_pow,←mul_sum] at h'
  exact mul_left_cancel₀ (pow_ne_zero _ ha) h'

/-- The finite set of ordered tuples whose entries lie in a given set. -/
def vinogradovTuples (s : ℕ) (I : Finset ℤ) : Finset (Fin s → ℤ) :=
  Fintype.piFinset fun _ => I

/-- Homogeneous solution count in an arbitrary finite set of integers. -/
def vinogradovCountOn (s k : ℕ) (I : Finset ℤ) : ℕ :=
  (vinogradovShiftedPairs (vinogradovTuples s I) (0:Fin k → ℤ)).card

private theorem mem_countPairs {s k : ℕ} {I : Finset ℤ} {xy : (Fin s → ℤ) × (Fin s → ℤ)} :
    xy ∈ vinogradovShiftedPairs (vinogradovTuples s I) (0:Fin k → ℤ) ↔
      ((∀ i, xy.1 i∈I) ∧ (∀ i, xy.2 i∈I)) ∧ vinogradovMoments k xy.1=vinogradovMoments k xy.2 := by
  simp [vinogradovShiftedPairs,vinogradovTuples,Fintype.mem_piFinset]

/-- The finite solution count is unchanged on affine images of a set. -/
theorem vinogradovCountOn_affine (s k : ℕ) (I : Finset ℤ) {a : ℤ} (ha : a≠0) (b : ℤ) :
    vinogradovCountOn s k (I.image (fun t => a*t+b)) = vinogradovCountOn s k I := by
  classical
  symm
  let f (x : Fin s → ℤ) (i : Fin s) := a*x i+b
  have hf : Function.Injective f := by
    intro x y h
    funext i
    exact mul_left_cancel₀ ha (add_right_cancel (congrFun h i))
  unfold vinogradovCountOn
  apply card_bij (fun xy _ => (f xy.1,f xy.2))
  · intro xy h
    obtain ⟨⟨hx,hy⟩,he⟩ := mem_countPairs.mp h
    exact mem_countPairs.mpr ⟨⟨fun i => mem_image_of_mem _ (hx i),fun i => mem_image_of_mem _ (hy i)⟩,
      vinogradovMoments_affine_of_eq he a b⟩
  · intro x _ y _ h
    exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  · intro xy h
    obtain ⟨⟨hx,hy⟩,he⟩ := mem_countPairs.mp h
    choose x hxI hxe using fun i => mem_image.mp (hx i)
    choose y hyI hye using fun i => mem_image.mp (hy i)
    have hx' : f x=xy.1 := funext hxe
    have hy' : f y=xy.2 := funext hye
    refine ⟨(x,y),mem_countPairs.mpr ⟨⟨hxI,hyI⟩,(vinogradovMoments_affine_eq_iff x y ha b).mp ?_⟩,
      Prod.ext hx' hy'⟩
    change vinogradovMoments k (f x)=vinogradovMoments k (f y)
    rwa [hx',hy']

/-- Integer interval counts agree with the original natural-number definition. -/
theorem vinogradovCountOn_interval (s k N : ℕ) :
    vinogradovCountOn s k (Icc 1 (N:ℤ)) = vinogradovSolutionCount s k N := by
  classical
  symm
  unfold vinogradovSolutionCount vinogradovCountOn
  let f (x : Fin s → ℕ) (i : Fin s) := (x i:ℤ)
  have hf : Function.Injective f := by
    intro x y h; funext i
    exact Int.ofNat_inj.mp (congrFun h i)
  apply card_bij (fun xy _ => (f xy.1,f xy.2))
  · intro xy h
    obtain ⟨hp,he⟩ := mem_filter.mp h
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    apply mem_countPairs.mpr
    refine ⟨⟨fun i => ?_,fun i => ?_⟩,?_⟩
    · exact mem_Icc.mpr (by dsimp [f]; exact_mod_cast mem_Icc.mp (Fintype.mem_piFinset.mp hx i))
    · exact mem_Icc.mpr (by dsimp [f]; exact_mod_cast mem_Icc.mp (Fintype.mem_piFinset.mp hy i))
    · funext j; dsimp [vinogradovMoments,f]; exact_mod_cast he j
  · intro x _ y _ h
    exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  · intro xy h
    obtain ⟨⟨hx,hy⟩,he⟩ := mem_countPairs.mp h
    let g (x : Fin s → ℤ) (i : Fin s) := (x i).toNat
    have hg (x : Fin s → ℤ) (h : ∀ i, x i∈Icc 1 (N:ℤ)) :
        f (g x)=x ∧ g x∈Fintype.piFinset (fun _ => Icc 1 N) := by
      have h' (i : Fin s) : (g x i:ℤ)=x i :=
        Int.toNat_of_nonneg (le_trans (by norm_num) (mem_Icc.mp (h i)).1)
      refine ⟨funext h',Fintype.mem_piFinset.mpr fun i => mem_Icc.mpr ?_⟩
      have hh := mem_Icc.mp (h i)
      rw [←h' i] at hh
      exact_mod_cast hh
    obtain ⟨h₁,hx'⟩ := hg _ hx
    obtain ⟨h₂,hy'⟩ := hg _ hy
    refine ⟨(g xy.1,g xy.2),mem_filter.mpr ⟨mem_product.mpr ⟨hx',hy'⟩,?_⟩,Prod.ext h₁ h₂⟩
    intro j
    rw [←h₁,←h₂] at he
    have hh := congrFun he j
    dsimp [vinogradovMoments,f] at hh
    exact_mod_cast hh

/-- Enlarging the support can only increase the homogeneous count. -/
theorem vinogradovCountOn_mono (s k : ℕ) {I J : Finset ℤ} (hIJ : I⊆J) :
    vinogradovCountOn s k I≤vinogradovCountOn s k J := by
  apply card_le_card
  intro xy h
  obtain ⟨⟨hx,hy⟩,he⟩ := mem_countPairs.mp h
  exact mem_countPairs.mpr ⟨⟨fun i => hIJ (hx i),fun i => hIJ (hy i)⟩,he⟩

/-- Representatives of a single residue class in the initial interval lie
in an affine image of at most `N/p+1` consecutive integers. -/
theorem vinogradov_residue_subset (N p : ℕ) (hp : 0<p) (r : ZMod p) :
    ((Icc 1 (N:ℤ)).filter (fun x : ℤ => (x:ZMod p)=r)) ⊆
      (Icc 1 ((N/p+1:ℕ):ℤ)).image (fun j : ℤ => (p:ℤ)*j+((r.val:ℤ)-p)) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  let J := Icc 1 ((N/p+1:ℕ):ℤ)
  let pz := (p:ℤ)
  have hpz : 0<pz := by dsimp [pz]; exact_mod_cast hp
  let b := (r.val:ℤ)-pz
  have hsub : ((Icc 1 (N:ℤ)).filter (fun x : ℤ => (x:ZMod p)=r)) ⊆ J.image (fun j : ℤ => pz*j+b) := by
    intro x hx
    obtain ⟨hx,hxr⟩ := mem_filter.mp hx
    obtain ⟨hx1,hxN⟩ := mem_Icc.mp hx
    have hr : (x:ZMod p) = ((r.val:ℤ):ZMod p) := by simpa using hxr
    have hm := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hr
    have hrep : (r.val:ℤ)%pz=r.val := Int.emod_eq_of_lt (by positivity) (by dsimp [pz]; exact_mod_cast ZMod.val_lt r)
    rw [hrep] at hm
    refine mem_image.mpr ⟨x/pz+1,mem_Icc.mpr ⟨by linarith [Int.ediv_nonneg (by linarith : 0≤x) hpz.le],?_⟩,?_⟩
    · have hd := Int.ediv_le_ediv hpz hxN
      dsimp [pz] at hd ⊢
      push_cast [Int.natCast_ediv]
      linarith
    · have he := Int.emod_add_mul_ediv x pz
      dsimp only [b]
      change x%pz=(r.val:ℤ) at hm
      rw [hm] at he
      linarith only [he]
  exact hsub

/-- Restricting a Vinogradov system to one residue class shortens its
support from `N` to at most `N/p+1` consecutive indices. -/
theorem vinogradovCountOn_residue_le (s k N p : ℕ) (hp : 0<p) (r : ZMod p) :
    vinogradovCountOn s k ((Icc 1 (N:ℤ)).filter (fun x : ℤ => (x:ZMod p)=r)) ≤
      vinogradovSolutionCount s k (N/p+1) := by
  let J := Icc 1 ((N/p+1:ℕ):ℤ)
  let b := (r.val:ℤ)-p
  have hpz : (p:ℤ)≠0 := by exact_mod_cast hp.ne'
  have hsub := vinogradov_residue_subset N p hp r
  exact (vinogradovCountOn_mono s k hsub).trans_eq
    ((vinogradovCountOn_affine s k J hpz b).trans (vinogradovCountOn_interval s k (N/p+1)))

end AnalyticNumberTheory.ExponentialSums
