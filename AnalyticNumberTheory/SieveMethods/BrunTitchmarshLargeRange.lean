import AnalyticNumberTheory.SieveMethods.CombinatorialSieve

/-! # Numerical comparison in the large range of Brun–Titchmarsh

At real length u ≥ 16000 a sieve block of length at most u+1 and cutoff
z = 5√N/6 gives the coefficient two, once its effective denominator is
at least log z + 0.31. The elementary odd-prime count suffices for π(z).
-/
open Real Finset
namespace AnalyticNumberTheory.SieveMethods

/-- Counting odd candidates, with a separate unit for the prime two. -/
theorem primeFinset_card_le_half_add_one {z : ℝ} (hz : 0≤z) :
    ((primeFinset z).card:ℝ)≤z/2+1 := by
  let P := (primeFinset z).erase 2
  have odd (p : ℕ) (hp : p∈P) : p%2=1 :=
    (mem_primeFinset_iff.mp (mem_erase.mp hp).2).1.eq_two_or_odd.resolve_left (mem_erase.mp hp).1
  have hi : Set.InjOn (fun p : ℕ => p/2) (↑P : Set ℕ) := by
    intro p hp q hq he
    change p/2=q/2 at he
    have hp' := odd p hp
    have hq' := odd q hq
    omega
  have hsub : P.image (fun p : ℕ => p/2) ⊆ Icc 1 ⌊z/2⌋₊ := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    obtain ⟨hpp,hpz⟩ := mem_primeFinset_iff.mp (mem_erase.mp hp).2
    refine mem_Icc.mpr ⟨by have := hpp.two_le; omega, Nat.le_floor ?_⟩
    apply (le_div_iff₀ (by norm_num)).2
    apply le_trans _ hpz
    exact_mod_cast Nat.div_mul_le_self p 2
  have h := card_le_card hsub
  rw [card_image_of_injOn hi,Nat.card_Icc,Nat.add_sub_cancel] at h
  have hcard : (primeFinset z).card ≤ P.card+1 := by
    by_cases hp : 2∈primeFinset z
    · exact (card_erase_add_one hp).symm.le
    · simp [P,erase_eq_of_notMem hp]
  have H : ((primeFinset z).card:ℝ) ≤ (⌊z/2⌋₊:ℝ)+1 := by exact_mod_cast hcard.trans (Nat.add_le_add_right h 1)
  linarith only [H,Nat.floor_le (show 0≤z/2 by linarith)]

private theorem bt_log_square_le_sqrt {N : ℝ} (hN : 16000≤N) : (log N)^2≤sqrt N := by
  let v := sqrt (sqrt N)
  have hs : 0≤sqrt N := sqrt_nonneg _
  have hv : 0≤v := sqrt_nonneg _
  have hn : 0<N := by linarith
  have hR : (sqrt N)^2=N := Real.sq_sqrt hn.le
  have hV : v^2=sqrt N := Real.sq_sqrt hs
  have hR₁ : 100≤sqrt N := by nlinarith only [hR,hN,hs]
  have hv₁ : 10≤v := by nlinarith only [hV,hR₁,hv]
  have hv₀ : 0<v := by linarith
  have hN' : v^4=N := by rw [show v^4=(v^2)^2 by ring,hV,hR]
  have h₁ : log 10 ≤ 5/2 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<10)).2
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤5/2) 6)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hv₀ (by norm_num : (0:ℝ)<10))
  rw [Real.log_div hv₀.ne' (by norm_num)] at h₂
  have hL : log N≤v := by rw [←hN',Real.log_pow]; push_cast; linarith
  exact (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hL 2).trans_eq hV

/-- Effective numerical comparison for every real block length N between
u and u+1. In particular N may be the ceiling of u. -/
theorem brun_titchmarsh_large_range_numeric {u N : ℝ} (hu : 16000≤u)
    (hlo : u≤N) (hhi : N≤u+1) :
    let z := (5/6:ℝ)*Real.sqrt N
    N/(Real.log z+31/100)+(primeFinset z).card ≤ 2*u/Real.log u := by
  intro z
  let L := log N
  let R := sqrt N
  have hN : 16000≤N := hu.trans hlo
  have hNp : 0<N := by linarith
  have hRp : 0<R := sqrt_pos.mpr hNp
  have hR : R^2=N := Real.sq_sqrt hNp.le
  have hR₁ : 100≤R := by nlinarith only [hR,hN,hRp.le]
  have hL : 4≤L := by
    apply (Real.le_log_iff_exp_le hNp).2
    rw [show (4:ℝ)=(4:ℕ)*1 by norm_num,Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (exp_pos 1).le (by linarith [Real.exp_one_lt_d9] : exp 1≤3) 4).trans (by linarith)
  have hLp : 0<L := by linarith
  have hLs : L^2≤R := bt_log_square_le_sqrt hN
  have hlog : log (6/5) ≤ 37/200 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<6/5)).2
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤37/200) 4)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have hd : L/2+1/8 ≤ log z+31/100 := by
    have he : z=R/(6/5) := by dsimp [z,R]; ring
    rw [he,Real.log_div hRp.ne' (by norm_num),show log R=L/2 from Real.log_sqrt hNp.le]
    linarith
  have hpp : ((primeFinset z).card:ℝ)≤5/12*R+1 := by
    convert primeFinset_card_le_half_add_one (z:=z) (by dsimp [z]; positivity) using 1
    dsimp [z,R]; ring
  have hden : L*(L/2+1/8)≤17/32*R := by
    nlinarith only [hLs,mul_nonneg hLp.le (sub_nonneg.mpr hL)]
  have hsave : 9/20*R ≤ (N/4)/(L*(L/2+1/8)) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_left hden (show 0≤9/20*R by positivity),hR,hNp.le]
  have hrec : N/(L/2+1/8)=2*N/L-(N/4)/(L*(L/2+1/8)) := by
    field_simp [hLp.ne',show L/2+1/8≠0 by positivity]
    ring
  have hfloor : 2/L≤1/2 := (div_le_iff₀ hLp).2 (by linarith)
  have huL := Real.log_pos (show 1<u by linarith)
  have huN : log u≤L := Real.log_le_log (by linarith) hlo
  calc _ ≤ N/(L/2+1/8)+(5/12*R+1) := add_le_add
          (div_le_div_of_nonneg_left hNp.le (by positivity) hd) hpp
       _ ≤ 2*(N-1)/L := by
          rw [hrec,show 2*(N-1)/L=2*N/L-2/L by ring]
          linarith only [hsave,hR₁,hfloor]
       _ ≤ 2*u/L := div_le_div_of_nonneg_right (by linarith) hLp.le
       _ ≤ _ := div_le_div_of_nonneg_left (by linarith) huL huN

end AnalyticNumberTheory.SieveMethods
