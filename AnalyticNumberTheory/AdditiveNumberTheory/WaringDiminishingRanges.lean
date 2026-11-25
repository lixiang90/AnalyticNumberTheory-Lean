import AnalyticNumberTheory.AdditiveNumberTheory.CircleMethod

/-!
# Diminishing ranges for sums of powers

Successive boxes are short enough that the first differing coordinate
determines the order of two sums. Orthogonality then gives the exact second
moment of the product of their exponential sums.
-/

open Finset MeasureTheory
namespace AnalyticNumberTheory.AdditiveNumberTheory

private theorem geometric_box_sum (m : ℕ) (w : ℕ → ℕ)
    (h : ∀ j, j+1<m → 2*w (j+1)≤w j) :
    ∑ j ∈ range m, w j ≤ 2*w 0 := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp; omega
    | succ m =>
      rw [sum_range_succ']
      have H := ih (fun j => w (j+1)) (fun j hj => h (j+1) (by omega))
      have h₀ := h 0 (by omega)
      omega

private theorem pow_step_lower (x n : ℕ) :
    x^(n+1)+(n+1)*x^n ≤ (x+1)^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ (x^(n+1)+(n+1)*x^n)*(x+1) := by
        rw [pow_succ x (n+1), pow_succ x n]
        ring_nf
        omega
      _ ≤ _ := by rw [pow_succ (x+1) (n+1)]; gcongr

private theorem box_power_gap {L a b k : ℕ} (hk : 1≤k) (hL : L≤a) (hab : a<b) :
    a^k+k*L^(k-1) ≤ b^k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  simpa using (calc
    a^(n+1)+(n+1)*L^n ≤ a^(n+1)+(n+1)*a^n := by gcongr
    _ ≤ (a+1)^(n+1) := pow_step_lower a n
    _ ≤ b^(n+1) := Nat.pow_le_pow_left hab _)

private theorem boxes_halve {k L M : ℕ} (hk : 1≤k) (hL : 0<L)
    (h : (2*M)^k≤L^(k-1)) : 2*(2*M)^k≤(2*L)^k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  change (2*M)^(n+1)≤L^n at h
  calc
    _ ≤ 2*L^n := Nat.mul_le_mul_left 2 h
    _ ≤ 2*(2^n*L)*(L^n) := by
      have ha : 1≤2^n*L := Nat.mul_pos (pow_pos (by decide) _) hL
      nlinarith [Nat.mul_le_mul_right (L^n) ha]
    _ = (2*L)^(n+1) := by rw [mul_pow, pow_succ, pow_succ L]; ring

private theorem box_tuple_sum_le {m k : ℕ} (L : ℕ → ℕ) (x : Fin m → ℕ)
    (hx : ∀ i, x i≤2*L i) (h : ∀ j, j+1<m → 2*(2*L (j+1))^k≤(2*L j)^k) :
    ∑ i, x i^k ≤ 2*(2*L 0)^k := by
  calc
    _ ≤ ∑ i : Fin m, (2*L i)^k := sum_le_sum fun i _ => Nat.pow_le_pow_left (hx i) _
    _ = ∑ j ∈ range m, (2*L j)^k := Fin.sum_univ_eq_sum_range (fun i => (2*L i)^k) m
    _ ≤ _ := geometric_box_sum m _ h

/-- A tuple of bases in diminishing dyadic intervals is determined by its power sum. -/
theorem waring_diminishing_injective {k m : ℕ} (hk : 3≤k) (L : ℕ → ℕ)
    (hpos : ∀ j, j<m → 0<L j)
    (hL : ∀ j, j+1<m → (2*L (j+1))^k ≤ (L j)^(k-1)) :
    Set.InjOn (fun x : Fin m → ℕ => ∑ i, x i^k)
      {x | ∀ i : Fin m, x i∈Ioc (L i) (2*L i)} := by
  induction m generalizing L with
  | zero =>
    intro x hx y hy hxy
    exact Subsingleton.elim _ _
  | succ m ih =>
    intro x hx y hy hxy
    change ∀ i : Fin (m+1), x i∈Ioc (L i) (2*L i) at hx
    change ∀ i : Fin (m+1), y i∈Ioc (L i) (2*L i) at hy
    let L' (j : ℕ) := L (j+1)
    have tail (v : Fin (m+1) → ℕ) (hv : ∀ i : Fin (m+1), v i∈Ioc (L i) (2*L i)) :
        ∑ j : Fin m, v j.succ^k < k*(L 0)^(k-1) := by
      have hp := pow_pos (hpos 0 (by omega)) (k-1)
      cases m with
      | zero => simpa using Nat.mul_pos (by omega : 0<k) hp
      | succ m =>
        have H := box_tuple_sum_le L' (fun i : Fin (m+1) => v i.succ)
          (fun i => (mem_Ioc.mp (hv i.succ)).2) (fun j hj =>
          boxes_halve (by omega) (hpos (j+1) (by omega)) (hL (j+1) (by omega)))
        have h₀ := hL 0 (by omega)
        dsimp [L'] at H
        nlinarith [Nat.mul_le_mul_right ((L 0)^(k-1)) hk]
    simp only [Fin.sum_univ_succ] at hxy
    have he : x 0 = y 0 := by
      rcases lt_trichotomy (x 0) (y 0) with h|h|h
      · have := box_power_gap (L:=L 0) (by omega : 1≤k) (mem_Ioc.mp (hx 0)).1.le h
        have := tail x hx
        omega
      · exact h
      · have := box_power_gap (L:=L 0) (by omega : 1≤k) (mem_Ioc.mp (hy 0)).1.le h
        have := tail y hy
        omega
    rw [he] at hxy
    have ht := ih L' (fun j hj => hpos (j+1) (by omega)) (fun j hj => hL (j+1) (by omega))
      (x₁:=fun j => x j.succ) (fun j => hx j.succ) (x₂:=fun j => y j.succ) (fun j => hy j.succ)
      (Nat.add_left_cancel hxy)
    funext i
    exact Fin.cases he (fun j => congrFun ht j) i

/-- Product of the short exponential sums over the individual dyadic boxes. -/
noncomputable def waringDiminishingSum (k m : ℕ) (L : ℕ → ℕ) (α : ℝ) : ℂ :=
  ∏ i : Fin m, ∑ x ∈ Ioc (L i) (2*L i), e (α*(x:ℝ)^k)

/-- Orthogonality on a whole period gives exactly the number of tuples. -/
theorem integral_norm_sq_waringDiminishingSum {k m : ℕ} (hk : 3≤k) (L : ℕ → ℕ)
    (hpos : ∀ j, j<m → 0<L j)
    (hL : ∀ j, j+1<m → (2*L (j+1))^k ≤ (L j)^(k-1)) (a : ℝ) :
    ∫ α in a..a+1, ‖waringDiminishingSum k m L α‖^2 = ∏ i : Fin m, (L i : ℝ) := by
  classical
  let B := Fintype.piFinset (fun i : Fin m => Ioc (L i) (2*L i))
  let f (x : Fin m → ℕ) := ∑ i, x i^k
  have hi : Set.InjOn f B := by
    intro x hx y hy h
    exact waring_diminishing_injective hk L hpos hL (Fintype.mem_piFinset.mp hx) (Fintype.mem_piFinset.mp hy) h
  have he : waringDiminishingSum k m L = expSum (fun _ => 1) (B.image f) := by
    funext α
    rw [waringDiminishingSum,Finset.prod_univ_sum,expSum,sum_image hi]
    apply sum_congr rfl
    intro x hx
    rw [one_mul]
    dsimp [f]
    push_cast
    rw [mul_sum,e_sum]
  rw [he,integral_norm_sq_expSum_shift]
  simp only [norm_one, one_pow, sum_const, nsmul_eq_mul, mul_one, Finset.card_image_of_injOn hi]
  simp [B,two_mul]

/-- The finite set of all sums over the shortened variables. -/
def waringDiminishingValues (k m : ℕ) (L : ℕ → ℕ) : Finset ℕ :=
  (Fintype.piFinset (fun i : Fin m => Ioc (L i) (2*L i))).image (fun x => ∑ i, x i^k)

/-- Diminishing ranges give a set of distinct representable shifts of full box cardinality. -/
theorem card_waringDiminishingValues {k m : ℕ} (hk : 3≤k) (L : ℕ → ℕ)
    (hpos : ∀ j, j<m → 0<L j)
    (hL : ∀ j, j+1<m → (2*L (j+1))^k ≤ (L j)^(k-1)) :
    (waringDiminishingValues k m L).card = ∏ i : Fin m, L i := by
  rw [waringDiminishingValues,card_image_of_injOn (by
    intro x hx y hy h
    exact waring_diminishing_injective hk L hpos hL (Fintype.mem_piFinset.mp hx) (Fintype.mem_piFinset.mp hy) h)]
  simp [two_mul]

/-- The whole shift set is contained in the interval bounded by twice the first box's upper power. -/
theorem waringDiminishingValues_le {k m : ℕ} (hk : 3≤k) (L : ℕ → ℕ)
    (hpos : ∀ j, j<m → 0<L j) (hL : ∀ j, j+1<m → (2*L (j+1))^k ≤ (L j)^(k-1))
    {a : ℕ} (ha : a∈waringDiminishingValues k m L) : a ≤ 2*(2*L 0)^k := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
  apply box_tuple_sum_le L x (fun i => (mem_Ioc.mp (Fintype.mem_piFinset.mp hx i)).2)
  exact fun j hj => boxes_halve (by omega) (hpos j (by omega)) (hL j hj)

end AnalyticNumberTheory.AdditiveNumberTheory
