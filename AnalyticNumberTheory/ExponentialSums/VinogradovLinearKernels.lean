import AnalyticNumberTheory.ExponentialSums.VinogradovBilinearSums

/-!
# One-dimensional factors in Vinogradov's bilinear method

A reciprocal rational approximation to a small real coefficient provides
cancellation in its symmetric frequency box. These estimates can be applied
independently in each degree of a logarithmic Taylor polynomial.
-/

open Finset Real
namespace AnalyticNumberTheory.ExponentialSums

private theorem sum_Icc_even (R : ℕ) (f : ℤ → ℝ) (hf : ∀ u, f (-u)=f u) :
    (∑ u ∈ Icc (-(R:ℤ)) R, f u) = f 0 + 2*∑ j ∈ Icc 1 R, f (j:ℤ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hset : Icc (-((R+1:ℕ):ℤ)) ((R+1:ℕ):ℤ) =
        insert ((R+1:ℕ):ℤ) (insert (-((R+1:ℕ):ℤ)) (Icc (-(R:ℤ)) R)) := by
      ext u; simp only [mem_Icc,mem_insert,Nat.cast_add,Nat.cast_one]; omega
    have hs : Icc 1 (R+1) = insert (R+1) (Icc 1 R) := by ext j; simp; omega
    rw [hset,hs,sum_insert (by simp; omega),sum_insert (by simp),
      sum_insert (by simp),hf,ih]
    ring

/-- The trivial bound for the symmetric two-dimensional geometric sum. -/
theorem vinogradovLinearKernel_le_sq (R : ℕ) (θ : ℝ) :
    vinogradovLinearKernel R θ ≤ (2*R+1:ℝ)^2 := by
  let D := Icc (-(R:ℤ)) R
  have hc : (D.card:ℝ) = 2*R+1 := by
    dsimp [D]; rw [Int.card_Icc]
    have : ((R:ℤ)+1- -R).toNat=2*R+1 := by omega
    rw [this]; push_cast; rfl
  calc _ ≤ ∑ _u ∈ D, ∑ _v ∈ D, (1:ℝ) := by
             exact sum_le_sum fun u _ => (norm_sum_le ..).trans_eq (by simp [D,norm_e])
       _ = _ := by simp [hc,sq]; ring

private theorem symm_linear_kernel_le (R : ℕ) (θ : ℝ) :
    vinogradovLinearKernel R θ ≤ (2*R+1:ℝ) +
      2*∑ j∈Icc 1 R, linearExpBound (2*R+1) (θ*j) := by
  let L := 2*R+1
  have hi : Icc (-(R:ℤ)) R = Ioc (-(R:ℤ)-1) R := by ext u; simp
  calc _ ≤ ∑ u ∈ Icc (-(R:ℤ)) R, linearExpBound (L:ℝ) (θ*u) := by
             apply sum_le_sum; intro u _
             calc _ = ‖∑ v ∈ Ioc (-(R:ℤ)-1) R, e ((θ*u)*v)‖ := by rw [hi]; simp only [mul_right_comm θ]
                  _ ≤ _ := norm_sum_Ioc_int_e_le_linearExpBound _ (by omega) (by dsimp [L]; omega)
       _ = _ := by
             rw [sum_Icc_even R _ (fun u => by simp [linearExpBound_neg])]
             simp [L,linearExpBound,distToInt]

/-- A rational approximation bounds a one-dimensional factor, including its
central frequency and both endpoints of the box. -/
theorem vinogradovLinearKernel_le_of_approx {θ : ℝ} {a : ℤ} {q : ℕ} (hq : 1≤q)
    (hcop : a.natAbs.Coprime q) (hθ : |θ-(a:ℝ)/q|≤1/(q:ℝ)^2) (R : ℕ) :
    vinogradovLinearKernel R θ ≤ (2*R+1:ℝ) +
      18*(((R:ℝ)+q)*Real.log (2*(q:ℝ)) + R*(2*R+1:ℝ)/q) := by
  have H := sum_Icc_linearExpBound_le hq hcop hθ R (Y:=2*R+1) (by positivity)
  linarith only [symm_linear_kernel_le R θ,H]

/-- The integer part of the reciprocal of a small coefficient is an admissible
denominator, within a factor two of its reciprocal. -/
theorem exists_reciprocal_approximation {θ : ℝ} (hθ : 0 < |θ|) (hsmall : |θ|≤1) :
    ∃ a : ℤ, ∃ q : ℕ, 1≤q ∧ a.natAbs.Coprime q ∧
      1/(2*|θ|)≤q ∧ (q:ℝ)≤1/|θ| ∧ |θ-(a:ℝ)/q|≤1/(q:ℝ)^2 := by
  let q := ⌊1/|θ|⌋₊
  have hq : 1≤q := Nat.le_floor (show ((1:ℕ):ℝ)≤1/|θ| by apply (le_div_iff₀ hθ).mpr; simpa using hsmall)
  have hq0 : 0<(q:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hu : (q:ℝ)≤1/|θ| := Nat.floor_le (by positivity)
  have hl : 1/|θ|<(q:ℝ)+1 := Nat.lt_floor_add_one _
  have hl' : 1/(2*|θ|)≤(q:ℝ) := by
    rw [show 1/(2*|θ|)=(1/|θ|)/2 by ring]
    linarith
  have hu' := (le_div_iff₀ hθ).mp hu
  have hl'' := (div_lt_iff₀ hθ).mp hl
  have he : |abs θ - 1/(q:ℝ)| ≤ 1/(q:ℝ)^2 := by
    apply abs_le.mpr
    constructor
    · field_simp
      nlinarith only [hu',mul_le_mul_of_nonneg_left hl''.le hq0.le]
    · apply le_trans _ (by positivity : 0≤1/(q:ℝ)^2)
      exact sub_nonpos.mpr ((le_div_iff₀ hq0).mpr (by linarith only [hu']))
  by_cases h : 0≤θ
  · refine ⟨1,q,hq,by simp,hl',hu,?_⟩
    simpa [abs_of_nonneg h] using he
  · refine ⟨-1,q,hq,by simp,hl',hu,?_⟩
    rw [abs_of_neg (lt_of_not_ge h)] at he
    convert he using 1
    rw [←abs_neg]; congr 1; push_cast; ring

/-- A simultaneous lower bound on the length, the reciprocal coefficient,
and the ratio of the area to the reciprocal coefficient saves the factor
`U`, up to the displayed logarithm. -/
theorem vinogradovLinearKernel_saving (R : ℕ) {θ U H : ℝ}
    (hθ : 0 < |θ|) (hU : 1≤U) (hH : 1≤H)
    (hL : U≤2*R+1) (hsmall : |θ|≤1/U) (hlarge : 1/|θ| ≤ (2*R+1:ℝ)^2/U)
    (hlog : Real.log (2/|θ|)≤H) :
    vinogradovLinearKernel R θ ≤ 73*H*((2*R+1:ℝ)^2/U) := by
  let L := (2*R+1:ℝ)
  let K := L^2/U
  have hU0 : 0<U := by linarith
  have hL0 : 0≤L := by dsimp [L]; positivity
  have hK0 : 0≤K := by dsimp [K]; positivity
  have hRL : (R:ℝ) ≤ L := by dsimp [L]; linarith [Nat.cast_nonneg (α:=ℝ) R]
  have hLK : L≤K := by
    apply (le_div_iff₀ hU0).mpr
    simpa [sq] using (mul_le_mul_of_nonneg_left hL hL0)
  obtain ⟨a,q,hq,hcop,hql,hqu,ha⟩ := exists_reciprocal_approximation hθ
    (hsmall.trans ((div_le_iff₀ hU0).mpr (by linarith)))
  have hq0 : 0<(q:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqU : 1/(q:ℝ)≤2/U := by
    have he := (div_le_iff₀ (by positivity : 0<2*|θ|)).mp hql
    rw [show 2/U=(1/U)*2 by ring]
    apply (div_le_iff₀ hq0).mpr
    nlinarith only [he,mul_le_mul_of_nonneg_right hsmall hq0.le]
  have hqK : (q:ℝ)≤K := hqu.trans hlarge
  have hlogq : Real.log (2*(q:ℝ))≤H := by
    apply (Real.log_le_log (by positivity) _).trans hlog
    simpa only [←mul_div_assoc,mul_one] using (mul_le_mul_of_nonneg_left hqu (by norm_num : (0:ℝ)≤2))
  have hterm₁ : ((R:ℝ)+q)*Real.log (2*(q:ℝ)) ≤ (2*K)*H := by
    exact (mul_le_mul_of_nonneg_left hlogq (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hRL,hLK,hqK]) (by linarith))
  have hterm₂ : (R:ℝ)*L/q ≤ 2*K := by
    calc _ = ((R:ℝ)*L)*(1/(q:ℝ)) := by ring
         _ ≤ (L*L)*(2/U) :=
           mul_le_mul (mul_le_mul_of_nonneg_right hRL hL0) hqU (by positivity) (by positivity)
         _ = _ := by dsimp [K]; ring
  have hh := vinogradovLinearKernel_le_of_approx hq hcop ha R
  change _ ≤ L + 18*(((R:ℝ)+q)*Real.log (2*(q:ℝ)) + (R:ℝ)*L/q) at hh
  change _ ≤ 73*H*K
  nlinarith only [hh,hterm₁,hterm₂,hLK,mul_le_mul_of_nonneg_right hH hK0]

end AnalyticNumberTheory.ExponentialSums
