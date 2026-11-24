import AnalyticNumberTheory.RiemannZeta.AsymptoticsAndMeans
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Dirichlet polynomials for periodic L-functions

Group the polynomial into complete residue blocks. The approximation for
Hurwitz zeta at the shifts `1/q,…,q/q` bounds the error uniformly in the
period and in bounded coefficient functions.
-/

open Complex Finset Real
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.RiemannZeta

namespace AnalyticNumberTheory.DirichletLFunctions

private theorem sum_residues_succ {q : ℕ} [NeZero q] {E : Type*} [AddCommMonoid E] (f : ZMod q → E) :
    ∑ j : ZMod q, f j = ∑ r ∈ range q, f ((r+1:ℕ):ZMod q) := by
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) f]
  refine sum_bij (fun j _ => j.val) (fun j _ => mem_range.mpr (ZMod.val_lt j))
    (fun _ _ _ _ he => ZMod.val_injective q he) ?_ ?_
  · intro r hr
    exact ⟨r, mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hr)⟩
  · intro j _
    change f (j+1) = f ((j.val+1:ℕ):ZMod q)
    simp

private theorem sum_residue_blocks {E : Type*} [AddCommMonoid E] {q : ℕ} (hq : 0 < q)
    (N : ℕ) (f : ℕ → E) :
    ∑ n ∈ Icc 1 (q*(N+1)), f n =
      ∑ r ∈ range q, ∑ m ∈ Icc 0 N, f (q*m+r+1) := by
  let S := (range q) ×ˢ (Icc 0 N)
  rw [← sum_product (f := fun p : ℕ × ℕ => f (q*p.2+p.1+1))]
  symm
  refine sum_bij (fun p _ => q*p.2+p.1+1) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨r,m⟩ hp
    obtain ⟨hr,hm⟩ := mem_product.mp hp
    obtain hr := mem_range.mp hr
    have hm := Nat.mul_le_mul_left q (mem_Icc.mp hm).2
    rw [mem_Icc,Nat.mul_succ]; omega
  · rintro ⟨r,m⟩ hp ⟨s,j⟩ hj hh
    obtain hr := mem_range.mp (mem_product.mp hp).1
    obtain hs := mem_range.mp (mem_product.mp hj).1
    change q*m+r+1=q*j+s+1 at hh
    have he : q*m+r=q*j+s := by omega
    have hr' := congrArg (· % q) he
    have hm' := congrArg (· / q) he
    simp [Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hs] at hr'
    simp [Nat.mul_add_div hq,Nat.div_eq_of_lt hr,Nat.div_eq_of_lt hs] at hm'
    exact Prod.ext hr' hm'
  · intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn' : n-1 < q*(N+1) := by have := (mem_Icc.mp hn).2; omega
    refine ⟨⟨(n-1)%q,(n-1)/q⟩, mem_product.mpr
      ⟨mem_range.mpr (Nat.mod_lt _ hq),mem_Icc.mpr ⟨Nat.zero_le _,?_⟩⟩,?_⟩
    · have := (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [Nat.mul_comm] using hn')
      omega
    · change q*((n-1)/q)+(n-1)%q+1=n
      rw [Nat.div_add_mod]; omega

private theorem split_periodic_poly {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) (N : ℕ) (s : ℂ) :
    dirichletPoly (fun n : ℕ => Φ n) (q*(N+1)) s =
      (q:ℂ)^(-s)*∑ r ∈ range q, Φ ((r+1:ℕ):ZMod q)*
        ∑ m ∈ Icc 0 N, ((m:ℂ)+(((r+1:ℕ):ℝ)/q:ℝ))^(-s) := by
  have hq := NeZero.pos q
  rw [dirichletPoly, sum_residue_blocks hq, mul_sum]
  apply sum_congr rfl
  intro r hr
  rw [← mul_assoc, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hχ : Φ ((q*m+r+1:ℕ):ZMod q) = Φ ((r+1:ℕ):ZMod q) := by simp
  rw [hχ, mul_right_comm, mul_comm _ (Φ _)]
  congr 1
  let x := (m:ℝ)+((r+1:ℕ):ℝ)/q
  have he : ((q*m+r+1:ℕ):ℝ) = (q:ℝ)*x := by
    dsimp [x]; push_cast; field_simp; ring
  have hx' : (q:ℂ)^(-s)*(x:ℂ)^(-s) = (((q:ℝ)*x : ℝ):ℂ)^(-s) := by
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ (q:ℝ)) (by dsimp [x]; positivity), Complex.ofReal_natCast]
  rw [← he] at hx'
  simpa only [x,Complex.ofReal_add,Complex.ofReal_natCast] using hx'.symm

private theorem hurwitz_sub_poly_bound {c : ℝ} (hc : 0 < c) (hc' : c < 2*π) :
    ∃ K > 0, ∀ {a : ℝ} {N : ℕ} {σ t : ℝ}, a ∈ Set.Ioc (0:ℝ) 1 → 0 < N → 0 < σ → σ ≤ 1 →
      0 < |t| → |t| ≤ c*N →
      let s := (σ:ℂ)+t*I
      ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s - ∑ m ∈ Icc 0 N, ((m:ℂ)+a)^(-s)‖ ≤
        ((N:ℝ)+1)^(1-σ)/|t|+K*(N:ℝ)^(-σ) := by
  obtain ⟨K,hK,H⟩ := hurwitzZeta_approx_dirichletPoly hc hc'
  refine ⟨K,hK,?_⟩
  intro a N σ t ha hN hσ hσ' ht hTN s
  have hr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : s ≠ 1 := by intro h; have h' := congrArg Complex.im h; simp [s] at h'; simp [h'] at ht
  have hz : 0 < (N:ℝ)+a := add_pos hr ha.1
  have hnorm : |t| ≤ ‖1-s‖ := by simpa [s] using Complex.abs_im_le_norm (1-s)
  have hmain := H ha (N:=N) hσ hs (hTN.trans (by nlinarith [mul_pos hc ha.1]))
  let D := ∑ m ∈ Icc 0 N, ((m:ℂ)+a)^(-s)
  let e := ((N:ℂ)+a)^(1-s)/(1-s)
  have he : ‖e‖ ≤ ((N:ℝ)+1)^(1-σ)/|t| := by
    dsimp [e]
    rw [norm_div, ← Complex.ofReal_natCast, ← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos hz]
    simp only [s,sub_re,one_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
    exact div_le_div₀ (by positivity)
      (Real.rpow_le_rpow hz.le (by linarith only [ha.2]) (by linarith)) ht hnorm
  have herr : K*((N:ℝ)+a)^(-σ) ≤ K*(N:ℝ)^(-σ) := by
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr (by linarith only [ha.1]) (by linarith)) hK.le
  have hb : ‖HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s - (D-e)‖ ≤ K*((N:ℝ)+a)^(-σ) := hmain
  calc _ = ‖(HurwitzZeta.hurwitzZeta (a:UnitAddCircle) s - (D-e)) + (-e)‖ := by congr 1; dsimp [D]; ring
       _ ≤ _ := (norm_add_le ..).trans (by rw [norm_neg,add_comm]; exact add_le_add he (hb.trans herr))

/-- Sharp finite Dirichlet approximation for a bounded periodic coefficient
function. The cutoff `q(N+1)` includes whole periods. The implied constant
depends only on the fixed allowed height-to-length ratio `c < 2π`. -/
theorem periodicLFunction_approx_dirichletPoly {c : ℝ} (hc : 0 < c) (hc' : c < 2*π) :
    ∃ K > 0, ∀ {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ), (∀ j, ‖Φ j‖ ≤ 1) →
      ∀ {N : ℕ} {σ t : ℝ}, 0 < N → 0 < σ → σ ≤ 1 → 0 < |t| → |t| ≤ c*N →
      let s := (σ:ℂ)+t*I
      ‖ZMod.LFunction Φ s-dirichletPoly (fun n : ℕ => Φ n) (q*(N+1)) s‖ ≤
        (q:ℝ)^(1-σ)*(((N:ℝ)+1)^(1-σ)/|t|+K*(N:ℝ)^(-σ)) := by
  obtain ⟨K,hK,H⟩ := hurwitz_sub_poly_bound hc hc'
  refine ⟨K,hK,?_⟩
  intro q _ Φ hΦ N σ t hN hσ hs1 ht hTN s
  let E := ((N:ℝ)+1)^(1-σ)/|t|+K*(N:ℝ)^(-σ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [ZMod.LFunction,split_periodic_poly, ← mul_sub, norm_mul,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos q), sum_residues_succ, ← sum_sub_distrib]
  have hr : (-s).re = -σ := by simp [s]
  rw [hr, sub_eq_add_neg (1:ℝ) σ,Real.rpow_add hq, Real.rpow_one]
  calc _ ≤ (q:ℝ)^(-σ)*(∑ r ∈ range q, E) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply (norm_sum_le ..).trans
            apply sum_le_sum
            intro r hr'
            rw [← mul_sub,norm_mul,ZMod.toAddCircle_natCast]
            have ha : ((r+1:ℕ):ℝ)/q ∈ Set.Ioc (0:ℝ) 1 :=
              ⟨by positivity, (div_le_one hq).mpr (by exact_mod_cast mem_range.mp hr')⟩
            exact (mul_le_mul (hΦ _) (H ha hN hσ hs1 ht hTN) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
       _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,E]; ring

end AnalyticNumberTheory.DirichletLFunctions
