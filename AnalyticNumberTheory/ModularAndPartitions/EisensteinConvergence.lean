import AnalyticNumberTheory.ModularAndPartitions.EisensteinLattice

/-!
# The abscissa of absolute convergence of the Eisenstein lattice

In the triangular sector `1 ≤ n ≤ m`, a row contains `m` comparable
terms. At real part two its row norm dominates a constant times `1/m`.
-/

open Complex Real Filter Finset
open scoped UpperHalfPlane Topology
namespace AnalyticNumberTheory.ModularAndPartitions

/-- Absolute convergence of the lattice series holds exactly to the
right of the line of real part two, for the stated logarithm branch. -/
theorem summable_eisensteinLatticeTerm_iff (z : ℍ) (s : ℂ) :
    (Summable fun v : ℤ×ℤ => eisensteinLatticeTerm z s v.1 v.2) ↔ 2<s.re := by
  refine ⟨?_,summable_eisensteinLatticeTerm z⟩
  intro h
  by_contra! hs
  let f (m n : ℕ) := ‖eisensteinLatticeTerm z s m n‖
  let F (m : ℕ) := ∑' n : ℕ,f m n
  have hf : Summable fun p : ℕ×ℕ => f p.1 p.2 := by
    let g := Prod.map (Nat.cast : ℕ→ℤ) (Nat.cast : ℕ→ℤ)
    have hg : Function.Injective g := Function.Injective.prodMap Nat.cast_injective Nat.cast_injective
    simpa only [Function.comp_def,g,f,Prod.map_fst,Prod.map_snd] using h.norm.comp_injective hg
  have hF : Summable F := hf.prod
  let C := (1+‖(z:ℂ)‖)^2*Real.exp (π*|s.im|)
  have hC : 0<C := by dsimp [C]; positivity
  apply Real.not_summable_natCast_inv
  apply Summable.of_norm_bounded_eventually (hF.mul_left C)
  have hcast : ∀ᶠ m : ℕ in atTop, (z.im)⁻¹≤(m:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hcast,eventually_ge_atTop 1] with m hm hm'
  have hm0 : 0<(m:ℝ) := by exact_mod_cast hm'
  have hmi : 1≤(m:ℝ)*z.im := (div_le_iff₀ z.im_pos).mp (by simpa only [one_div] using hm)
  have hlocal (n : ℕ) (hn : n∈Icc 1 m) : ((m:ℝ)^2)⁻¹≤C*f m n := by
    let w : ℂ := (m:ℂ)*z+n
    have hi : w.im=(m:ℝ)*z.im := by simp [w,Complex.mul_im]
    have hw : 1≤‖w‖ := hmi.trans (hi ▸ Complex.im_le_norm w)
    have hw' : w≠0 := by intro h; norm_num [h] at hw
    have htop : ‖w‖≤(m:ℝ)*(1+‖(z:ℂ)‖) := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast]
      linarith only [show (n:ℝ)≤m by exact_mod_cast (mem_Icc.mp hn).2]
    have hb := Real.rpow_le_rpow_of_nonpos (show 0<‖w‖ by linarith) htop (by norm_num : (-2:ℝ)≤0)
    have hb' := Real.rpow_le_rpow_of_exponent_le hw (by linarith : (-2:ℝ)≤ -s.re)
    have hwgt : Real.exp (w.arg*(-s).im)≤Real.exp (π*|s.im|) := by
      apply Real.exp_le_exp.mpr
      have harg : |w.arg|≤π := abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩
      calc _ ≤ |w.arg*(-s).im| := le_abs_self _
           _ = |w.arg| * |s.im| := by simp [abs_mul]
           _ ≤ _ := mul_le_mul_of_nonneg_right harg (abs_nonneg _)
    have hterm : f m n=‖w^(-s)‖ := by simp [f,eisensteinLatticeTerm,w,show (0:ℤ)<m by exact_mod_cast hm',show m≠0 by omega,show 0<m by omega]
    rw [hterm]
    have he := (div_le_iff₀ (Real.exp_pos (w.arg*(-s).im))).mp (Complex.norm_cpow_of_ne_zero hw' (-s)).symm.le
    simp only [Complex.neg_re] at he
    have hh := (hb.trans hb').trans (he.trans (mul_le_mul_of_nonneg_left hwgt (norm_nonneg _)))
    rw [show (-2:ℝ)= -(2:ℝ) by norm_num,Real.rpow_neg (by positivity),Real.rpow_two,mul_pow,mul_inv_rev] at hh
    have hc' : 0<(1+‖(z:ℂ)‖)^2 := by positivity
    have H := mul_le_mul_of_nonneg_left hh hc'.le
    dsimp [C]; calc
      _ = (1+‖(z:ℂ)‖)^2*((((1+‖(z:ℂ)‖)^2)⁻¹)*((m:ℝ)^2)⁻¹) := by field_simp
      _ ≤ _ := H.trans_eq (by ring)
  have H := sum_le_sum (s:=Icc 1 m) (fun n hn => hlocal n hn)
  rw [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,←mul_sum] at H
  have hsum := (hf.prod_factor m).sum_le_tsum (Icc 1 m) (fun n _ => norm_nonneg _)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hm0.le)]
  calc (m:ℝ)⁻¹ = (m:ℝ)*((m:ℝ)^2)⁻¹ := by field_simp
       _ ≤ _ := H.trans (mul_le_mul_of_nonneg_left hsum hC.le)

end AnalyticNumberTheory.ModularAndPartitions
