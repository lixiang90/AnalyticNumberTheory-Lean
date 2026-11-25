import AnalyticNumberTheory.AnalyticTools.BarnesHankel
import AnalyticNumberTheory.ModularAndPartitions.EisensteinConeIntegral

/-!
# The Hankel integral in the Eisenstein modular transformation

A common small circle works for the finitely many Barnes kernels.
The modular identity extends from the absolutely convergent lattice
sum to all complex weights by the identity theorem.
-/

open Complex Real Set Finset Filter
open scoped Topology MatrixGroups UpperHalfPlane
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.ModularAndPartitions

/-- Full Hankel representation of the period for every complex weight
when the modular denominator is in the open right half-plane. -/
theorem eisensteinPeriod_eq_hankel (γ : SL(2,ℤ)) (z : ℍ) {c : ℕ}
    (hc : 0<c) (hγ : γ 1 0=(c:ℤ)) (hz : 0<(c:ℝ)*z.re+γ 1 1) :
    ∃ X : ℝ, ∀ s : ℂ, eisensteinPeriod γ z s=
      -Complex.exp (-π*I*s)*(Complex.Gamma s)⁻¹*
        ∑ j : Fin c,barnesHankel (eisensteinBarnesOffset c (γ 1 1) z j) ((c:ℂ)*z+γ 1 1) X s := by
  let a := eisensteinBarnesOffset c (γ 1 1) z
  let b : ℂ := (c:ℂ)*z+γ 1 1
  have hb : 0<b.re := by simpa [b,Complex.mul_re] using hz
  have ha (j : Fin c) := barnesOffset_re_pos hc (γ 1 1) z hz j
  choose R hR using (fun j : Fin c => exists_barnesHankelRadius (a j) (b:=b) (fun e => by rw [e] at hb; simp at hb))
  obtain ⟨X,hX⟩ := (Set.finite_range R).bddBelow
  have hA (j : Fin c) : BarnesHankelRadius (a j) b X := (hR j).mono (hX (mem_range_self j))
  let F (s : ℂ) := -Complex.exp (-π*I*s)*(Complex.Gamma s)⁻¹*∑ j : Fin c,barnesHankel (a j) b X s
  have hF : Differentiable ℂ F := by
    apply Differentiable.mul ((by fun_prop : Differentiable ℂ (fun s : ℂ => -Complex.exp (-π*I*s))).mul Complex.differentiable_one_div_Gamma)
    exact Differentiable.fun_sum fun j _ => differentiable_barnesHankel (ha j) hb (hA j)
  have H (s : ℂ) (hs : 2<s.re) : eisensteinPeriod γ z s=F s := by
    have hci : 0<γ 1 0 := by rw [hγ]; exact_mod_cast hc
    rw [eisensteinPeriod_eq_cone γ z hci hs,hγ,eisensteinConeSum_eq_barnes hc _ z hz hs]
    unfold F
    have he (j : Fin c) : barnesHankel (a j) b X s=(Complex.exp (s*(2*π*I))-1)*(Complex.Gamma s*barnesDoubleZeta (a j) b s) :=
      barnesHankel_eq (ha j) hb (hA j) hs
    simp_rw [he]
    simp_rw [←mul_assoc (Complex.exp (s*(2*π*I))-1) (Complex.Gamma s)]
    rw [←Finset.mul_sum]
    have hgam : Complex.Gamma s≠0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hphase : -Complex.exp (-π*I*s)*(Complex.exp (s*(2*π*I))-1)=Complex.exp (-π*I*s)-Complex.exp (π*I*s) := by
      rw [neg_mul,mul_sub,mul_one,←Complex.exp_add,show -↑π*I*s+s*(2*↑π*I)=↑π*I*s by ring]; ring
    rw [←hphase]
    let U := -Complex.exp (-π*I*s)
    let V := Complex.exp (s*(2*π*I))-1
    let Z := ∑ j : Fin c, barnesDoubleZeta (a j) b s
    change U*V*Z=U*(Complex.Gamma s)⁻¹*(V*Complex.Gamma s*Z)
    field_simp
  have f₁ : AnalyticOnNhd ℂ (eisensteinPeriod γ z) univ := fun s _ => (differentiable_eisensteinPeriod γ z).analyticAt s
  have f₂ : AnalyticOnNhd ℂ F univ := fun s _ => hF.analyticAt s
  have heq : eisensteinPeriod γ z=F := f₁.eq_of_eventuallyEq f₂ (z₀:=(3:ℂ))
    ((Complex.continuous_re.continuousAt.eventually_const_lt (by norm_num : 2<(3:ℂ).re)).mono fun s hs => H s hs)
  exact ⟨X,congrFun heq⟩

end AnalyticNumberTheory.ModularAndPartitions
