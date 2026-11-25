import AnalyticNumberTheory.ModularAndPartitions.EisensteinPeriods
import AnalyticNumberTheory.AnalyticTools.BarnesDoubleZeta

/-!
# Mellin representation of the modular correction

Dividing the first lattice coordinate by `c` splits the angular cone
into `c` Barnes double zeta series. Their Mellin kernels are products
of two geometric denominators.
-/

open Complex Real Finset Set MeasureTheory
open scoped UpperHalfPlane Topology
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.ModularAndPartitions

private def coneIndices (c d : ℤ) := {v : Fin 2→ℤ // 0≤v 0 ∧ d*v 0<c*v 1}

private def coneEnumeration {c : ℤ} (hc : 0<c) (d : ℤ) : (ℕ×ℕ) ≃ coneIndices c d where
  toFun p := ⟨![p.1,d*(p.1:ℤ)/c+p.2+1],by
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    refine ⟨Int.natCast_nonneg _,?_⟩
    rw [mul_comm c,←Int.ediv_lt_iff_lt_mul hc]; omega⟩
  invFun v := ⟨(v.1 0).toNat,(v.1 1-d*(v.1 0)/c-1).toNat⟩
  left_inv p := by
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Int.toNat_natCast]
    congr 1; omega
  right_inv v := by
    have h₁ := v.2.1
    have h₂ := (Int.ediv_lt_iff_lt_mul hc).mpr (by simpa only [mul_comm c] using v.2.2)
    apply Subtype.ext
    funext i
    fin_cases i
    · change ((v.1 0).toNat:ℤ)=v.1 0
      exact Int.toNat_of_nonneg h₁
    · change d*((v.1 0).toNat:ℤ)/c+((v.1 1-d*(v.1 0)/c-1).toNat:ℤ)+1=v.1 1
      rw [Int.toNat_of_nonneg h₁,Int.toNat_of_nonneg (by omega : 0≤v.1 1-d*(v.1 0)/c-1)]
      omega

/-- The offset of the Barnes lattice for the residue class `j mod c`. -/
noncomputable def eisensteinBarnesOffset (c : ℕ) (d : ℤ) (z : ℍ) (j : Fin c) : ℂ :=
  (j:ℕ)*(z:ℂ)+((d*(j:ℕ)/(c:ℤ):ℤ):ℂ)+1

/-- The real part of each offset is positive on the right of the cusp. -/
theorem barnesOffset_re_pos {c : ℕ} (hc : 0<c) (d : ℤ) (z : ℍ)
    (hz : 0<((c:ℝ)*z.re+d)) (j : Fin c) :
    0<(eisensteinBarnesOffset c d z j).re := by
  have hc' : 0<(c:ℤ) := by exact_mod_cast hc
  have hcr : 0<(c:ℝ) := by exact_mod_cast hc
  have hr := Int.emod_lt_of_pos (d*(j:ℕ)) hc'
  have hdiv := Int.emod_add_mul_ediv (d*(j:ℕ)) (c:ℤ)
  rw [add_comm] at hdiv
  have h₁ : (c:ℝ)*(↑(d*(j:ℕ)/(c:ℤ):ℤ):ℝ)+↑(d*(j:ℕ)%(c:ℤ):ℤ)=(d:ℝ)*(j:ℕ) := by exact_mod_cast hdiv
  have h₂ : (↑(d*(j:ℕ)%(c:ℤ):ℤ):ℝ)<c := by exact_mod_cast hr
  simp only [eisensteinBarnesOffset,Complex.add_re,Complex.one_re,Complex.mul_re,Complex.natCast_im,
    zero_mul,sub_zero,Complex.natCast_re,Complex.intCast_re]
  apply (mul_pos_iff_of_pos_left hcr).mp
  change 0<(c:ℝ)*(z:ℂ).re+d at hz
  have hj : 0≤((j:ℕ):ℝ) := Nat.cast_nonneg _
  nlinarith only [h₁,h₂,mul_nonneg hj hz.le]

/-- Splitting the cone into Barnes double zeta series works everywhere
in the upper half-plane, including to the left of the cusp. -/
theorem eisensteinConeSum_eq_barnes_upperHalfPlane {c : ℕ} (hc : 0<c) (d : ℤ) (z : ℍ)
    {s : ℂ} (hs : 2<s.re) :
    eisensteinConeSum c d z s=∑ j : Fin c,barnesDoubleZeta (eisensteinBarnesOffset c d z j)
      ((c:ℂ)*z+d) s := by
  letI : NeZero c := ⟨hc.ne'⟩
  have hc' : 0<(c:ℤ) := by exact_mod_cast hc
  let V (v : Fin 2→ℤ) := ((v 0:ℂ)*(z:ℂ)+v 1)^(-s)
  let E : Fin c × (ℕ×ℕ) ≃ coneIndices c d :=
    ((Equiv.prodAssoc (Fin c) ℕ ℕ).symm.trans ((Equiv.prodCongr
      ((Equiv.prodComm (Fin c) ℕ).trans (Nat.divModEquiv c).symm) (Equiv.refl ℕ)).trans (coneEnumeration hc' d)))
  have he (p : Fin c × (ℕ×ℕ)) : V (E p).1=
      (barnesVector (eisensteinBarnesOffset c d z p.1) ((c:ℂ)*z+d) p.2)^(-s) := by
    let j := p.1
    let m := p.2.1
    let n := p.2.2
    have hd : d*((m*c+j:ℕ):ℤ)/(c:ℤ)=d*m+d*(j:ℕ)/c := by
      push_cast; rw [show d*((m:ℤ)*c+j)=c*(d*m)+d*j by ring,Int.mul_add_ediv_left _ _ hc'.ne']
    change ((((m*c+j:ℕ):ℂ)*(z:ℂ)+((d*((m*c+j:ℕ):ℤ)/c+n+1:ℤ):ℂ)))^(-s)=_
    rw [hd]
    unfold barnesVector eisensteinBarnesOffset; push_cast; dsimp only [m,n,j]; ring_nf
  have hsum : Summable fun p : Fin c × (ℕ×ℕ) =>
      (barnesVector (eisensteinBarnesOffset c d z p.1) ((c:ℂ)*z+d) p.2)^(-s) := by
    have hw : Summable fun v : Fin 2→ℤ => eisensteinLatticeTerm z s (v 0) (v 1) :=
      (finTwoArrowEquiv ℤ).summable_iff.mpr (summable_eisensteinLatticeTerm z hs)
    have hv : Summable fun v : coneIndices c d => V v.1 := by
      apply (hw.subtype (fun u : Fin 2→ℤ => 0≤u 0 ∧ d*u 0<(c:ℤ)*u 1)).congr
      intro v
      have hpos : 0<v.1 0 ∨ v.1 0=0 ∧ 0<v.1 1 := by
        rcases v.2.1.eq_or_lt with hm|hm
        · right; refine ⟨hm.symm,?_⟩
          have hn := v.2.2; rw [←hm,mul_zero] at hn
          exact (mul_pos_iff_of_pos_left hc').mp hn
        · exact Or.inl hm
      have hn : ¬(v.1 0=0 ∧ v.1 1=0) := by rcases hpos with h|⟨_,h⟩ <;> omega
      simp only [Function.comp_apply,eisensteinLatticeTerm,if_neg hn,if_pos hpos,V]
    exact (E.summable_iff.mpr hv).congr he
  have hs' : eisensteinConeSum c d z s=∑' v : coneIndices c d,V v.1 := by
    classical
    change _=∑' v : {u : Fin 2→ℤ | 0≤u 0 ∧ d*u 0<(c:ℤ)*u 1},V v.1
    rw [_root_.tsum_subtype]
    unfold eisensteinConeSum
    apply tsum_congr; intro v
    by_cases hv : 0≤v 0 ∧ d*v 0<(c:ℤ)*v 1
    · rw [if_pos hv,Set.indicator_of_mem hv]; rfl
    · change (if 0≤v 0 ∧ d*v 0<(c:ℤ)*v 1 then _ else 0)=_
      rw [if_neg hv,Set.indicator_of_notMem hv]
  rw [hs',←E.tsum_eq]
  simp_rw [he]; rw [hsum.tsum_prod,tsum_fintype]; rfl

/-- Specialization to the domain of the positive-axis Mellin integral. -/
theorem eisensteinConeSum_eq_barnes {c : ℕ} (hc : 0<c) (d : ℤ) (z : ℍ)
    (_hz : 0<((c:ℝ)*z.re+d)) {s : ℂ} (hs : 2<s.re) :
    eisensteinConeSum c d z s=∑ j : Fin c,barnesDoubleZeta (eisensteinBarnesOffset c d z j)
      ((c:ℂ)*z+d) s := eisensteinConeSum_eq_barnes_upperHalfPlane hc d z hs

/-- Mellin integral formula for the correction cone in the half-plane
of absolute convergence. Each term has explicit offset and modular denominator. -/
theorem eisensteinConeSum_gamma_eq_integral {c : ℕ} (hc : 0<c) (d : ℤ) (z : ℍ)
    (hz : 0<((c:ℝ)*z.re+d)) {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*eisensteinConeSum c d z s=
      ∑ j : Fin c,∫ t : ℝ in Ioi 0,barnesKernel (eisensteinBarnesOffset c d z j) ((c:ℂ)*z+d) t*(t:ℂ)^(s-1) := by
  rw [eisensteinConeSum_eq_barnes hc d z hz hs,mul_sum]
  apply sum_congr rfl; intro j _
  exact (integral_barnesKernel (barnesOffset_re_pos hc d z hz j) (by simpa [Complex.mul_re] using hz) hs).symm

end AnalyticNumberTheory.ModularAndPartitions
