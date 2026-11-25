import AnalyticNumberTheory.ModularAndPartitions.EisensteinLattice

/-!
# The logarithm branch in Eisenstein transformations

Conjugating the principal power gives the branch with argument in
`[-π,π)`, including the negative real ray. Its multiplicative defect
is a single winding factor when the first base lies in the upper half-plane.
-/

open Complex Real
open scoped ComplexConjugate UpperHalfPlane
namespace AnalyticNumberTheory.ModularAndPartitions

/-- The inverse complex power with the negative real ray assigned argument `-π`. -/
noncomputable def eisensteinInversePower (w s : ℂ) : ℂ := conj ((conj w)^(-conj s))

/-- Away from the negative real axis, this convention agrees with the principal power. -/
theorem eisensteinInversePower_eq_cpow {w : ℂ} (hw : w.arg≠π) (s : ℂ) :
    eisensteinInversePower w s=w^(-s) := by
  rw [eisensteinInversePower,←Complex.cpow_conj w (-conj s) hw]
  simp

private theorem reflected_neg_one_power (s : ℂ) :
    conj ((-1:ℂ)^(-conj s))=eisensteinReflection s := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num),Complex.log_neg_one,←Complex.exp_conj]
  simp [eisensteinReflection]

/-- Opposite rays, taking the upper representative first. -/
theorem eisensteinInversePower_neg {w : ℂ} (hw : 0≤w.im) (hw' : w.arg≠π) (s : ℂ) :
    eisensteinInversePower (-w) s=eisensteinReflection s*w^(-s) := by
  have ha : (conj w).arg= -w.arg := by rw [Complex.arg_conj,if_neg hw']
  have hb := Complex.arg_nonneg_iff.mpr hw
  have hcut : (-1:ℂ).arg+(conj w).arg∈Set.Ioc (-π) π := by
    rw [Complex.arg_neg_one,ha]; constructor <;> linarith [Complex.arg_le_pi w,Real.pi_pos]
  rw [eisensteinInversePower,map_neg,←neg_one_mul (conj w),Complex.mul_cpow hcut,
    map_mul,reflected_neg_one_power]
  exact congrArg (eisensteinReflection s * ·) (eisensteinInversePower_eq_cpow hw' s)

/-- The lattice definition is the lower-cut power of the lattice vector. -/
theorem eisensteinLatticeTerm_eq_inversePower (z : ℍ) {s : ℂ} (hs : s≠0) (m n : ℤ) :
    eisensteinLatticeTerm z s m n=eisensteinInversePower ((m:ℂ)*(z:ℂ)+n) s := by
  let w : ℂ := (m:ℂ)*z+n
  have hi : w.im=(m:ℝ)*z.im := by simp [w,Complex.mul_im]
  have harg {u : ℂ} (h : 0<u.im ∨ 0<u.re ∧ u.im=0) : u.arg≠π := by
    intro he; have hh := Complex.arg_eq_pi_iff.mp he; rcases h with h | h <;> linarith [hh.1,hh.2]
  rw [eisensteinLatticeTerm]
  split_ifs with h h
  · rcases h with ⟨rfl,rfl⟩
    have hn : -conj s≠0 := by simpa using hs
    simp [eisensteinInversePower,Complex.zero_cpow hn]
  · change w^(-s)=eisensteinInversePower w s
    apply (eisensteinInversePower_eq_cpow _ _).symm
    apply harg
    rcases h with h | ⟨rfl,hn⟩
    · exact Or.inl (hi ▸ mul_pos (Int.cast_pos.mpr h) z.im_pos)
    · right; simp [w,hn]
  · change eisensteinReflection s*(-w)^(-s)=eisensteinInversePower w s
    have hw : 0<(-w).im ∨ 0<(-w).re ∧ (-w).im=0 := by
      by_cases hzero : m=0
      · subst m; right
        have hn : n<0 := by omega
        simp [w,hn]
      · left
        have hm : m<0 := by omega
        rw [Complex.neg_im,hi]; exact neg_pos.mpr (mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hm) z.im_pos)
    have hi' : 0≤(-w).im := hw.elim (·.le) (fun h => h.2.ge)
    simpa only [neg_neg] using (eisensteinInversePower_neg hi' (harg hw) s).symm

/-- Multiplying a vector by `j` in the upper half-plane winds once
precisely when the two conjugate arguments cross the lower cut. -/
def eisensteinBranchCrossing (j w : ℂ) : Prop := (conj j).arg+(conj w).arg≤ -π

noncomputable instance (j w : ℂ) : Decidable (eisensteinBranchCrossing j w) := Classical.propDecidable _

/-- The winding multiplier of the lower-cut inverse power. -/
theorem eisensteinInversePower_mul {j : ℂ} (hj : 0<j.im) (w s : ℂ) :
    j^(-s)*eisensteinInversePower w s=
      (if eisensteinBranchCrossing j w then Complex.exp (-2*π*I*s) else 1)*
        eisensteinInversePower (j*w) s := by
  have harg : j.arg≠π := fun h => (ne_of_gt hj) (Complex.arg_eq_pi_iff.mp h).2
  rw [←eisensteinInversePower_eq_cpow harg]
  unfold eisensteinInversePower
  rw [map_mul]
  by_cases h : eisensteinBranchCrossing j w
  · rw [if_pos h,Complex.mul_cpow_of_le_neg_pi h,map_mul,map_mul,←Complex.exp_conj]
    simp only [map_mul,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I,Complex.conj_conj]
    rw [show 2*(π:ℂ)*(-I)*(-s) = -(-2*π*I*s) by ring,Complex.exp_neg]
    field_simp
  · have hcut : (conj j).arg+(conj w).arg∈Set.Ioc (-π) π := by
      refine ⟨lt_of_not_ge h,?_⟩
      have hneg : (conj j).arg<0 := Complex.arg_neg_iff.mpr (by simpa)
      linarith [Complex.arg_le_pi (conj w)]
    rw [if_neg h,one_mul,Complex.mul_cpow hcut,map_mul]

/-- The winding sector is determined by the signs of the imaginary
parts of the original and transformed vector. Its boundary on the
negative real ray belongs to the crossing sector. -/
theorem eisensteinBranchCrossing_iff {j w : ℂ} (hj : 0<j.im) :
    eisensteinBranchCrossing j w ↔ 0<w.im ∧ (j*w).im≤0 := by
  have arg_pos {u : ℂ} (hu : 0<u.im) : 0<u.arg ∧ u.arg<π := by
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hu.le) (fun he => ?_),
      Complex.arg_lt_pi_iff.mpr (Or.inr hu.ne')⟩
    exact hu.ne' (Complex.arg_eq_zero_iff.mp he.symm).2
  have im_pos {u : ℂ} (h₁ : 0<u.arg) (h₂ : u.arg<π) : 0<u.im := by
    obtain h|h := (Complex.arg_nonneg_iff.mp h₁.le).lt_or_eq
    · exact h
    · by_cases hr : u.re<0
      · exact (h₂.ne (Complex.arg_eq_pi_iff.mpr ⟨hr,h.symm⟩)).elim
      · exact (h₁.ne' (Complex.arg_eq_zero_iff.mpr ⟨not_lt.mp hr,h.symm⟩)).elim
  by_cases hw : 0<w.im
  swap
  · have hn : 0≤(conj w).arg := Complex.arg_nonneg_iff.mpr (by simpa using (neg_nonneg.mpr (not_lt.mp hw)))
    have hnj := Complex.neg_pi_lt_arg (conj j)
    simp only [eisensteinBranchCrossing,hw,false_and,iff_false,not_le]; linarith
  have ⟨hj₁,hj₂⟩ := arg_pos hj
  have ⟨hw₁,hw₂⟩ := arg_pos hw
  simp only [eisensteinBranchCrossing,Complex.arg_conj,if_neg hj₂.ne,if_neg hw₂.ne,hw,true_and]
  rcases lt_trichotomy (j.arg+w.arg) π with h | h | h
  · have harg := Complex.arg_mul (by intro he; simp [he] at hj) (by intro he; simp [he] at hw)
      (show j.arg+w.arg∈Set.Ioc (-π) π from ⟨by linarith [Real.pi_pos],h.le⟩)
    have hz := im_pos (u:=j*w) (by rw [harg]; linarith) (by rw [harg]; exact h)
    constructor <;> intro H <;> linarith
  · have harg := Complex.arg_mul (by intro he; simp [he] at hj) (by intro he; simp [he] at hw)
      (show j.arg+w.arg∈Set.Ioc (-π) π from ⟨by linarith [Real.pi_pos],h.le⟩)
    have hz := (Complex.arg_eq_pi_iff.mp (harg.trans h)).2
    constructor <;> intro H <;> linarith
  · have harg := Complex.arg_mul_of_pi_lt h
    have hz : (j*w).im<0 := Complex.arg_neg_iff.mp (by rw [harg]; linarith)
    constructor <;> intro H <;> linarith

end AnalyticNumberTheory.ModularAndPartitions
