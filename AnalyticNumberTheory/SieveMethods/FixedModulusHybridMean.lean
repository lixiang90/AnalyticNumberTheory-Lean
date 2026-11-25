import AnalyticNumberTheory.SieveMethods.WeightedMeanValues
import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentOrthogonality

/-!
# Hybrid mean squares at a single modulus

Orthogonality divides the Dirichlet polynomial into residue classes.
Logarithmic frequencies in one class are separated by at least q/N;
the individual spacing at n is at least q/(n+q).
-/
noncomputable section
open Real Complex Finset MeasureTheory
open scoped Classical
open AnalyticNumberTheory.AnalyticTools AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.SieveMethods

private def residueBlock (q N : ℕ) (r : ZMod q) : Finset ℕ :=
  (Icc 1 N).filter fun (n : ℕ) => (n:ZMod q)=r

private theorem log_gap {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    (v-u)/v ≤ Real.log v-Real.log u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne'] at h
  have he : (v-u)/v=1-u/v := by field_simp
  linarith

private theorem same_residue_spacing {q N i j : ℕ} {r : ZMod q}
    (hi : i∈residueBlock q N r) (hj : j∈residueBlock q N r) (hij : i<j) :
    (q:ℝ)/N ≤ Real.log j-Real.log i ∧
    (q:ℝ)/(i+q) ≤ Real.log j-Real.log i ∧
    (q:ℝ)/(j+q) ≤ Real.log j-Real.log i := by
  obtain ⟨hi',hir⟩ := mem_filter.mp hi
  obtain ⟨hj',hjr⟩ := mem_filter.mp hj
  obtain ⟨hi₁,_⟩ := mem_Icc.mp hi'
  obtain ⟨hj₁,hjN⟩ := mem_Icc.mp hj'
  have hd := ((ZMod.natCast_eq_natCast_iff ..).mp (hir.trans hjr.symm)).add_le_of_lt hij
  have hd' : (i:ℝ)+q ≤ j := by exact_mod_cast hd
  have hi₀ : 0<(i:ℝ) := by exact_mod_cast hi₁
  have hj₀ : 0<(j:ℝ) := by exact_mod_cast hj₁
  have hv : 0<(i:ℝ)+q := by positivity
  have h := log_gap hi₀ hj₀
  have hq : (q:ℝ)/j ≤ Real.log j-Real.log i :=
    (div_le_div_of_nonneg_right (by linarith : (q:ℝ)≤j-i) hj₀.le).trans h
  refine ⟨(div_le_div_of_nonneg_left (Nat.cast_nonneg _) hj₀ (by exact_mod_cast hjN)).trans hq,?_,?_⟩
  · have hh := log_gap hi₀ hv
    rw [add_sub_cancel_left] at hh
    linarith [Real.log_le_log hv hd']
  · exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hj₀ (by linarith [Nat.cast_nonneg (α:=ℝ) q])).trans hq

private def phaseTerm (a : ℕ→ℂ) (n:ℕ) (t:ℝ) :=
  a n*cexp (I*((-Real.log n:ℝ):ℂ)*t)

private def residuePoly (a : ℕ→ℂ) {q : ℕ} (N : ℕ) (r:ZMod q) (t:ℝ) :=
  ∑n∈residueBlock q N r,phaseTerm a n t

private def characterPoly (a : ℕ→ℂ) {q : ℕ} (N : ℕ) (χ:DirichletCharacter ℂ q) (t:ℝ) :=
  ∑n∈Icc 1 N,χ n*phaseTerm a n t

private theorem characterPoly_eq (a : ℕ→ℂ) {q : ℕ} (N : ℕ) (χ:DirichletCharacter ℂ q) (t:ℝ) :
    (∑n∈Icc 1 N,a n*χ n*(n:ℂ)^(-(I*(t:ℂ))))=characterPoly a N χ t := by
  apply sum_congr rfl
  intro n hn
  have hn₀ : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
  rw [Complex.cpow_def_of_ne_zero hn₀,←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n)]
  dsimp only [phaseTerm];push_cast;ring_nf

private theorem characterPoly_split (a : ℕ→ℂ) {q : ℕ} [NeZero q] (N : ℕ) (χ:DirichletCharacter ℂ q) (t:ℝ) :
    characterPoly a N χ t = ∑r : ZMod q,χ r*residuePoly a N r t := by
  unfold characterPoly
  have hm : ∀n∈Icc 1 N,(n:ZMod q)∈(univ : Finset (ZMod q)) := fun _ _ => mem_univ _
  rw [←sum_fiberwise_of_maps_to hm]
  apply sum_congr rfl;intro r _
  rw [residuePoly,mul_sum]
  apply sum_congr rfl;intro n hn
  rw [(mem_filter.mp hn).2]

private theorem residue_energy (a : ℕ→ℂ) (q N : ℕ) [NeZero q] (t:ℝ) :
    (∑χ : DirichletCharacter ℂ q,‖characterPoly a N χ t‖^2)≤q.totient*∑r : ZMod q,‖residuePoly a N r t‖^2 := by
  simp_rw [characterPoly_split];rw [dirichlet_character_parseval]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum;intro r _;split_ifs <;> first | rfl | positivity

private theorem continuous_residue_energy (a : ℕ→ℂ) {q : ℕ} (N : ℕ) (r:ZMod q) :
    Continuous fun t => ‖residuePoly a N r t‖^2 := by unfold residuePoly phaseTerm;fun_prop

private theorem continuous_character_energy (a : ℕ→ℂ) {q : ℕ} (N : ℕ) (χ:DirichletCharacter ℂ q) :
    Continuous fun t => ‖characterPoly a N χ t‖^2 := by unfold characterPoly phaseTerm;fun_prop

private theorem integral_residue_energy (a : ℕ→ℂ) (q N : ℕ) [NeZero q] {A B : ℝ} (hAB : A≤B) :
    (∑χ : DirichletCharacter ℂ q,∫ t in A..B,‖characterPoly a N χ t‖^2)≤
      q.totient*∑r : ZMod q,∫t in A..B,‖residuePoly a N r t‖^2 := by
  rw [←intervalIntegral.integral_finsetSum (f:=fun χ t => ‖characterPoly a N χ t‖^2)
    fun χ _ => (continuous_character_energy a N χ).intervalIntegrable ..,
    ←intervalIntegral.integral_finsetSum (f:=fun r t => ‖residuePoly a N r t‖^2)
      fun r _ => (continuous_residue_energy a N r).intervalIntegrable ..,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono hAB _ _ (residue_energy a q N)
  · exact (continuous_finsetSum _ fun χ _ => continuous_character_energy a N χ).intervalIntegrable ..
  · exact (continuous_const.mul (continuous_finsetSum _ fun r _ => continuous_residue_energy a N r)).intervalIntegrable ..

private theorem mean_of_residue_bounds {q N : ℕ} [NeZero q] (a : ℕ→ℂ) (w : ℕ→ℝ)
    {A B : ℝ} (hAB : A≤B) (H : ∀r : ZMod q,
      (∫t in A..B,‖∑n∈residueBlock q N r,a n*cexp (I*((-Real.log n:ℝ):ℂ)*t)‖^2)≤
        ∑n∈residueBlock q N r,w n) :
    (∑χ : DirichletCharacter ℂ q,∫t in A..B,
      ‖∑n∈Icc 1 N,a n*χ n*(n:ℂ)^(-(I*(t:ℂ)))‖^2) ≤ q.totient*∑n∈Icc 1 N,w n := by
  simp_rw [characterPoly_eq]
  apply (integral_residue_energy a q N hAB).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hm : ∀n∈Icc 1 N,(n:ZMod q)∈(univ : Finset (ZMod q)) := fun _ _ => mem_univ _
  exact (sum_le_sum fun r _ => H r).trans_eq (sum_fiberwise_of_maps_to hm w)

/-- The hybrid mean square over all characters of a fixed modulus, retaining φ(q). -/
theorem fixed_modulus_hybrid_mean_square {q N : ℕ} [NeZero q] (hN : 1≤N)
    (a : ℕ→ℂ) {A B : ℝ} (hAB : A≤B) :
    (∑χ : DirichletCharacter ℂ q,∫t in A..B,‖∑n∈Icc 1 N,a n*χ n*(n:ℂ)^(-(I*(t:ℂ)))‖^2) ≤
      q.totient*((B-A)+2*Real.pi*N/q)*(∑n∈Icc 1 N,‖a n‖^2) := by
  rw [mul_assoc,mul_sum]
  apply mean_of_residue_bounds a _ hAB
  intro r
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hN' : 0<(N:ℝ) := by exact_mod_cast hN
  have hsep (i) (hi : i∈residueBlock q N r) (j) (hj : j∈residueBlock q N r) (hij : i≠j) :
      (q:ℝ)/N≤|-Real.log i- -Real.log j| := by
    rcases lt_or_gt_of_ne hij with h|h
    · simpa only [sub_neg_eq_add,neg_add_eq_sub] using
        ((same_residue_spacing hi hj h).1.trans (le_abs_self _))
    · rw [abs_sub_comm]
      simpa only [sub_neg_eq_add,neg_add_eq_sub] using
        ((same_residue_spacing hj hi h).1.trans (le_abs_self _))
  have h := le_abs_self _ |>.trans (separated_frequency_mean_square (residueBlock q N r)
    (fun n => -Real.log n) a (div_pos hq hN') hsep A B)
  rw [←mul_sum]
  rw [inv_div] at h
  convert (by linarith only [h] :
    (∫t in A..B,‖∑n∈residueBlock q N r,a n*cexp (I*((-Real.log n:ℝ):ℂ)*t)‖^2)≤
      (B-A)*(∑n∈residueBlock q N r,‖a n‖^2)+2*Real.pi*(N/q)*(∑n∈residueBlock q N r,‖a n‖^2)) using 1 <;>ring

/-- Individual frequency spacings give a length-free weighted remainder in the full family. -/
theorem fixed_modulus_hybrid_weighted_mean_square {q N : ℕ} [NeZero q]
    (a : ℕ→ℂ) {A B : ℝ} (hAB : A≤B) :
    (∑χ : DirichletCharacter ℂ q,∫t in A..B,‖∑n∈Icc 1 N,a n*χ n*(n:ℂ)^(-(I*(t:ℂ)))‖^2) ≤
      q.totient*((B-A)*(∑n∈Icc 1 N,‖a n‖^2)+
        2*weightedHilbertConstant*(∑n∈Icc 1 N,(1+(n:ℝ)/q)*‖a n‖^2)) := by
  rw [mul_sum,mul_sum,←sum_add_distrib]
  apply mean_of_residue_bounds a _ hAB
  intro r
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  let δ (n:ℕ) := (q:ℝ)/(n+q)
  have hδ (n : ℕ) : 0<δ n := by dsimp [δ];positivity
  have hs (i) (hi : i∈residueBlock q N r) (j) (hj : j∈residueBlock q N r) (hij : i≠j) :
      δ i≤|-Real.log i- -Real.log j| := by
    rcases lt_or_gt_of_ne hij with h|h
    · simpa only [sub_neg_eq_add,neg_add_eq_sub] using
        ((same_residue_spacing hi hj h).2.1.trans (le_abs_self _))
    · rw [abs_sub_comm]
      simpa only [sub_neg_eq_add,neg_add_eq_sub] using
        ((same_residue_spacing hj hi h).2.2.trans (le_abs_self _))
  have h := le_abs_self _ |>.trans (weighted_frequency_mean_square (residueBlock q N r)
    (fun n => -Real.log n) δ a (fun n _ => hδ n) hs A B)
  have he (n : ℕ) : ‖a n‖^2/δ n=(1+(n:ℝ)/q)*‖a n‖^2 := by
    dsimp [δ];field_simp;ring
  simp_rw [he] at h
  rw [sum_add_distrib,←mul_sum,←mul_sum]
  linarith only [h]

end AnalyticNumberTheory.SieveMethods
