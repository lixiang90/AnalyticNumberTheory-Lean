import AnalyticNumberTheory.DirichletLFunctions.CharacterMomentOrthogonality
import AnalyticNumberTheory.PrimeDistribution.ArithmeticProgressions

/-! # The variance in arithmetic progressions as a character second moment -/
noncomputable section
open Real Complex Finset
open scoped ArithmeticFunction.vonMangoldt Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

/-- Sum of the squared errors in the reduced residue classes of one modulus,
with the common reference numerator m. -/
def progressionVariance (x m : ℝ) (q : ℕ) [NeZero q] : ℝ :=
  ∑ r : ZMod q,if IsUnit r then (psiAP x q r.val-m/(q.totient:ℝ))^2 else 0

private theorem psiChar_residue_transform {q : ℕ} [NeZero q] (x : ℝ) (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q,χ r*(psiAP x q r.val:ℂ))=psiChar x χ := by
  simp only [psiAP,Complex.ofReal_sum,sum_filter,Complex.ofReal_zero,apply_ite,Complex.ofReal_zero,
    mul_sum,mul_ite,mul_zero]
  rw [sum_comm];apply sum_congr rfl;intro n hn
  have he (r : ZMod q) : (n ≡ r.val [MOD q]) ↔ (n:ZMod q)=r := by
    rw [←ZMod.natCast_eq_natCast_iff,ZMod.natCast_zmod_val]
  simp [he]

/-- Parseval with an arbitrary common centering. Only the principal Fourier
coefficient changes when m is subtracted from the total. -/
theorem progressionVariance_eq_character_mean {q : ℕ} [NeZero q] (x m : ℝ) :
    progressionVariance x m q=(q.totient:ℝ)⁻¹*
      ∑ χ : DirichletCharacter ℂ q,‖psiChar x χ-(if χ=1 then (m:ℂ) else 0)‖^2 := by
  let f (r : ZMod q) : ℂ := (psiAP x q r.val-m/(q.totient:ℝ):ℝ)
  have hφ : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hφ' : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have ht (χ : DirichletCharacter ℂ q) :
      (∑ r : ZMod q,χ r*f r)=psiChar x χ-(if χ=1 then (m:ℂ) else 0) := by
    simp only [f,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_natCast,mul_sub,sum_sub_distrib,
      ←sum_mul,psiChar_residue_transform,sum_zmod_eq]
    by_cases h : χ=1 <;> simp [h] <;> field_simp
  have hd := dirichlet_character_parseval f
  simp only [ht] at hd
  have hh (r : ZMod q) : ‖f r‖^2=(psiAP x q r.val-m/(q.totient:ℝ))^2 := by
    rw [show ‖f r‖=|psiAP x q r.val-m/(q.totient:ℝ)| by exact Complex.norm_real _]
    exact sq_abs _
  simp only [hh] at hd
  rw [hd,←mul_assoc,inv_mul_cancel₀ hφ',one_mul];rfl

/-- Centering at the sum on the units removes exactly the principal coefficient. -/
theorem progressionVariance_eq_nonprincipal {q : ℕ} [NeZero q] (x : ℝ) :
    progressionVariance x (psiChar x (1:DirichletCharacter ℂ q)).re q=(q.totient:ℝ)⁻¹*
      ∑ χ∈(univ : Finset (DirichletCharacter ℂ q)).erase 1,‖psiChar x χ‖^2 := by
  rw [progressionVariance_eq_character_mean]
  congr 1
  have he : ((psiChar x (1:DirichletCharacter ℂ q)).re:ℂ)=psiChar x (1:DirichletCharacter ℂ q) := by
    have he := psiChar_one_eq_psi_sub x q
    let y := Chebyshev.psi x-∑ n∈Icc 1 ⌊x⌋₊ with ¬n.Coprime q,Λ n
    have hy : psiChar x (1:DirichletCharacter ℂ q)=(y:ℂ) := by
      dsimp only [y];push_cast;linear_combination -he
    rw [hy];rfl
  rw [←sum_erase_add _ _ (mem_univ (1:DirichletCharacter ℂ q))]
  simp only [he,ite_true,sub_self,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero,if_pos rfl]
  apply sum_congr rfl;intro χ hχ
  rw [if_neg (mem_erase.mp hχ).1,sub_zero]

end AnalyticNumberTheory.PrimeDistribution
