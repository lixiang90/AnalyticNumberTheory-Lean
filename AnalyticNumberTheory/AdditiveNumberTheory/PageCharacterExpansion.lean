import AnalyticNumberTheory.AdditiveNumberTheory.GoldbachMajorArcs
import AnalyticNumberTheory.PrimeDistribution.PageProgressions

/-! # Separating exceptional character sums on a major arc

At a rational frequency, finite character orthogonality expresses the
contribution of the reduced residue classes by Gauss coefficients.
After retaining the principal and one distinguished character, the other
sums are bounded uniformly using their partial sums.
-/

noncomputable section
open Finset AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.PrimeDistribution
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace AnalyticNumberTheory.AdditiveNumberTheory

/-- Fourier coefficient of the rational exponential on reduced residues. -/
def rationalCharacterCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ) : ℂ :=
  (q.totient:ℂ)⁻¹*∑r∈coprimeResidues q, star (χ r)*e ((r:ℝ)*a/q)

theorem rationalCharacterCoefficient_eq_gauss {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ℕ) :
    rationalCharacterCoefficient χ a=gaussSum (star χ) (a:ZMod q)/q.totient := by
  rw [rationalCharacterCoefficient,div_eq_inv_mul,gaussSum_nat_eq_sum_range,coprimeResidues,sum_filter]
  congr 1
  apply sum_congr rfl; intro r _
  by_cases h : r.Coprime q
  · have he : e ((r:ℝ)*a/q) = Complex.exp (2*Real.pi*Complex.I*(a:ℂ)*(r:ℂ)/(q:ℂ)) := by
      rw [e_def]; congr 1; push_cast; ring
    rw [if_pos h,he,MulChar.star_apply',MulChar.star_eq_inv]
  · rw [if_neg h]
    have hu : ¬IsUnit (r:ZMod q) := fun hu => h ((ZMod.isUnit_iff_coprime r q).mp hu)
    rw [MulChar.map_nonunit _ hu,zero_mul]

theorem norm_rationalCharacterCoefficient_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ℕ) : ‖rationalCharacterCoefficient χ a‖≤1 := by
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [rationalCharacterCoefficient,norm_mul,norm_inv,Complex.norm_natCast]
  calc _ ≤ (q.totient:ℝ)⁻¹*(∑ _r∈coprimeResidues q,(1:ℝ)) :=
            mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun r _ => by
              rw [norm_mul,norm_star,norm_e,mul_one]; exact χ.norm_le_one _)) (by positivity)
       _ = 1 := by
         have he : (coprimeResidues q).card=q.totient := by
           simp [coprimeResidues,Nat.totient_eq_card_coprime,Nat.coprime_comm]
         simp [he,hφ.ne']

/-- The conductor, rather than the level, governs the exceptional coefficient. -/
theorem norm_rationalCharacterCoefficient_le_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {a : ℕ} (ha : a.Coprime q) :
    ‖rationalCharacterCoefficient χ a‖≤Real.sqrt χ.conductor/q.totient := by
  rw [rationalCharacterCoefficient_eq_gauss,norm_div,Complex.norm_natCast,norm_gaussSum_star,
    gaussSum_eq_star_mul_of_coprime χ ha,norm_mul,norm_star]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
  rw [norm_gaussSum_one_eq]
  split_ifs <;> simp [Real.sqrt_nonneg]

/-- The discarded nonunit indices have total von Mangoldt mass at most
`log q log x / log 2`. This bound also holds at modulus one. -/
theorem norm_primeExpSum_sub_character_expansion {x : ℝ} (hx : 1≤x)
    {q : ℕ} [NeZero q] (a : ℕ) :
    ‖primeExpSum x ((a:ℝ)/q)-∑χ : DirichletCharacter ℂ q,
      rationalCharacterCoefficient χ a*psiChar x χ‖≤Real.log q/Real.log 2*Real.log x := by
  let E := fun r : ℕ => e ((r:ℝ)*a/q)
  let w := fun r : ℕ => (psiAP x q r:ℂ)*E r
  let R := coprimeResidues q
  have hsplit := sum_filter_add_sum_filter_not (range q) (fun r => r.Coprime q) w
  change ∑r∈R,w r+∑r∈(range q).filter (fun r => ¬r.Coprime q),w r=∑r∈range q,w r at hsplit
  have hmain : (∑r∈R,w r)=∑χ : DirichletCharacter ℂ q,rationalCharacterCoefficient χ a*psiChar x χ := by
    unfold rationalCharacterCoefficient
    calc _ = ∑r∈R, ∑χ : DirichletCharacter ℂ q,
          (q.totient:ℂ)⁻¹*(star (χ r)*E r)*psiChar x χ := by
            refine sum_congr rfl fun r hr => ?_
            dsimp only [w]
            rw [psiAP_eq_inv_totient_mul_sum_psiChar (NeZero.ne q) (mem_filter.mp hr).2,mul_sum,sum_mul]
            apply sum_congr rfl; intro χ _; ring
         _ = _ := by
            rw [sum_comm]
            apply sum_congr rfl; intro χ _
            rw [mul_sum,sum_mul]
  have h := primeExpSum_rat_eq_sum_psiAP x (a:ℤ) (NeZero.pos q)
  push_cast at h
  change primeExpSum x ((a:ℝ)/q)=∑r∈range q,w r at h
  rw [h,←hsplit,←hmain,add_sub_cancel_left]
  apply (norm_sum_le ..).trans
  simpa [w,E,norm_mul,Complex.norm_real,Real.norm_of_nonneg (psiAP_nonneg _ _ _)]
    using sum_psiAP_nonCoprime_le hx (NeZero.pos q)

/-- Partial sum after isolating the principal and a distinguished character. -/
theorem norm_primeExpSum_sub_two_characters {x E : ℝ} (hx : 1≤x) (hE : 0≤E)
    {q : ℕ} [NeZero q] (a : ℕ) (χ₀ : DirichletCharacter ℂ q) (hne : χ₀≠1)
    (hgood : ∀ χ : DirichletCharacter ℂ q,χ≠1 → χ≠χ₀ → ‖psiChar x χ‖≤E) :
    ‖primeExpSum x ((a:ℝ)/q)-rationalCharacterCoefficient (1 : DirichletCharacter ℂ q) a*psiChar x (1 : DirichletCharacter ℂ q)-
      rationalCharacterCoefficient χ₀ a*psiChar x χ₀‖≤Real.log q/Real.log 2*Real.log x+q.totient*E := by
  let F := (univ : Finset (DirichletCharacter ℂ q)).erase 1
  let W := F.erase χ₀
  let f := fun χ : DirichletCharacter ℂ q => rationalCharacterCoefficient χ a*psiChar x χ
  have hχF : χ₀∈F := mem_erase.mpr ⟨hne,mem_univ _⟩
  have he : ∑χ,f χ=f 1+f χ₀+∑χ∈W,f χ := by
    dsimp only [W]
    rw [add_assoc,add_sum_erase F f hχF,add_sum_erase univ f (mem_univ 1)]
  have hcard : W.card≤q.totient := by
    simpa only [Fintype.card_eq_nat_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      using card_le_univ W
  have htail : ‖∑χ∈W,f χ‖≤q.totient*E := calc
    _ ≤ ∑ _χ∈W,E := (norm_sum_le ..).trans (sum_le_sum fun χ hh => by
      obtain ⟨hχ₀,hχ⟩ := mem_erase.mp hh
      exact (norm_mul _ _).le.trans (mul_le_of_le_one_left (norm_nonneg _)
        (norm_rationalCharacterCoefficient_le_one χ a) |>.trans (hgood χ (mem_erase.mp hχ).1 hχ₀)))
    _ = (W.card:ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE
  have H := norm_primeExpSum_sub_character_expansion hx (q:=q) a
  change ‖primeExpSum x ((a:ℝ)/q)-∑χ,f χ‖≤_ at H
  change ‖primeExpSum x ((a:ℝ)/q)-f 1-f χ₀‖≤_
  rw [show primeExpSum x ((a:ℝ)/q)-f 1-f χ₀ =
    (primeExpSum x ((a:ℝ)/q)-∑χ,f χ)+∑χ∈W,f χ by rw [he]; ring]
  exact (norm_add_le ..).trans (add_le_add H htail)

/-- An inducing pair recovers its unique representative at every multiple of
its conductor. -/
theorem eq_changeLevel_of_inducingPair_eq {q d : ℕ} (hdq : d∣q)
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ d}
    (he : (⟨χ.conductor,χ.primitiveCharacter⟩ : Σ m : ℕ,DirichletCharacter ℂ m)=⟨d,ψ⟩) :
    χ=ψ.changeLevel hdq := by
  let recover := fun z : Σ m : ℕ,DirichletCharacter ℂ m =>
    if h : z.1∣q then z.2.changeLevel h else 1
  have h := congrArg recover he
  simpa only [recover,dif_pos χ.conductor_dvd_level,dif_pos hdq,χ.changeLevel_primitiveCharacter] using h

/-- The shifted von Mangoldt sum with a multiplicative character. -/
def characterPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (β : ℝ) : ℂ :=
  expSum (fun n => χ n*(Λ n:ℂ)) (Icc 1 N) β

theorem continuous_characterPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Continuous (characterPrimeSum χ N) := continuous_expSum _ _

/-- On a multiple of a primitive conductor, keep the principal and inducing
characters in the approximation and sum by parts only for the others. -/
theorem norm_page_shift_sub_two_characters {K E : ℝ} {N q d : ℕ} [NeZero q]
    (hN : 1≤N) (hqK : (q:ℝ)≤K) (hdq : d∣q) {ψ : DirichletCharacter ℂ d}
    (hψ : ψ≠1) (hdata : PagePartialBound N K E ⟨d,ψ⟩) (hE : 0≤E) (a : ℕ) (β : ℝ) :
    let χ := ψ.changeLevel hdq
    let χ₁ := (1 : DirichletCharacter ℂ q)
    ‖primeExpSum N ((a:ℝ)/q+β)-rationalCharacterCoefficient χ₁ a*characterPrimeSum χ₁ N β-
      rationalCharacterCoefficient χ a*characterPrimeSum χ N β‖≤
    (Real.log q/Real.log 2*Real.log N+q.totient*E)*(1+2*Real.pi*N*|β|) := by
  intro χ χ₁
  have hn : χ≠1 := fun h => hψ ((DirichletCharacter.changeLevel_eq_one_iff hdq).mp h)
  let b := fun n : ℕ => (Λ n:ℂ)*e (((a:ℝ)/q)*n)-
    rationalCharacterCoefficient χ₁ a*(χ₁ n*(Λ n:ℂ))-
    rationalCharacterCoefficient χ a*(χ n*(Λ n:ℂ))
  let D := Real.log q/Real.log 2*Real.log N+q.totient*E
  have hfac : 0≤Real.log q/Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast NeZero.pos q)) (by positivity)
  have hD : 0≤D := add_nonneg (mul_nonneg hfac (Real.log_nonneg (by exact_mod_cast hN))) (by positivity)
  have hpartial (k : ℕ) (hk : k∈Icc 1 N) : ‖∑n∈Icc 1 k,b n‖≤D := by
    have hk1 : (1:ℝ)≤k := by exact_mod_cast (mem_Icc.mp hk).1
    have hg (ξ : DirichletCharacter ℂ q) (hξ : ξ≠1) (hne : ξ≠χ) : ‖psiChar k ξ‖≤E :=
      hdata hqK (fun hh => hne (eq_changeLevel_of_inducingPair_eq hdq hh)) hξ k hk
    have H := norm_primeExpSum_sub_two_characters hk1 hE a χ hn hg
    simp only [b,sum_sub_distrib,←mul_sum]
    simp only [primeExpSum,expSum,psiChar,Nat.floor_natCast] at H
    apply H.trans
    exact add_le_add (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith)
      (by exact_mod_cast (mem_Icc.mp hk).2)) hfac) le_rfl
  have heq : primeExpSum N ((a:ℝ)/q+β)-rationalCharacterCoefficient χ₁ a*characterPrimeSum χ₁ N β-
      rationalCharacterCoefficient χ a*characterPrimeSum χ N β=expSum b (Icc 1 N) β := by
    simp only [primeExpSum,characterPrimeSum,expSum,Nat.floor_natCast,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl; intro n _
    simp only [b,add_mul,e_add]
    ring
  rw [heq]
  exact norm_expSum_le_of_partial_sums b β hD hpartial

end AnalyticNumberTheory.AdditiveNumberTheory
