import AnalyticNumberTheory.DirichletLFunctions.ExceptionalCharacterPowers

/-!
# Repulsion for ζ and for the exceptional character itself

The real exceptional zero of a nonprincipal real character repels the zeros
of ζ and every other zero of the same L-function. The absolute constants
apply even when the height of the target approaches zero.
-/
noncomputable section
open Complex Filter Set Finset Metric
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem signed_zetaOne_scaled (t : ℝ) (k : ℕ) :
    (signedTaylorCoeff (logDeriv zetaOne) (5/4+t*I) k).re/(4:ℝ)^(k+1) =
      (zeroPowerPoint (5/4+t*I) ⟨1,0⟩^(k+1)).re +
      (signedTaylorCoeff (logDeriv riemannZeta) (5/4+t*I) k).re/(4:ℝ)^(k+1) := by
  rw [zetaOne_shifted_signed_coeff,Complex.add_re,add_div]
  congr 1
  simp only [zeroPowerPoint,div_pow]
  rw [show (4:ℂ)^(k+1)=((4:ℝ)^(k+1):ℝ) by push_cast; rfl,Complex.div_ofReal_re]

private theorem detect_exceptional_character_zeros {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hr : IsReal χ) {α : ℝ} {ρ : ℂ} (hα : 31/32≤α) (hα' : α<1)
    (hβ : 31/32≤ρ.re) (hβ' : ρ.re<1) {H : ℝ} (hH : 0≤H)
    (hαz : DirichletCharacter.LFunction χ (α:ℂ)=0)
    (hρ : riemannZeta ρ=0 ∨ (DirichletCharacter.LFunction χ ρ=0 ∧ ρ≠(α:ℂ)))
    {S₀ S₁ S₂ S₃ : Finset ZeroPowerIndex}
    (h₀ : ZeroPowerBounds zetaOne (5/4) H S₀)
    (h₁ : ZeroPowerBounds (DirichletCharacter.LFunction χ) (5/4) H S₁)
    (h₂ : ZeroPowerBounds zetaOne (5/4+ρ.im*I) H S₂)
    (h₃ : ZeroPowerBounds (DirichletCharacter.LFunction χ) (5/4+ρ.im*I) H S₃)
    {K : ℕ} (hK : 512*(8*H+2) ≤ K) :
    1 ≤ 128*(1-α)*K*(1+4*(1-ρ.re))^K := by
  classical
  let a : ZeroPowerIndex := ⟨α,0⟩
  let b : ZeroPowerIndex := ⟨ρ,0⟩
  let c : ℂ := 5/4+ρ.im*I
  let z₀ := zeroPowerPoint (5/4)
  let zt := zeroPowerPoint c
  have ha : a∈S₁ := h₁.mem_of_zero (by simpa using shifted_mem_ball (by linarith : 7/8≤α) hα' 0) hαz
  have hball : ρ∈closedBall c (3/8) := by simpa [c,Complex.re_add_im] using shifted_mem_ball (by linarith : 7/8≤ρ.re) hβ' ρ.im
  have hza : z₀ a=(((1+4*(1-α))⁻¹:ℝ):ℂ) := by simpa [z₀,a] using real_zero_power_point 0 α
  let R := if |ρ.im|≤3/16 then S₃.erase a else S₃
  have hR : R⊆S₃ := by
    dsimp only [R]
    split
    · exact Finset.erase_subset _ _
    · exact fun _ hi => hi
  let S := (S₀.disjSum (S₁.erase a)).disjSum (S₂.disjSum R)
  let z := Sum.elim (Sum.elim z₀ z₀) (Sum.elim zt zt)
  have hc : (S.card:ℝ)≤4*H := by
    have her : ((S₁.erase a).card:ℝ)≤S₁.card := by exact_mod_cast Finset.card_le_card (erase_subset a S₁)
    have hr' : (R.card:ℝ)≤S₃.card := by exact_mod_cast Finset.card_le_card hR
    simp only [S,card_disjSum,Nat.cast_add]
    linarith [h₀.card_le,h₁.card_le,h₂.card_le,h₃.card_le]
  have hnorm (i) (hi : i∈S) : ‖z i‖≤1 := by
    rcases i with (i|i)|(i|i)
    · exact h₀.norm_le _ (by simpa [S] using hi)
    · exact h₁.norm_le _ (mem_of_mem_erase (by simpa [S] using hi : i ∈ S₁.erase a))
    · exact h₂.norm_le _ (by simpa [S] using hi)
    · exact h₃.norm_le _ (hR (by simpa [S] using hi))
  have hex : ∃ w∈S, z w=zt b := by
    rcases hρ with hζ | ⟨hχ,hne⟩
    · have hz : zetaOne ρ=0 := by
        rw [zetaOne_eq_sub_one_mul (by intro he; rw [he] at hβ'; norm_num at hβ'),hζ,mul_zero]
      exact ⟨Sum.inr (Sum.inl b),by simpa [S] using h₂.mem_of_zero hball hz,rfl⟩
    · have hb := h₃.mem_of_zero hball hχ
      have hne' : b≠a := fun he => hne (congrArg Sigma.fst he)
      refine ⟨Sum.inr (Sum.inr b),?_,rfl⟩
      simp only [S,inr_mem_disjSum]
      dsimp only [R]; split <;> simp [b,hne',hb,mem_erase,a,hne]
  obtain ⟨w,hw,hzw⟩ := hex
  have hnormw : ‖z w‖=(1+4*(1-ρ.re))⁻¹ := by
    have hv := real_zero_power_point ρ.im ρ.re
    rw [Complex.re_add_im] at hv
    rw [hzw,show zt b=_ from hv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (by linarith))]
  have hbig : 8/9≤‖z w‖ := by rw [hnormw,inv_eq_one_div,le_div_iff₀ (by linarith)]; linarith
  have hp := power_sum_detection S z hnorm hw hbig (H:=4*H+1) (D:=8*(1-α))
    (by positivity) (by linarith) (K:=K) (by linarith) (fun j _ => by
      let p := zeroPowerPoint c (⟨1,0⟩:ZeroPowerIndex)
      have hZ₀ := signed_zetaOne_scaled 0 j
      simp only [Complex.ofReal_zero,zero_mul,add_zero] at hZ₀
      have hone : zeroPowerPoint (5/4) ⟨1,0⟩=1 := by norm_num [zeroPowerPoint]
      rw [hone,one_pow,Complex.one_re] at hZ₀
      have hZ₂ := signed_zetaOne_scaled ρ.im j
      have e₀ := h₀.sum_le j
      have e₂ := h₂.sum_le j
      rw [hZ₀] at e₀
      rw [hZ₂] at e₂
      have hsum := self_shifted_four_logDeriv_power_nonpos hr (σ:=5/4) (by norm_num) ρ.im j
      norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hsum
      have hadd := add_le_add (add_le_add (add_le_add e₀ (h₁.sum_le j)) e₂) (h₃.sum_le j)
      have htotal : (∑ i ∈ S₀,(z₀ i^(j+1)).re) + (∑ i ∈ S₁,(z₀ i^(j+1)).re) +
          (∑ i ∈ S₂,(zt i^(j+1)).re) + (∑ i ∈ S₃,(zt i^(j+1)).re) ≤ 1+(p^(j+1)).re+4*H*(4/5:ℝ)^j := by
        refine hadd.trans ?_
        have hdiv := div_nonpos_of_nonpos_of_nonneg hsum (by positivity : 0≤(4:ℝ)^(j+1))
        rw [add_div,add_div,add_div] at hdiv
        dsimp only [p,c]; linarith
      have he := Finset.sum_erase_add S₁ (fun i => (z₀ i^(j+1)).re) ha
      rw [hza,←Complex.ofReal_pow,Complex.ofReal_re] at he
      have hlose := reciprocal_loss (show 0≤4*(1-α) by linarith) (j+1)
      push_cast at hlose
      have hRsum : (∑ i ∈ R,(zt i^(j+1)).re)+(p^(j+1)).re ≤
          (∑ i ∈ S₃,(zt i^(j+1)).re) + 4*(1-α)*(j+1)+(4/5:ℝ)^j := by
        by_cases ht : |ρ.im|≤3/16
        · have has := h₃.mem_of_zero (exceptional_zero_mem_shifted_ball hα hα' ht) hαz
          have hse := Finset.sum_erase_add S₃ (fun i => (zt i^(j+1)).re) has
          have hdiff := shifted_pole_minus_zero_power_le ρ.im α hα'.le (j+1)
          change (p^(j+1)).re-(zt a^(j+1)).re ≤ _ at hdiff
          push_cast at hdiff
          rw [show R=S₃.erase a by simp [R,ht]]
          linarith [show 0≤(4/5:ℝ)^j by positivity]
        · have hn : ‖p‖≤4/5 := shifted_pole_norm_le_of_height (le_of_not_ge ht)
          have hv : (p^(j+1)).re≤(4/5:ℝ)^j := by
            calc
              _ ≤ ‖p^(j+1)‖ := Complex.re_le_norm _
              _ ≤ (4/5:ℝ)^(j+1) := by rw [norm_pow]; gcongr
              _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          rw [show R=S₃ by simp [R,ht]]
          nlinarith [mul_nonneg (sub_nonneg.mpr hα'.le) (Nat.cast_nonneg (α:=ℝ) j)]
      simp only [S,z,Finset.sum_disjSum,Sum.elim_inl,Sum.elim_inr]
      nlinarith only [hRsum,he,htotal,hlose])
  rw [hnormw,inv_inv] at hp
  linarith

/-- Deuring–Heilbronn repulsion for ζ and for the exceptional character itself.
For a real zero α of a nonprincipal real character χ, every zero ρ of ζ and
every zero ρ≠α of L(s,χ) obey this estimate uniformly in q and in height. -/
theorem deuring_heilbronn_exceptional_character_and_zeta :
    ∃ C : ℝ, 0<C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}, IsReal χ → χ≠1 →
      ∀ {α : ℝ} {ρ : ℂ}, DirichletCharacter.LFunction χ (α:ℂ)=0 →
      (riemannZeta ρ=0 ∨ (DirichletCharacter.LFunction χ ρ=0 ∧ ρ≠(α:ℂ))) →
      let L := Real.log ((q:ℝ)*(|ρ.im|+2))
      min (1/32) (Real.log (1/(C*(1-α)*L))/(C*L)) ≤ 1-ρ.re := by
  obtain ⟨B,hB,hs⟩ := exists_shifted_zetaOne_zero_power_bounds
  let A := B+1056
  let P := 4096*A+2050
  let C := 128*P
  have hA : 0<A := by dsimp [A]; linarith
  have hP : 0<P := by dsimp [P]; linarith
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun {q} _ {χ} hr hχ {α ρ} hzα hzρ => ?_⟩
  let L := Real.log ((q:ℝ)*(|ρ.im|+2))
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hQ : 2≤(q:ℝ)*(|ρ.im|+2) := by nlinarith [abs_nonneg ρ.im,mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg ρ.im)]
  have hL : 1/2≤L := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h; exact h.trans (Real.log_le_log (by norm_num) hQ)
  have hLp : 0<L := by linarith
  have hα' : α<1 := lt_of_not_ge (fun hh => LFunction_ne_zero_on_re_one χ (by simpa using hh) (.inl hχ) hzα)
  have hβ' : ρ.re<1 := lt_of_not_ge (fun hh => hzρ.elim (riemannZeta_ne_zero_of_one_le_re hh)
    (fun h => LFunction_ne_zero_on_re_one χ hh (.inl hχ) h.1))
  by_cases hβ : 31/32≤ρ.re
  · apply le_trans (min_le_right _ _)
    by_cases hα : 31/32≤α
    · let H := A*L
      have hH : 0≤H := (mul_pos hA hLp).le
      have h₁₀ : Real.log ((q:ℝ)*(|0|+2))≤L := by
        apply Real.log_le_log (by positivity)
        exact mul_le_mul_of_nonneg_left (by rw [abs_zero]; linarith [abs_nonneg ρ.im]) (Nat.cast_nonneg _)
      have h₀t : Real.log (|ρ.im|+2)≤L := by
        apply Real.log_le_log (by positivity)
        exact le_mul_of_one_le_left (by positivity) hq
      have h₀₀ : Real.log (|0|+2)≤L := (Real.log_le_log (by positivity) (by rw [abs_zero]; linarith [abs_nonneg ρ.im] : |(0:ℝ)|+2≤|ρ.im|+2)).trans h₀t
      have hB' : B*L ≤ H := by dsimp [H,A]; nlinarith
      have hA' : 1056*L ≤ H := by dsimp [H,A]; nlinarith [mul_nonneg hB.le hLp.le]
      obtain ⟨S₀,h₀⟩ := hs 0
      obtain ⟨S₁,h₁⟩ := exists_LFunction_zero_power_bounds hχ 0
      obtain ⟨S₂,h₂⟩ := hs ρ.im
      obtain ⟨S₃,h₃⟩ := exists_LFunction_zero_power_bounds hχ ρ.im
      have h₀' : ZeroPowerBounds zetaOne (5/4) H S₀ := by
        simpa using h₀.mono ((mul_le_mul_of_nonneg_left h₀₀ hB.le).trans hB')
      have h₁' : ZeroPowerBounds (DirichletCharacter.LFunction χ) (5/4) H S₁ := by
        simpa using h₁.mono ((mul_le_mul_of_nonneg_left h₁₀ (by norm_num : (0:ℝ)≤1056)).trans hA')
      let K := ⌈512*(8*H+2)⌉₊
      have hK : 512*(8*H+2)≤K := Nat.le_ceil _
      have hKu : (K:ℝ)≤P*L := by
        have h := Nat.ceil_lt_add_one (show 0≤512*(8*H+2) by positivity)
        dsimp [K,P,H] at *; linarith
      have hd := detect_exceptional_character_zeros hr hα hα' hβ hβ' hH hzα hzρ h₀' h₁'
        (h₂.mono ((mul_le_mul_of_nonneg_left h₀t hB.le).trans hB')) (h₃.mono hA') hK
      have hpow : (1+4*(1-ρ.re))^K ≤ Real.exp (C*L*(1-ρ.re)) := by
        calc
          _ ≤ Real.exp (4*(1-ρ.re))^K := by gcongr; linarith [Real.add_one_le_exp (4*(1-ρ.re))]
          _ = Real.exp ((K:ℝ)*(4*(1-ρ.re))) := (Real.exp_nat_mul _ _).symm
          _ ≤ _ := by apply Real.exp_le_exp.mpr; dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hKu) (sub_nonneg.mpr hβ'.le),mul_pos (mul_pos hP hLp) (sub_pos.mpr hβ')]
      have hp : 128*(1-α)*K ≤ C*(1-α)*L := by dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hKu) (sub_nonneg.mpr hα'.le)]
      have he := hd.trans (mul_le_mul hp hpow (pow_nonneg (by linarith) _) (by positivity))
      change Real.log (1/(C*(1-α)*L))/(C*L) ≤ 1-ρ.re
      rw [div_le_iff₀ (mul_pos hC hLp)]
      apply (Real.log_le_iff_le_exp (by positivity)).2
      rw [div_le_iff₀ (by positivity),mul_comm (1-ρ.re) (C*L),mul_comm (Real.exp _)]
      exact he
    · have h64 : 64≤C := by dsimp [C,P,A]; linarith
      have hd : 1≤C*(1-α)*L := by
        calc
          1=64*(1/32:ℝ)*(1/2) := by norm_num
          _ ≤ _ := by gcongr <;> first | positivity | linarith
      have hn : Real.log (1/(C*(1-α)*L)) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one (by linarith)).mpr hd)
      exact (div_nonpos_of_nonpos_of_nonneg hn (by positivity)).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

end AnalyticNumberTheory.DirichletLFunctions
