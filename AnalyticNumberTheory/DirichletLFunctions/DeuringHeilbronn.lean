import AnalyticNumberTheory.DirichletLFunctions.ZeroPowerFamilies

/-!
# The Deuring–Heilbronn repulsion phenomenon

An exceptional real zero of a real character pushes zeros of distinct
primitive Dirichlet characters to the left. The proof differentiates a
positive four-factor logarithmic derivative and detects a large reciprocal
zero by Fejér's inequality. Its constants are absolute, uniformly in height.
-/

noncomputable section
open Complex Filter Metric Finset Set
open scoped Topology
open AnalyticNumberTheory.AnalyticTools.ComplexAnalysis
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem zetaOne_signed_coeff (k : ℕ) :
    signedTaylorCoeff (logDeriv zetaOne) (5/4) k =
      (4:ℂ)^(k+1) + signedTaylorCoeff (logDeriv riemannZeta) (5/4) k := by
  let c : ℂ := 5/4
  let lin : ℂ → ℂ := fun w => w-1
  have hc : 1<c.re := by norm_num [c]
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const continuous_re
  have hmem : {w : ℂ | 1<w.re} ∈ 𝓝 c := hopen.mem_nhds hc
  have hn {w : ℂ} (hw : 1<w.re) : w≠1 := fun h => by subst w; simp at hw
  have he : zetaOne =ᶠ[𝓝 c] lin*riemannZeta := by
    filter_upwards [hmem] with w hw; exact zetaOne_eq_sub_one_mul (hn hw)
  have he' : logDeriv zetaOne =ᶠ[𝓝 c] fun w => (w-1)⁻¹+logDeriv riemannZeta w := by
    filter_upwards [hmem,logDeriv_congr_nhds he] with w hw hew
    rw [hew,logDeriv_mul (f:=lin) (g:=riemannZeta) w (sub_ne_zero.mpr (hn hw)) (riemannZeta_ne_zero_of_one_le_re hw.le)
      (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta (hn hw))]
    simp [lin,logDeriv_apply,one_div]
  have hζ : AnalyticAt ℂ riemannZeta c :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) c (hn hc)
  have hp : AnalyticAt ℂ (fun w => (w-1)⁻¹) c := (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hn hc))
  rw [signedTaylorCoeff_congr he',signedTaylorCoeff_add (h:=logDeriv riemannZeta) hp (hζ.deriv.div hζ (riemannZeta_ne_zero_of_one_le_re hc.le)),
    signedTaylorCoeff_inv_sub]
  norm_num [c]

theorem real_zero_power_point (t x : ℝ) :
    zeroPowerPoint (5/4+t*I) ⟨(x:ℂ)+t*I,0⟩ = (((1+4*(1-x))⁻¹:ℝ):ℂ) := by
  simp only [zeroPowerPoint,add_sub_add_right_eq_sub,Complex.ofReal_inv]
  push_cast
  rw [div_eq_mul_inv,←mul_inv_rev]
  congr 1
  ring

theorem shifted_mem_ball {x : ℝ} (hx : 7/8 ≤ x) (hx' : x<1) (t : ℝ) :
    ((x:ℂ)+t*I) ∈ closedBall (5/4+t*I) (3/8) := by
  rw [mem_closedBall,dist_eq_norm,add_sub_add_right_eq_sub]
  have h : (x:ℂ)-(5:ℂ)/4 = (((x-5/4):ℝ):ℂ) := by push_cast; rfl
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]; linarith

theorem reciprocal_loss {d : ℝ} (hd : 0≤d) (k : ℕ) :
    1-((1+d)⁻¹)^k ≤ d*k := by
  have h₁ : 0<1+d := by linarith
  have hn := one_add_mul_le_pow (a:=(1+d)⁻¹-1) (by linarith [inv_pos.mpr h₁]) k
  rw [add_sub_cancel] at hn
  have hdiff : 1-(1+d)⁻¹ ≤ d := by
    rw [inv_eq_one_div,sub_le_comm,le_div_iff₀ h₁]
    nlinarith [sq_nonneg d]
  nlinarith [mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg (α:=ℝ) k)]

private theorem detect_four_zeros {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hr : IsReal χ) (t : ℝ) {α β H : ℝ} (hα : 7/8≤α) (hα' : α<1)
    (hβ : 31/32≤β) (hβ' : β<1) (hH : 0≤H)
    (hαz : DirichletCharacter.LFunction χ (α:ℂ)=0)
    (hβz : DirichletCharacter.LFunction ψ (β+t*I)=0)
    {S₀ S₁ S₂ S₃ : Finset ZeroPowerIndex}
    (h₀ : ZeroPowerBounds zetaOne (5/4) H S₀)
    (h₁ : ZeroPowerBounds (DirichletCharacter.LFunction χ) (5/4) H S₁)
    (h₂ : ZeroPowerBounds (DirichletCharacter.LFunction ψ) (5/4+t*I) H S₂)
    (h₃ : ZeroPowerBounds (DirichletCharacter.LFunction (χ*ψ)) (5/4+t*I) H S₃)
    {K : ℕ} (hK : 512*(8*H+1) ≤ K) :
    1 ≤ 64*(1-α)*K*(1+4*(1-β))^K := by
  classical
  let a : ZeroPowerIndex := ⟨α,0⟩
  let b : ZeroPowerIndex := ⟨(β:ℂ)+t*I,0⟩
  have ha : a∈S₁ := h₁.mem_of_zero (by simpa using shifted_mem_ball hα hα' 0) hαz
  have hb : b∈S₂ := h₂.mem_of_zero (shifted_mem_ball (by linarith) hβ' t) hβz
  let z₀ := zeroPowerPoint (5/4)
  let zt := zeroPowerPoint (5/4+t*I)
  let S := (S₀.disjSum (S₁.erase a)).disjSum (S₂.disjSum S₃)
  let z := Sum.elim (Sum.elim z₀ z₀) (Sum.elim zt zt)
  let w : (ZeroPowerIndex ⊕ ZeroPowerIndex) ⊕ (ZeroPowerIndex ⊕ ZeroPowerIndex) := Sum.inr (Sum.inl b)
  have hw : w∈S := by simp [w,S,hb]
  have hc : (S.card:ℝ)≤4*H := by
    have hcard : ((S₁.erase a).card:ℝ)≤S₁.card := by exact_mod_cast Finset.card_le_card (erase_subset a S₁)
    simp only [S,card_disjSum,Nat.cast_add]
    linarith [h₀.card_le,h₁.card_le,h₂.card_le,h₃.card_le]
  have hnorm (i) (hi : i∈S) : ‖z i‖≤1 := by
    rcases i with (i|i)|(i|i)
    · exact h₀.norm_le _ (by simpa [S] using hi)
    · exact h₁.norm_le _ (mem_of_mem_erase (by simpa [S] using hi : i ∈ S₁.erase a))
    · exact h₂.norm_le _ (by simpa [S] using hi)
    · exact h₃.norm_le _ (by simpa [S] using hi)
  have hza : z₀ a=(((1+4*(1-α))⁻¹:ℝ):ℂ) := by simpa [z₀,a] using real_zero_power_point 0 α
  have hzw : ‖z w‖=(1+4*(1-β))⁻¹ := by
    change ‖zeroPowerPoint _ b‖=_
    rw [show zeroPowerPoint (5/4+t*I) b=_ from real_zero_power_point t β,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (by linarith))]
  have hbig : 8/9 ≤ ‖z w‖ := by
    rw [hzw,inv_eq_one_div,le_div_iff₀ (by linarith)]; linarith
  have hp := power_sum_detection S z hnorm hw hbig (H:=4*H) (D:=4*(1-α))
    (by positivity) (by linarith) (K:=K) (by linarith) (fun j _ => by
      have hsum := shifted_four_logDeriv_power_nonpos hr ψ (σ:=5/4) (by norm_num) t j
      norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hsum
      have e₀ := h₀.sum_le j
      rw [zetaOne_signed_coeff,Complex.add_re,show ((4:ℂ)^(j+1)).re=(4:ℝ)^(j+1) by norm_cast] at e₀
      have hadd := add_le_add (add_le_add (add_le_add e₀ (h₁.sum_le j)) (h₂.sum_le j)) (h₃.sum_le j)
      have htotal : (∑ i ∈ S₀,(z₀ i^(j+1)).re) + (∑ i ∈ S₁,(z₀ i^(j+1)).re) +
          (∑ i ∈ S₂,(zt i^(j+1)).re) + (∑ i ∈ S₃,(zt i^(j+1)).re) ≤ 1+4*H*(4/5:ℝ)^j := by
        refine hadd.trans ?_
        have hdiv := div_nonpos_of_nonpos_of_nonneg hsum (by positivity : 0≤(4:ℝ)^(j+1))
        rw [add_div,add_div,add_div] at hdiv
        rw [add_div,div_self (by positivity : (4:ℝ)^(j+1)≠0)]
        linarith
      have herase := Finset.sum_erase_add S₁ (fun i => (z₀ i^(j+1)).re) ha
      rw [hza,←Complex.ofReal_pow,Complex.ofReal_re] at herase
      have hlose := reciprocal_loss (show 0≤4*(1-α) by linarith) (j+1)
      push_cast at hlose
      simp only [S,z,Finset.sum_disjSum,Sum.elim_inl,Sum.elim_inr]
      linarith)
  rw [hzw,inv_inv] at hp
  linarith

/-- Common-modulus Deuring–Heilbronn repulsion. The exceptional real zero α
and the target β+it belong to nonprincipal characters χ and ψ for which χψ
is also nonprincipal. The same absolute C works for all choices. -/
theorem deuring_heilbronn_common_modulus :
    ∃ C : ℝ, 16≤C ∧ ∀ {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q},
      IsReal χ → χ≠1 → ψ≠1 → χ*ψ≠1 → ∀ {α β t : ℝ},
      7/8≤α → 31/32≤β → DirichletCharacter.LFunction χ (α:ℂ)=0 →
      DirichletCharacter.LFunction ψ (β+t*I)=0 →
      let L := Real.log ((q:ℝ)*(|t|+2))
      Real.log (1/(C*(1-α)*L))/(C*L) ≤ 1-β := by
  obtain ⟨B,hB,S₀,h₀⟩ := exists_zetaOne_zero_power_bounds
  let A := 2*B+1056
  let P := 4096*A+1026
  let C := 64*P
  have hA : 0<A := by dsimp [A]; linarith
  have hP : 0<P := by dsimp [P]; linarith
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,by dsimp [C,P,A]; linarith,fun {q} _ {χ ψ} hr hχ hψ hχψ {α β t} hα hβ hαz hβz => ?_⟩
  let L := Real.log ((q:ℝ)*(|t|+2))
  have hq : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hL : 1/2≤L := by
    have hq' : 2≤(q:ℝ)*(|t|+2) := by nlinarith [abs_nonneg t,mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) hq')
  have hLp : 0<L := by linarith
  have hα' : α<1 := lt_of_not_ge (fun hg => LFunction_ne_zero_on_re_one χ (by simpa using hg) (.inl hχ) hαz)
  have hβ' : β<1 := lt_of_not_ge (fun hg => LFunction_ne_zero_on_re_one ψ (by simpa using hg) (.inl hψ) hβz)
  let H := A*L
  have hH : 0≤H := (mul_pos hA hLp).le
  have hB' : B≤H := by dsimp [H,A]; nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hL)]
  have hA' : 1056*L ≤ H := by dsimp [H,A]; nlinarith [mul_nonneg hB.le hLp.le]
  have hlog : Real.log ((q:ℝ)*(|0|+2)) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by rw [abs_zero]; linarith [abs_nonneg t]) (Nat.cast_nonneg _)
  obtain ⟨S₁,h₁⟩ := exists_LFunction_zero_power_bounds hχ 0
  obtain ⟨S₂,h₂⟩ := exists_LFunction_zero_power_bounds hψ t
  obtain ⟨S₃,h₃⟩ := exists_LFunction_zero_power_bounds hχψ t
  have h₁' : ZeroPowerBounds (DirichletCharacter.LFunction χ) (5/4) H S₁ := by
    simpa using h₁.mono ((mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤1056)).trans hA')
  let K := ⌈512*(8*H+1)⌉₊
  have hK : 512*(8*H+1) ≤ K := Nat.le_ceil _
  have hKu : (K:ℝ) ≤ P*L := by
    have h := Nat.ceil_lt_add_one (show 0≤512*(8*H+1) by positivity)
    dsimp [K,P,H] at *
    linarith
  have hd := detect_four_zeros hr t hα hα' hβ hβ' hH hαz hβz (h₀.mono hB') h₁' (h₂.mono hA') (h₃.mono hA') hK
  have hpow : (1+4*(1-β))^K ≤ Real.exp (C*L*(1-β)) := by
    calc
      _ ≤ Real.exp (4*(1-β))^K := by gcongr; linarith [Real.add_one_le_exp (4*(1-β))]
      _ = Real.exp ((K:ℝ)*(4*(1-β))) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hKu) (sub_nonneg.mpr hβ'.le),mul_pos (mul_pos hP hLp) (sub_pos.mpr hβ')]
  have hpref : 64*(1-α)*K ≤ C*(1-α)*L := by dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hKu) (sub_nonneg.mpr hα'.le)]
  have he := hd.trans (mul_le_mul hpref hpow (pow_nonneg (by linarith) _) (by positivity))
  change Real.log (1/(C*(1-α)*L))/(C*L) ≤ 1-β
  rw [div_le_iff₀ (mul_pos hC hLp)]
  apply (Real.log_le_iff_le_exp (by positivity)).2
  rw [div_le_iff₀ (by positivity)]
  rw [mul_comm (1-β) (C*L),mul_comm (Real.exp _)]
  exact he

/-- Deuring–Heilbronn repulsion across distinct nonprincipal primitive characters.
For any real zero α of a real χ and any complex zero ρ of ψ the gain is
log(1/(C (1−α) L))/(C L), capped at 1/32, where L=log(qχ qψ (|Im ρ|+2)).
All constants are absolute. -/
theorem deuring_heilbronn_distinct_primitive :
    ∃ C : ℝ, 0<C ∧ ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
      {χ : DirichletCharacter ℂ q₁} {ψ : DirichletCharacter ℂ q₂},
      χ.IsPrimitive → ψ.IsPrimitive → IsReal χ → χ≠1 → ψ≠1 →
      (⟨q₁,χ⟩ : Σ q : ℕ, DirichletCharacter ℂ q) ≠ ⟨q₂,ψ⟩ →
      ∀ {α : ℝ} {ρ : ℂ}, DirichletCharacter.LFunction χ (α:ℂ)=0 →
        DirichletCharacter.LFunction ψ ρ=0 →
        let L := Real.log ((q₁:ℝ)*q₂*(|ρ.im|+2))
        min (1/32) (Real.log (1/(C*(1-α)*L))/(C*L)) ≤ 1-ρ.re := by
  obtain ⟨C,hC,hrep⟩ := deuring_heilbronn_common_modulus
  refine ⟨C,by linarith,fun {q₁ q₂} _ _ {χ ψ} hpχ hpψ hrχ hχ hψ hne {α ρ} hzα hzρ => ?_⟩
  let L := Real.log ((q₁:ℝ)*q₂*(|ρ.im|+2))
  have hβ' : ρ.re<1 := lt_of_not_ge (fun h => LFunction_ne_zero_on_re_one ψ h (.inl hψ) hzρ)
  by_cases hβ : 31/32 ≤ ρ.re
  · apply le_trans (min_le_right _ _)
    by_cases hα : 7/8≤α
    · let χ' := χ.changeLevel (dvd_mul_right q₁ q₂)
      let ψ' := ψ.changeLevel (dvd_mul_left q₂ q₁)
      obtain ⟨hχ',hψ',hprod⟩ := changeLevel_ne_one_of_distinct_primitive hpχ hpψ hrχ hχ hψ hne
      have h₁ : DirichletCharacter.LFunction χ' (α:ℂ)=0 := by
        rw [LFunction_changeLevel_eq _ χ (.inl hχ),hzα,zero_mul]
      have h₂ : DirichletCharacter.LFunction ψ' ((ρ.re:ℂ)+ρ.im*I)=0 := by
        rw [Complex.re_add_im,LFunction_changeLevel_eq _ ψ (.inl hψ),hzρ,zero_mul]
      simpa only [Nat.cast_mul] using hrep (changeLevel_isReal _ hrχ) hχ' hψ' hprod hα hβ h₁ h₂
    · have hQ : (1:ℝ)≤(q₁:ℝ)*q₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (q₁*q₂))
      have hL : 1/2≤L := by
        have hq : 2≤(q₁:ℝ)*q₂*(|ρ.im|+2) := by
          nlinarith [abs_nonneg ρ.im,mul_nonneg (sub_nonneg.mpr hQ) (abs_nonneg ρ.im)]
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
        norm_num at h; exact h.trans (Real.log_le_log (by norm_num) hq)
      have hgap : 0≤1-α := by linarith
      have hCp : 0≤C := by linarith
      have hLp : 0≤L := by linarith
      have hd : 1≤C*(1-α)*L := by
        calc
          1 = 16*(1/8:ℝ)*(1/2) := by norm_num
          _ ≤ _ := by gcongr <;> first | positivity | linarith
      have hn : Real.log (1/(C*(1-α)*L)) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one (by linarith)).mpr hd)
      exact (div_nonpos_of_nonpos_of_nonneg hn (by positivity)).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

end AnalyticNumberTheory.DirichletLFunctions
