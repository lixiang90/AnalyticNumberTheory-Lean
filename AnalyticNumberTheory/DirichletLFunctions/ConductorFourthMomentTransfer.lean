import AnalyticNumberTheory.DirichletLFunctions.PrimitiveConductorSums
import AnalyticNumberTheory.DirichletLFunctions.ConductorEulerWeights
import AnalyticNumberTheory.DirichletLFunctions.FunctionalEquation

/-!
# Transferring fourth moments from primitive conductors

A character and its inducing primitive character differ by a finite Euler
product. Summing its fourth power against the totient controls the actual
imprimitive functions as well as the functions at their primitive level.
-/
noncomputable section
open Real Complex Set Finset MeasureTheory
open scoped Classical Interval
namespace AnalyticNumberTheory.DirichletLFunctions

/-- The L-function of the primitive character inducing χ. -/
def inducingLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ→ℂ :=
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  χ.primitiveCharacter.LFunction

theorem inducingLFunction_changeLevel {q d : ℕ} [NeZero q] [NeZero d] (hd : d∣q)
    {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive) :
    inducingLFunction (ψ.changeLevel hd)=ψ.LFunction := by
  let χ := ψ.changeLevel hd
  have hc : χ.conductor=d := conductor_changeLevel_of_isPrimitive hd hψ
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ' : χ.primitiveCharacter.changeLevel (dvd_of_eq hc)=ψ := by
    apply DirichletCharacter.changeLevel_injective hd
    rw [←DirichletCharacter.changeLevel_trans,χ.changeLevel_primitiveCharacter]
  have tr {l m : ℕ} [NeZero l] [NeZero m] (hm : l=m) (α : DirichletCharacter ℂ l) :
      (α.changeLevel (dvd_of_eq hm)).LFunction=α.LFunction := by
    subst m;rw [DirichletCharacter.changeLevel_self]
  change χ.primitiveCharacter.LFunction=ψ.LFunction
  rw [←tr hc χ.primitiveCharacter,hψ']

/-- The cost of passing to a multiple of the primitive conductor on the
half-plane of real part at least a quarter. -/
theorem changeLevel_fourth_le {q d : ℕ} [NeZero q] [NeZero d] (hd : d∣q)
    (ψ : DirichletCharacter ℂ d) {s : ℂ} (hs : 1/4≤s.re) (hs' : s≠1) :
    ‖(ψ.changeLevel hd).LFunction s‖^4≤
      ‖ψ.LFunction s‖^4*∏p∈(q/d).primeFactors,(1+(p:ℝ)^(-(1/4):ℝ))^4 := by
  let S := q.primeFactors.filter (fun p=>¬p∣d)
  let f (p : ℕ) := 1-ψ p*(p:ℂ)^(-s)
  let w (p : ℕ) := (1+(p:ℝ)^(-(1/4):ℝ))^4
  have hh := LFunction_changeLevel_eq hd ψ (Or.inr hs')
  have he : (∏p∈q.primeFactors,f p)=∏p∈S,f p := by
    symm;apply prod_subset (filter_subset _ _);intro p hp hn
    have hpd : p∣d := by simpa only [S,mem_filter,hp,true_and,not_not] using hn
    have hu : ¬IsUnit (p:ZMod d) := by
      rw [ZMod.isUnit_iff_coprime,(Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd];simpa
    simp [f,MulChar.map_nonunit ψ hu]
  have hsub : S⊆(q/d).primeFactors := by
    intro p hp
    obtain ⟨hm,hpd⟩ := mem_filter.mp hp
    obtain ⟨hpr,hpq,_⟩ := Nat.mem_primeFactors.mp hm
    have hdiv : p∣(q/d)*d := by rwa [Nat.div_mul_cancel hd]
    exact Nat.mem_primeFactors.mpr ⟨hpr,(hpr.dvd_mul.mp hdiv).resolve_right hpd,
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd) (NeZero.pos d)).ne'⟩
  have hf (p : ℕ) (hp : p∈S) : ‖f p‖^4≤w p := by
    have hpr := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h := norm_sub_le (1:ℂ) (ψ p*(p:ℂ)^(-s))
    rw [norm_one,norm_mul,Complex.norm_natCast_cpow_of_pos hpr.pos,neg_re] at h
    apply h.trans
    exact add_le_add (le_refl (1:ℝ)) (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (ψ.norm_le_one _) |>.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpr.one_le) (neg_le_neg hs)))
  have hw (p : ℕ) : 1≤w p := one_le_pow₀ (by linarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) p) (-(1/4):ℝ)]) (n:=4)
  rw [hh,norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change ‖∏p∈q.primeFactors,f p‖^4≤∏p∈(q/d).primeFactors,w p
  rw [he,norm_prod,←Finset.prod_pow]
  exact (prod_le_prod₀ (fun p _=>pow_nonneg (norm_nonneg _) _) hf).trans
    (prod_le_prod_of_subset_of_one_le₀ hsub (fun p _=>zero_le_one.trans (hw p)) (fun p _ _=>hw p))

/-- From a primitive moment bound φ(d)B for every conductor dividing q,
deduce qB for the inducing functions and CqB for the actual functions. -/
theorem family_fourth_of_primitive_bounds : ∃ C : ℝ,0<C ∧
    ∀{q : ℕ} [NeZero q] {σ a b B : ℝ},1/4≤σ → σ≠1 → a≤b → 0≤B →
      (∀ d : q.divisors, letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
        (∑ψ : DirichletCharacter ℂ d.val with ψ.IsPrimitive,∫t in a..b,‖ψ.LFunction ((σ:ℂ)+t*I)‖^4)≤d.val.totient*B) →
      ((∑χ : DirichletCharacter ℂ q,∫t in a..b,‖inducingLFunction χ ((σ:ℂ)+t*I)‖^4)≤q*B) ∧
      ((∑χ : DirichletCharacter ℂ q,∫t in a..b,‖χ.LFunction ((σ:ℂ)+t*I)‖^4)≤C*q*B) := by
  obtain ⟨C,hC,H⟩ := conductor_euler_fourth_weight_le
  refine ⟨C,hC,?_⟩
  intro q _ σ a b B hσ hσ' hab hB hmean
  let W (d : ℕ) := ∏p∈(q/d).primeFactors,(1+(p:ℝ)^(-(1/4):ℝ))^4
  let z (t : ℝ) := (σ:ℂ)+t*I
  have hz (t : ℝ) : (z t).re=σ := by simp [z]
  have hz' (t : ℝ) : z t≠1 := by intro he;apply hσ';simpa only [hz,Complex.one_re] using congrArg Complex.re he
  have hW (d : ℕ) : 0≤W d := prod_nonneg (fun p _=>by positivity)
  constructor
  · rw [sum_by_primitive_conductor]
    apply (sum_le_sum (g:=fun d : q.divisors=>(d.val.totient:ℝ)*B) (fun d _=>?_)).trans_eq
    · rw [Finset.sum_attach q.divisors (fun n=>(n.totient:ℝ)*B),←sum_mul];congr 1;exact_mod_cast Nat.sum_totient q
    · letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
      have he (ψ : DirichletCharacter ℂ d.val) (hp : ψ.IsPrimitive) :
          (∫t in a..b,‖inducingLFunction (ψ.changeLevel (Nat.dvd_of_mem_divisors d.property)) (z t)‖^4)=
          ∫t in a..b,‖ψ.LFunction (z t)‖^4 := by rw [inducingLFunction_changeLevel _ hp]
      rw [sum_congr rfl (fun ψ hψ=>he ψ (mem_filter.mp hψ).2)];exact hmean d
  · rw [sum_by_primitive_conductor]
    apply (sum_le_sum (g:=fun d : q.divisors=>(d.val.totient:ℝ)*W d.val*B) (fun d _=>?_)).trans
    · rw [Finset.sum_attach q.divisors (fun n=>(n.totient:ℝ)*W n*B),←sum_mul];exact mul_le_mul_of_nonneg_right (H q) hB
    · letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
      let hd := Nat.dvd_of_mem_divisors d.property
      let S := (univ:Finset (DirichletCharacter ℂ d.val)).filter (fun ψ=>ψ.IsPrimitive)
      have hh (ψ : DirichletCharacter ℂ d.val) : (∫t in a..b,‖(ψ.changeLevel hd).LFunction (z t)‖^4)≤
          (∫t in a..b,‖ψ.LFunction (z t)‖^4)*W d.val := by
        have hc : Continuous (fun t=>ψ.LFunction (z t)) := continuous_iff_continuousAt.mpr fun t=>
          (DirichletCharacter.differentiableAt_LFunction ψ _ (Or.inl (hz' t))).continuousAt.comp (show Continuous z by dsimp [z];fun_prop).continuousAt
        rw [←intervalIntegral.integral_mul_const,intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
        exact integral_mono_of_nonneg (ae_of_all _ (fun t=>by positivity))
          ((hc.norm.pow 4).mul continuous_const |>.integrableOn_Icc |>.mono_set Set.Ioc_subset_Icc_self)
          (ae_of_all _ (fun t=>changeLevel_fourth_le hd ψ (by rw [hz];exact hσ) (hz' t)))
      apply (sum_le_sum (fun ψ (_ : ψ∈S)=>hh ψ)).trans
      rw [←sum_mul]
      exact (mul_le_mul_of_nonneg_right (hmean d) (hW _)).trans_eq (by ring)

end AnalyticNumberTheory.DirichletLFunctions
