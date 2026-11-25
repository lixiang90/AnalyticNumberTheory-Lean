import AnalyticNumberTheory.DirichletLFunctions.BalancedCharacterMoments
import AnalyticNumberTheory.AnalyticTools.DyadicIntegralMajorants
import AnalyticNumberTheory.RiemannZeta.FourthMomentNarrowStrip

/-!
# Fourth moment over primitive characters of one modulus

The bound on the symmetric critical-line height interval is uniform in
the modulus, retaining Euler's totient and exactly four logarithms.
-/
noncomputable section
open Real Complex Finset Set MeasureTheory
open scoped Interval Classical
open AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem primitive_fourth_conductor_blocks :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q],2≤q → ∀{a b U : ℝ},a≤b → 1≤U → b-a≤U →
      (∀t∈Set.Icc a b,U≤1+|t| ∧ 1+|t|≤4*U) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫t in a..b,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤
        C*q.totient*U*(1+Real.log (q*U))^4 := by
  obtain ⟨C,hC,H⟩ := primitive_fourth_on_balanced_interval
  refine ⟨4^4*C,by positivity,?_⟩
  intro q _ hq a b U hab hU hlen hwin
  let x := Real.sqrt ((q:ℝ)*U)
  let N := ⌈x⌉₊
  have hq₁ : 1≤(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hp : 1≤(q:ℝ)*U := one_le_mul_of_one_le_of_one_le hq₁ hU
  have hx : 1≤x := Real.one_le_sqrt.mpr hp
  have hs : x^2=(q:ℝ)*U := Real.sq_sqrt (by linarith)
  have hN : 1≤N := Nat.one_le_ceil_iff.mpr (by linarith)
  have hn : x≤(N:ℝ) := Nat.le_ceil _
  have hn' : (N:ℝ)≤2*x := (Nat.ceil_lt_add_one (by linarith : 0≤x)).le.trans (by linarith)
  have hNs : (N:ℝ)^2≤4*q*U := by nlinarith only [pow_le_pow_left₀ (Nat.cast_nonneg _) hn' 2,hs]
  have hcomp (t : ℝ) (ht : t∈Set.Icc a b) : (N:ℝ)≤2*conductorLength q t ∧ conductorLength q t≤2*N := by
    have h₁ : x≤conductorLength q t := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hwin t ht).1 (Nat.cast_nonneg _))
    have h₂ : (conductorLength q t)^2≤4*x^2 := by
      rw [conductorLength,Real.sq_sqrt (by positivity),hs]
      nlinarith only [mul_le_mul_of_nonneg_left (hwin t ht).2 (Nat.cast_nonneg (α:=ℝ) q)]
    refine ⟨by linarith,?_⟩
    have h₃ : conductorLength q t≤2*x := by nlinarith only [h₂,Real.sqrt_nonneg ((q:ℝ)*U),sq_nonneg (conductorLength q t-2*x)]
    linarith
  apply (H hq hN hab hU hlen hNs hcomp).trans
  have hl : 0≤Real.log ((q:ℝ)*U) := Real.log_nonneg hp
  have hL : 0≤1+Real.log (N^2:ℕ) := by positivity [Real.log_nonneg (show (1:ℝ)≤(N^2:ℕ) by exact_mod_cast Nat.one_le_pow 2 N hN)]
  have hlog : 1+Real.log (N^2:ℕ)≤4*(1+Real.log ((q:ℝ)*U)) := by
    have hl' := Real.log_le_log (by positivity : 0<(N:ℝ)^2) hNs
    rw [show (4:ℝ)*q*U=4*(q*U) by ring,Real.log_mul (by norm_num) (by linarith : (q:ℝ)*U≠0)] at hl'
    push_cast
    linarith only [hl',Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4),hl]
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hlog 4) (by positivity : 0≤C*(q.totient:ℝ)*U)).trans_eq;ring

/-- Symmetric height integral, uniform for every positive modulus and
every T at least one, including the zeta function of modulus one. -/
theorem primitive_family_critical_fourth_moment :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {T : ℝ},1≤T →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫t in (-T)..T,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤
        C*q.totient*T*(1+Real.log (q*T))^4 := by
  classical
  obtain ⟨C,hC,H⟩ := primitive_fourth_conductor_blocks
  obtain ⟨D,hD,HD⟩ := RiemannZeta.fourthMoment_riemannZeta_symmetric_log_le
  refine ⟨4*C+D,by positivity,?_⟩
  intro q _ T hT
  have hq₀ := NeZero.pos q
  by_cases hq : q=1
  · subst q
    have he : ∀χ : DirichletCharacter ℂ 1,χ.IsPrimitive := fun χ=>(DirichletCharacter.level_one χ) ▸ DirichletCharacter.isPrimitive_one_level_one
    have hall : (Finset.univ : Finset (DirichletCharacter ℂ 1)).filter (fun χ=>χ.IsPrimitive) = (Finset.univ : Finset (DirichletCharacter ℂ 1)) := by
      ext χ;constructor
      · intro _;exact Finset.mem_univ _
      · intro h;exact Finset.mem_filter.mpr ⟨h,he χ⟩
    rw [hall]
    simp only [DirichletCharacter.LFunction_modOne_eq,Finset.sum_const,card_univ,Fintype.card_unique,
      one_nsmul,Nat.totient_one,Nat.cast_one,mul_one,one_mul]
    apply (HD hT).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : D≤4*C+D) (by linarith : 0≤T))
      (by positivity)
  have hq' : 2≤q := by omega
  let S := (univ:Finset (DirichletCharacter ℂ q)).filter (fun χ=>χ.IsPrimitive)
  let f (χ : DirichletCharacter ℂ q) (t : ℝ) := ‖χ.LFunction ((1/2:ℂ)+t*I)‖^4
  let F (t : ℝ) := ∑χ∈S,(f χ t+f χ (-t))
  have cf (χ : DirichletCharacter ℂ q) (hχ : χ∈S) : Continuous (f χ) :=
    (((differentiable_LFunction_of_ne_one (isPrimitive_ne_one (mem_filter.mp hχ).2 hq')).continuous.comp (by fun_prop)).norm.pow 4)
  have cF : Continuous F := continuous_finsetSum _ (fun χ hχ=>(cf χ hχ).add ((cf χ hχ).comp continuous_neg))
  have f₀ (t : ℝ) : 0≤F t := Finset.sum_nonneg (fun χ _=>add_nonneg (by dsimp [f];positivity) (by dsimp [f];positivity))
  let w (u : ℝ) := 2*C*q.totient*(1+Real.log (q*u))^4
  have hmono : MonotoneOn w (Ici 1) := by
    intro u hu v hv huv
    have hprod : 1≤(q:ℝ)*u := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq₀) hu
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Real.log_nonneg hprod])
      (add_le_add_right (Real.log_le_log (by linarith : 0<(q:ℝ)*u) (mul_le_mul_of_nonneg_left huv (Nat.cast_nonneg _))) 1) 4) (by positivity)
  have he (a b : ℝ) : (∫t in a..b,F t)=
      (∑χ∈S,∫t in a..b,f χ t)+(∑χ∈S,∫t in (-b)..(-a),f χ t) := by
    simp only [F];rw [intervalIntegral.integral_finsetSum (s:=S) (f:=fun χ t=>f χ t+f χ (-t)) (fun χ hχ=>((cf χ hχ).add ((cf χ hχ).comp continuous_neg)).intervalIntegrable ..),←sum_add_distrib]
    apply sum_congr rfl;intro χ hχ
    have hnegχ : Continuous (fun t : ℝ=>f χ (-t)) := (cf χ hχ).comp continuous_neg
    rw [intervalIntegral.integral_add ((cf χ hχ).intervalIntegrable ..) (hnegχ.intervalIntegrable ..),
      intervalIntegral.integral_comp_neg]
  have hblocks (a b U : ℝ) (hab : a≤b) (hU : 1≤U) (hlen : b-a≤U)
      (hwin : ∀t∈Set.Icc a b,U≤1+|t| ∧ 1+|t|≤4*U) : (∫t in a..b,F t)≤U*w U := by
    rw [he]
    have hneg (t : ℝ) (ht : t∈Set.Icc (-b) (-a)) : U≤1+|t| ∧ 1+|t|≤4*U := by
      simpa only [abs_neg] using hwin (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    exact (add_le_add (H hq' hab hU hlen hwin) (H hq' (by linarith) hU (by linarith) hneg)).trans_eq (by dsimp [w];ring)
  have hu : (∫t in (0:ℝ)..1,F t)≤w 1 := by
    simpa only [one_mul] using hblocks 0 1 1 (by norm_num) (by norm_num) (by norm_num)
      (fun t ht=>by rw [abs_of_nonneg ht.1];constructor <;>linarith [ht.1,ht.2])
  have hd (u : ℝ) (hu : 1≤u) : (∫t in u..(2*u),F t)≤u*w u :=
    hblocks u (2*u) u (by linarith) hu (by linarith)
      (fun t ht=>by rw [abs_of_nonneg (by linarith [ht.1])];constructor <;>linarith [ht.1,ht.2])
  have hh := integral_zero_to_of_weighted_dyadic cF f₀ hmono (fun u _=>by dsimp [w];positivity) hu hd hT
  have heq : (∫t in (0:ℝ)..T,F t)=∑χ∈S,∫t in (-T)..T,f χ t := by
    rw [he,neg_zero,add_comm,←sum_add_distrib];apply sum_congr rfl;intro χ hχ
    exact intervalIntegral.integral_add_adjacent_intervals ((cf χ hχ).intervalIntegrable ..) ((cf χ hχ).intervalIntegrable ..)
  rw [heq] at hh
  apply hh.trans
  dsimp only [w]
  nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hD.le (Nat.cast_nonneg (α:=ℝ) q.totient)) (by linarith : 0≤T)) (pow_nonneg (by positivity [Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq₀ : (1:ℝ)≤q) hT)] : 0≤1+Real.log (q*T)) 4)]

end AnalyticNumberTheory.DirichletLFunctions
