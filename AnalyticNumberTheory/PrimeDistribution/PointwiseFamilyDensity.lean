import AnalyticNumberTheory.PrimeDistribution.PointwiseCharacterDensity
import AnalyticNumberTheory.PrimeDistribution.PointwiseZetaDensity
import AnalyticNumberTheory.PrimeDistribution.PrimitiveFamilyIngham
import AnalyticNumberTheory.PrimeDistribution.MontgomeryDensityInputs
import AnalyticNumberTheory.DirichletLFunctions.CriticalConductorBound

/-!
# Density from critical-line growth for both Dirichlet character families

The fixed-modulus and primitive-conductor counts include the principal
character and all analytic multiplicities at both signs of height. Their
conductor-height scales are qT and Q²T respectively.
-/
noncomputable section
open Real Complex Finset
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.RiemannZeta
namespace AnalyticNumberTheory.PrimeDistribution

private theorem criticalCharacterGrowth_to_zeta {a b : ℝ} (h : CriticalCharacterGrowth a b) : CriticalZetaGrowth a b := by
  obtain ⟨B,hB,HB⟩ := h
  exact ⟨B,hB,fun t => by simpa only [DirichletCharacter.LFunction_modOne_eq,Nat.cast_one,one_mul] using HB (1:DirichletCharacter ℂ 1) t⟩

private theorem principal_pointwise {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b) (hg : CriticalCharacterGrowth a b) :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T Z H : ℝ},σ∈Set.Icc (3/4:ℝ) 1 → 2≤T → T≤Z → T≤H →
      (characterDensityCount (1:DirichletCharacter ℂ q) σ T:ℝ)≤C*H^(pointwiseDensityExponent a σ)*(Real.log Z)^(10+2*b) := by
  obtain ⟨D,hD,HD⟩ := pointwise_zeta_density ha hb (criticalCharacterGrowth_to_zeta hg)
  refine ⟨2*D,by positivity,?_⟩
  intro q _ σ T Z H hs hT hTZ hTH
  rw [characterDensityCount_principal_eq_twice (by linarith [hs.1])]
  push_cast
  have he := (pointwiseDensityExponent_mem ha hs).1
  have hlog := Real.log_nonneg (by linarith : 1≤T)
  have hh := (HD hs hT).trans (mul_le_mul (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by linarith) hTH he) hD.le)
    (Real.rpow_le_rpow hlog (Real.log_le_log (by linarith) hTZ) (by linarith : 0≤10+2*b))
    (Real.rpow_nonneg hlog _) (by positivity [show 0≤H by linarith]))
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : 0≤(2:ℝ))).trans_eq (by ring)

private theorem fixed_pointwise_narrow {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b) (hg : CriticalCharacterGrowth a b) :
    ∃ C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (3/4:ℝ) 1 → 2≤T →
    (modulusDensityCount q σ T:ℝ)≤C*((q:ℝ)*T)^(pointwiseDensityExponent a σ)*(Real.log ((q:ℝ)*T))^(10+2*b) := by
  obtain ⟨C,hC,HC,_⟩ := sparse_character_family_mean
  obtain ⟨D,hD,HD⟩ := nonprincipal_pointwise_density ha hb hC hg
  obtain ⟨P,hP,HP⟩ := principal_pointwise ha hb hg
  refine ⟨P+D*(12*30^(10+2*b)),by positivity,?_⟩
  intro q _ σ T hs hT
  let L := ⌊T⌋₊+16
  let X := q*(L+2)
  have hL : 16≤L := by dsimp [L];omega
  have hq := NeZero.pos q
  have hX : 1≤X := Nat.mul_pos hq (by omega)
  have hTL : T<(L:ℝ) := by dsimp [L];push_cast;linarith [Nat.lt_floor_add_one T]
  have hscale : (X:ℝ)=(q:ℝ)*((L:ℝ)+2) := by simp [X]
  have hu := HD (univ : Finset (DirichletCharacter ℂ q)) (fun _ => q) id star (H:=X) (L:=L) (T:=T) (σ:=σ)
    (fun χ => star_star χ) (fun _ _ => mem_univ _) (fun i _ => nonprincipal_star_conjugate i)
    hX (by omega) hTL hs (by
      rw [card_univ,card_dirichletCharacter_eq_totient]
      exact Nat.mul_le_mul (Nat.totient_le _) (Nat.le_add_right L 2))
    (fun _ _ => le_rfl) (by rw [hscale];exact HC q L)
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have ht : T≤(q:ℝ)*T := le_mul_of_one_le_left (by linarith) hq'
  have hfrac : (L:ℝ)+2≤12*T := by dsimp [L];push_cast;linarith [Nat.floor_le (by linarith : 0≤T)]
  have hbound := pointwise_density_scale hb (by exact_mod_cast hX : (1:ℝ)≤X) (by positivity : 0≤(q:ℝ)*T) (hT.trans ht)
    (by rw [hscale];nlinarith only [mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (α:=ℝ) q)])
    (by nlinarith [sq_nonneg ((q:ℝ)*T-1)]) (pointwiseDensityExponent_mem ha hs)
  have hnon := hu.trans ((le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hbound hD.le))
  have hprincipal := HP (q:=q) hs hT ht ht
  have he : modulusDensityCount q σ T=characterDensityCount (1:DirichletCharacter ℂ q) σ T+
      ∑χ : DirichletCharacter ℂ q,∑z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z := by
    unfold modulusDensityCount
    calc _ = ∑χ : DirichletCharacter ℂ q,((if χ=1 then characterDensityCount 1 σ T else 0)+
           ∑z∈nonprincipalDensityFinset χ σ T,characterZeroMultiplicity χ z) :=
             sum_congr rfl (fun χ _ => characterDensityCount_split_principal χ σ T)
         _=_ := by rw [sum_add_distrib];simp
  rw [he];push_cast
  exact (add_le_add hprincipal hnon).trans_eq (by ring)

private theorem primitive_pointwise_narrow {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) (1/4)) (hb : 0≤b) (hg : CriticalCharacterGrowth a b) :
    ∃C : ℝ,0<C ∧ ∀{Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (3/4:ℝ) 1 → 2≤T →
    (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤C*((Q:ℝ)^2*T)^(pointwiseDensityExponent a σ)*(Real.log ((Q:ℝ)*T))^(10+2*b) := by
  obtain ⟨C,hC,HC⟩ := primitive_sparse_mean_attach
  obtain ⟨D,hD,HD⟩ := nonprincipal_pointwise_density ha hb hC hg
  obtain ⟨P,hP,HP⟩ := principal_pointwise ha hb hg
  refine ⟨P+D*(12*30^(10+2*b)),by positivity,?_⟩
  intro Q σ T hQ hs hT
  let L := ⌊T⌋₊+16
  let X := Q^2*(L+2)
  let F := primitiveCharacterFamily Q
  let q (i : F) := i.val.1
  let χ (i : F) := i.val.2
  letI (i : F) : NeZero (q i) := ⟨Nat.ne_of_gt (primitiveCharacterFamily_modulus i.property).1⟩
  let c (i : F) : F := ⟨primitiveStarIndex i.val,primitiveStarIndex_mem i.property⟩
  have hL : 16≤L := by dsimp [L];omega
  have hQ₂ : 1≤Q^2 := Nat.one_le_pow _ _ hQ
  have hQq : Q≤Q^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right Q hQ
  have hX : 1≤X := Nat.mul_pos hQ₂ (by omega)
  have hTL : T<(L:ℝ) := by dsimp [L];push_cast;linarith [Nat.lt_floor_add_one T]
  have hscale : (X:ℝ)=(Q:ℝ)^2*((L:ℝ)+2) := by simp [X]
  have hu := HD F.attach q χ c (H:=X) (L:=L) (σ:=σ) (T:=T)
    (fun i => Subtype.ext (primitiveStarIndex_involutive _)) (fun i _ => mem_attach _ _)
    (fun i _ => nonprincipal_star_conjugate (χ i)) hX (by omega) hTL hs
    (by simpa only [card_attach,F] using Nat.mul_le_mul (card_primitiveFamily_le Q) (Nat.le_add_right L 2))
    (fun i _ => Nat.mul_le_mul_right _ ((primitiveCharacterFamily_modulus i.property).2.trans hQq))
    (by rw [hscale];exact HC Q L hQ)
  have hnon : (primitiveFamilyZeroCount Q σ T:ℝ)≤D*(1+Real.log X)^(10+2*b)*(X:ℝ)^(pointwiseDensityExponent a σ) := by
    simp only [primitiveFamilyZeroCount,Nat.cast_sum]
    exact (sum_attach F _).symm.le.trans hu
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have ht : T≤(Q:ℝ)*T := le_mul_of_one_le_left (by linarith) hqr
  have hqt : T≤(Q:ℝ)^2*T := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hqr)
  have hfrac : (L:ℝ)+2≤12*T := by dsimp [L];push_cast;linarith [Nat.floor_le (by linarith : 0≤T)]
  have hbound := pointwise_density_scale hb (by exact_mod_cast hX : (1:ℝ)≤X) (by positivity : 0≤(Q:ℝ)^2*T) (hT.trans ht)
    (by rw [hscale];nlinarith only [mul_le_mul_of_nonneg_left hfrac (sq_nonneg (Q:ℝ))])
    (by nlinarith only [mul_nonneg (sq_nonneg (Q:ℝ)) (show 0≤T^2-T by nlinarith only [hT,sq_nonneg (T-1)])])
    (pointwiseDensityExponent_mem ha hs)
  have hh := hnon.trans ((le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hbound hD.le))
  have hp := HP (q:=1) hs hT ht hqt
  have he := congrArg (fun n:ℕ => (n:ℝ)) (primitive_density_sum_eq_principal_add hQ σ T)
  push_cast at he
  rw [he]
  exact (add_le_add hp hh).trans_eq (by ring)

private theorem characterGrowth_clipped {a b : ℝ} (hb : 0≤b) (hg : CriticalCharacterGrowth a b) :
    CriticalCharacterGrowth (min a (1/4)) b := by
  rcases le_total a (1/4) with h|h
  · simpa only [min_eq_left h] using hg
  rw [min_eq_right h]
  obtain ⟨A,hA,HA⟩ := norm_LFunction_critical_conductor_quarter
  refine ⟨A,hA,?_⟩
  intro q _ χ t
  have hq : (1:ℝ)≤q := by exact_mod_cast (NeZero.one_le : 1≤q)
  have hP : 1≤(q:ℝ)*(|t|+2) := one_le_mul_of_one_le_of_one_le hq (by linarith [abs_nonneg t])
  have hlog : 1≤1+Real.log ((q:ℝ)*(|t|+2)) := by linarith [Real.log_nonneg hP]
  apply (HA χ t).trans
  apply le_trans _ (le_mul_of_one_le_right (by positivity : 0≤A*((q:ℝ)*(|t|+2))^(1/4:ℝ)) (Real.one_le_rpow hlog hb))
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
    (by linarith : 1+|t|≤|t|+2) (Nat.cast_nonneg (α:=ℝ) q)) (by norm_num)) hA.le

private theorem pointwiseExponent_monotone {a c σ : ℝ} (h : a≤c) (hs : σ∈Set.Icc (3/4:ℝ) 1) :
    pointwiseDensityExponent a σ≤pointwiseDensityExponent c σ := by
  unfold pointwiseDensityExponent
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hs.2)) (by linarith [hs.1])

/-- For the complete character group of one modulus, a hybrid critical-line bound
with conductor exponent a gives density exponent (1+4a)(1−σ)/(2σ−1) uniformly
over 3/4 ≤ σ ≤ 1 and T ≥ 2. The count includes multiplicity and both signs of height. -/
theorem modulusDensityCount_of_critical_growth {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hg : CriticalCharacterGrowth a b) :
    ∃C : ℝ,0<C ∧ ∀{q : ℕ} [NeZero q] {σ T : ℝ},σ∈Set.Icc (3/4:ℝ) 1 → 2≤T →
      (modulusDensityCount q σ T:ℝ)≤C*((q:ℝ)*T)^(pointwiseDensityExponent a σ)*(Real.log ((q:ℝ)*T))^(10+2*b) := by
  obtain ⟨C,hC,H⟩ := fixed_pointwise_narrow (a:=min a (1/4)) ⟨le_min ha (by norm_num),min_le_right ..⟩ hb (characterGrowth_clipped hb hg)
  refine ⟨C,hC,?_⟩;intro q _ σ T hs hT
  have hh : 1≤(q:ℝ)*T := one_le_mul_of_one_le_of_one_le (by exact_mod_cast (NeZero.one_le : 1≤q)) (by linarith)
  exact (H (q:=q) hs hT).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hh (pointwiseExponent_monotone (min_le_left ..) hs)) hC.le) (Real.rpow_nonneg (Real.log_nonneg hh) _))

/-- The analogous pointwise density estimate over all primitive conductors at
most Q. The conductor power uses Q²T and the logarithm uses QT. -/
theorem primitive_conductors_of_critical_growth {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hg : CriticalCharacterGrowth a b) :
    ∃C : ℝ,0<C ∧ ∀{Q : ℕ} {σ T : ℝ},1≤Q → σ∈Set.Icc (3/4:ℝ) 1 → 2≤T →
      (∑q∈Icc 1 Q,(primitiveModulusDensityCount q σ T:ℝ))≤C*((Q:ℝ)^2*T)^(pointwiseDensityExponent a σ)*(Real.log ((Q:ℝ)*T))^(10+2*b) := by
  obtain ⟨C,hC,H⟩ := primitive_pointwise_narrow (a:=min a (1/4)) ⟨le_min ha (by norm_num),min_le_right ..⟩ hb (characterGrowth_clipped hb hg)
  refine ⟨C,hC,?_⟩;intro Q σ T hQ hs hT
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hh := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hqr (n:=2)) (by linarith : 1≤T)
  have hl := one_le_mul_of_one_le_of_one_le hqr (by linarith : 1≤T)
  exact (H hQ hs hT).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hh (pointwiseExponent_monotone (min_le_left ..) hs)) hC.le) (Real.rpow_nonneg (Real.log_nonneg hl) _))

end AnalyticNumberTheory.PrimeDistribution
