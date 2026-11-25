import AnalyticNumberTheory.DirichletLFunctions.PrimitiveGaussianFourthReduction
import AnalyticNumberTheory.DirichletLFunctions.CharacterPolynomialFourthMeans
import AnalyticNumberTheory.AnalyticTools.FourthMomentConvolution

/-!
# Fourth moments at a balanced conductor length

On a height interval where the square root of the conductor stays comparable
to a single integer cutoff, the central polynomial and both Gaussian shifts
give a fourth power of the logarithm with a factor φ(q).
-/
noncomputable section
open Real Complex Set Finset MeasureTheory
open scoped Interval Classical
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.DirichletLFunctions

private theorem inverse_quarter_four {n : ℝ} (h : 0<n) : (n^(-(1/4):ℝ))^4=n⁻¹ := by
  rw [←Real.rpow_natCast _ 4,←Real.rpow_mul h.le];norm_num [Real.rpow_neg_one]

/-- A bound uniform in the location of the interval and the modulus; the
cutoff has to stay within a factor of two of the conductor length there. -/
theorem primitive_fourth_on_balanced_interval :
    ∃ C : ℝ,0<C ∧ ∀ {q N : ℕ} [NeZero q],2≤q → 1≤N → ∀{a b U : ℝ},a≤b → 1≤U → b-a≤U →
      (N:ℝ)^2≤4*q*U → (∀t∈Set.Icc a b,(N:ℝ)≤2*conductorLength q t ∧ conductorLength q t≤2*N) →
      (∑χ : DirichletCharacter ℂ q with χ.IsPrimitive,∫t in a..b,‖χ.LFunction ((1/2:ℂ)+t*I)‖^4)≤
        C*q.totient*U*(1+Real.log (N^2:ℕ))^4 := by
  classical
  obtain ⟨C,hC,HC⟩ := primitive_L_critical_gaussian_polynomials
  obtain ⟨D,hD,HD⟩ := character_tail_fourth_mean
  let W := 1+∫v,characterMomentGaussian v
  have hw : ∀v,0≤characterMomentGaussian v := fun v=>(Real.exp_pos _).le
  have cw : Continuous characterMomentGaussian := by change Continuous (fun v : ℝ=>Real.exp (-v^2/2));fun_prop
  have hW : 0<W := by dsimp [W];linarith [integral_nonneg (μ:=volume) hw]
  let J := 1+8*π
  let K := 2*weightedHilbertConstant
  let E := 64*((2*π)^4*J+(2*C)^4*W^4*(2*J)+(2*C)^4*W^4*D*(1+5*K))
  have hJ : 0<J := by dsimp [J];positivity
  have hK : 0<K := by dsimp [K];positivity [weightedHilbertConstant_pos]
  refine ⟨E,by dsimp [E];positivity,?_⟩
  intro q N _ hq hN a b U hab hU hlen hsize hX
  let S := (univ:Finset (DirichletCharacter ℂ q)).filter (fun χ=>χ.IsPrimitive)
  let z (σ t : ℝ) := (σ:ℂ)+t*I
  let P (χ : DirichletCharacter ℂ q) := dirichletPoly (fun n : ℕ=>χ n) N
  let f (σ : ℝ) (χ : DirichletCharacter ℂ q) (t : ℝ) := ‖P χ (z σ t)‖
  let r (χ : DirichletCharacter ℂ q) (t : ℝ) := ‖χ.LFunction (z (3/2) t)-P χ (z (3/2) t)‖
  let conv (g : DirichletCharacter ℂ q→ℝ→ℝ) (χ : DirichletCharacter ℂ q) (t : ℝ) :=
    ∫v,characterMomentGaussian v*g χ (t+v)
  let L := 1+Real.log (N^2:ℕ)
  let Y := (q.totient:ℝ)*U
  have hq₀ : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hN₀ : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hY : 0≤Y := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hL : 1≤L := by dsimp [L];linarith [Real.log_nonneg (show (1:ℝ)≤(N^2:ℕ) by exact_mod_cast Nat.one_le_pow 2 N hN)]
  have hh : b-a+2*π*(N:ℝ)^2/q≤J*U := by
    have hdiv : (N:ℝ)^2/q≤4*U := (div_le_iff₀ hq₀).mpr (by nlinarith only [hsize])
    dsimp only [J];rw [mul_div_assoc];nlinarith only [hlen,mul_le_mul_of_nonneg_left hdiv (show 0≤2*π by positivity)]
  have hP := fun v : ℝ => character_polynomial_fourth_means (q:=q) hN (a:=a+v) (b:=b+v) (by linarith)
  have castz (u t : ℝ) : z u t=(u:ℂ)+(t:ℂ)*I := rfl
  have hsub (g : DirichletCharacter ℂ q→ℝ→ℝ) (v : ℝ) :
      (∑χ∈S,∫t in (a+v)..(b+v),g χ t^4)≤∑χ : DirichletCharacter ℂ q,∫t in (a+v)..(b+v),g χ t^4 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun χ _ _=>intervalIntegral.integral_nonneg (by linarith) (fun t _=>by positivity))
  have hmain (v : ℝ) : (∑χ∈S,∫t in (a+v)..(b+v),f (1/2) χ t^4)≤(J*Y)*L^4 := by
    apply (hsub _ v).trans
    have h := (hP v).1
    rw [show b+v-(a+v)=b-a by ring] at h
    simp only [f,P,z,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0≤L) 4)
    exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)).trans_eq (by dsimp [Y];ring)
  have hshort (v : ℝ) : (∑χ∈S,∫t in (a+v)..(b+v),f (1/4) χ t^4)≤(2*J*Y)*(N:ℝ)*L^3 := by
    apply (hsub _ v).trans
    have h := (hP v).2
    rw [show b+v-(a+v)=b-a by ring] at h
    simp only [f,P,z,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    apply h.trans
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) q.totient))
      (by positivity [show 0≤L by linarith] : 0≤2*(N:ℝ)*L^3)).trans_eq
    dsimp [Y,L];ring
  have htail (v : ℝ) : (∑χ∈S,∫t in (a+v)..(b+v),r χ t^4)≤D*(1+5*K)*Y/(N:ℝ)^4*L^3 := by
    apply (hsub _ v).trans
    have h := HD (q:=q) hN (a:=a+v) (b:=b+v) (by linarith)
    rw [show b+v-(a+v)=b-a by ring] at h
    simp only [r,P,z,Complex.ofReal_div,Complex.ofReal_ofNat]
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0≤L) 3)
    have hh' : (b-a+K)+K*((N:ℝ)^2/q)≤(1+5*K)*U := by
      have hdiv : (N:ℝ)^2/q≤4*U := (div_le_iff₀ hq₀).mpr (by nlinarith only [hsize])
      nlinarith only [hlen,mul_le_mul_of_nonneg_left hdiv hK.le,mul_le_mul_of_nonneg_left hU hK.le]
    change (q.totient:ℝ)*D*((b-a+K)/N^4+K/(q*(N:ℝ)^2))≤_
    calc _ = (q.totient:ℝ)*D*((b-a+K)+K*((N:ℝ)^2/q))/(N:ℝ)^4 := by field_simp
         _ ≤ _ := div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left hh' (by positivity : 0≤(q.totient:ℝ)*D)).trans_eq (by dsimp [Y];ring)) (by positivity)
  have cf (σ : ℝ) (χ : DirichletCharacter ℂ q) : Continuous (f σ χ) :=
    ((differentiable_dirichletPoly _ _).continuous.comp (by dsimp [z];fun_prop)).norm
  have cr (χ : DirichletCharacter ℂ q) (hχ : χ∈S) : Continuous (r χ) := by
    have hl := (differentiable_LFunction_of_ne_one (isPrimitive_ne_one (mem_filter.mp hχ).2 hq)).continuous
    exact ((hl.comp (by dsimp [z];fun_prop)).sub ((differentiable_dirichletPoly _ _).continuous.comp (by dsimp [z];fun_prop))).norm
  have hPbound (χ : DirichletCharacter ℂ q) (t : ℝ) : 0≤f (1/4) χ t ∧ f (1/4) χ t≤N := by
    refine ⟨norm_nonneg _,(norm_characterPolynomial_le_power_sum χ N _).trans ?_⟩
    calc _ ≤ ∑_n∈Finset.Icc 1 N,(1:ℝ) := by
                apply sum_le_sum;intro n hn
                apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (mem_Icc.mp hn).1)
                norm_num [z]
         _ = _ := by simp
  have hRbound (χ : DirichletCharacter ℂ q) (t : ℝ) : 0≤r χ t ∧ r χ t≤2 := by
    have h := norm_LFunction_sub_polynomial_absolute χ hN (s:=z (3/2) t) (by norm_num [z])
    have hp := Real.rpow_le_one_of_one_le_of_nonpos (show (1:ℝ)≤N by exact_mod_cast hN) (by norm_num : -(1/2:ℝ)≤0)
    refine ⟨norm_nonneg _,h.trans ?_⟩;norm_num [z] at *;linarith only [hp]
  have hconv (g : DirichletCharacter ℂ q→ℝ→ℝ) {R M : ℝ} (hg : ∀χ∈S,Continuous (g χ))
      (hbound : ∀χ∈S,∀t,0≤g χ t ∧ g χ t≤M) (hmean : ∀v,(∑χ∈S,∫t in (a+v)..(b+v),g χ t^4)≤R) :
      (∑χ∈S,∫t in a..b,conv g χ t^4)≤W^4*R := by
    have H := family_fourth_convolution_le S (conv g) g characterMomentGaussian hab zero_le_one hw cw integrable_characterMomentGaussian hg hbound
      (fun χ hχ t _=>⟨integral_nonneg (fun v=>mul_nonneg (hw v) (hbound χ hχ _).1),by dsimp [conv];rw [one_mul]⟩) hmean
    simpa only [one_pow,one_mul,W] using H
  have hneg := hconv (f (1/4)) (fun χ _=>cf _ χ) (fun χ _=>hPbound χ) hshort
  have hpos := hconv r cr (fun χ _=>hRbound χ) htail
  let A := 2*C*(N:ℝ)^(-(1/4):ℝ)
  let B := 2*C*N
  have hA : 0≤A := by dsimp [A];positivity
  have hB : 0≤B := by dsimp [B];positivity
  let F (χ : DirichletCharacter ℂ q) (t : ℝ) := ‖χ.LFunction ((1/2:ℂ)+t*I)‖
  have hu (χ : DirichletCharacter ℂ q) (hχ : χ∈S) (t : ℝ) (ht : t∈Set.Icc a b) :
      0≤F χ t ∧ F χ t≤2*π*f (1/2) χ t+A*conv (f (1/4)) χ t+B*conv r χ t := by
    have H := HC (χ:=χ) (mem_filter.mp hχ).2 hq hN t
    change ‖χ.LFunction (z (1/2) t)‖≤2*π*f (1/2) χ t+_*conv (f (1/4)) χ t+_*conv r χ t at H
    have he : z (1/2) t=(1/2:ℂ)+t*I := by simp [z]
    rw [he] at H
    have hxx := hX t ht
    have hcneg : (conductorLength q t)^(-(1/4):ℝ)≤2*(N:ℝ)^(-(1/4):ℝ) := by
      apply (Real.rpow_le_rpow_of_nonpos (half_pos hN₀) (by linarith only [hxx.1]) (by norm_num : -(1/4:ℝ)≤0)).trans
      rw [Real.div_rpow hN₀.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul]
      exact (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (1/4:ℝ)≤1)) (Real.rpow_nonneg hN₀.le _)).trans_eq (mul_comm ..)
    refine ⟨norm_nonneg _,H.trans (add_le_add (add_le_add (le_refl _) ?_) ?_)⟩
    · exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hcneg hC.le).trans_eq (by dsimp [A];ring))
        (integral_nonneg (fun v=>mul_nonneg (hw v) (hPbound χ _).1))
    · exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hxx.2 hC.le).trans_eq (by dsimp [B];ring))
        (integral_nonneg (fun v=>mul_nonneg (hw v) (hRbound χ _).1))
  have hc₃ (χ) (hχ : χ∈S) : Continuous (f (1/2) χ) ∧ Continuous (conv (f (1/4)) χ) ∧ Continuous (conv r χ) :=
    ⟨cf _ χ,continuous_positive_convolution cw integrable_characterMomentGaussian hw (cf _ χ) (hPbound χ),
      continuous_positive_convolution cw integrable_characterMomentGaussian hw (cr χ hχ) (hRbound χ)⟩
  have hn₃ (χ) (hχ : χ∈S) (t : ℝ) (_ : t∈Set.Icc a b) : 0≤f (1/2) χ t ∧ 0≤conv (f (1/4)) χ t ∧ 0≤conv r χ t :=
    ⟨norm_nonneg _,integral_nonneg (fun v=>mul_nonneg (hw v) (hPbound χ _).1),
      integral_nonneg (fun v=>mul_nonneg (hw v) (hRbound χ _).1)⟩
  have H := family_three_fourth_le S F (f (1/2)) (conv (f (1/4))) (conv r) hab (by positivity : 0≤2*π) hA hB hc₃ hn₃ hu
  apply H.trans
  have h₀ := hmain 0
  simp only [add_zero] at h₀
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity : 0≤(2*π)^4))
    (mul_le_mul_of_nonneg_left hneg (pow_nonneg hA 4))) (mul_le_mul_of_nonneg_left hpos (pow_nonneg hB 4))) (by norm_num : (0:ℝ)≤64)).trans
  dsimp only [A,B];simp only [mul_pow,inverse_quarter_four hN₀]
  have hL34 : L^3≤L^4 := pow_le_pow_right₀ hL (by decide)
  have hcommon : 0≤(2*C)^4*W^4*(2*J)*Y+(2*C)^4*W^4*D*(1+5*K)*Y := by positivity
  change _≤E*(q.totient:ℝ)*U*L^4
  dsimp only [E,Y] at *
  field_simp
  have hpos : 0≤(L-1)*(2*J*C^4*W^4+C^4*W^4*D*(1+5*K)) := mul_nonneg (sub_nonneg.mpr hL) (by positivity)
  nlinarith only [hpos]

end AnalyticNumberTheory.DirichletLFunctions
