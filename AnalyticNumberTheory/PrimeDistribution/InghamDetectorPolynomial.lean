import AnalyticNumberTheory.PrimeDistribution.InghamRieszInversion
import AnalyticNumberTheory.ExponentialSums.VaughanIdentity

/-!
# The finite polynomial in Ingham's zero detector

The correction which cancels the zeta pole contributes a difference of
two adjacent Riesz means.  This difference has an extra factor n/Y.
-/
noncomputable section
open Complex Real Finset MeasureTheory Filter
open scoped ArithmeticFunction.Moebius Topology
open AnalyticNumberTheory.DirichletSeries
namespace AnalyticNumberTheory.PrimeDistribution

/-- The coefficient used for all zeros in the same height band. -/
def inghamRieszCoeff (X : ℕ) (Y : ℝ) (n : ℕ) : ℂ :=
  if n≤⌊Y⌋₊ then inghamDetectorCoeff X n*(inghamRieszWeight 6 Y n:ℂ) else 0

private theorem weight_mem {Y : ℝ} (hY : 0<Y) {n : ℕ} (hn : n≤⌊Y⌋₊) :
    0≤1-n/Y ∧ 1-n/Y≤1 := by
  have h := (Nat.le_floor_iff hY.le).mp hn
  constructor
  · exact sub_nonneg.mpr ((div_le_one hY).mpr h)
  · exact sub_le_self _ (by positivity)

theorem norm_inghamRieszCoeff {Y : ℝ} (hY : 0<Y) (X n : ℕ) :
    ‖inghamRieszCoeff X Y n‖≤n.divisors.card := by
  rw [inghamRieszCoeff]; split_ifs with hn
  · obtain ⟨ha,hb⟩ := weight_mem hY hn
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,inghamRieszWeight,abs_of_nonneg (pow_nonneg ha _)]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ha hb)).trans (norm_inghamDetectorCoeff X n)
  · simp

/-- Mollified Riesz mean at a complex point. -/
def inghamRieszSum (X k : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  ∑ n∈Icc 1 ⌊Y⌋₊,inghamDetectorCoeff X n*(n:ℂ)^(-ρ)*(inghamRieszWeight k Y n:ℂ)

/-- The sixth-order right-line integral with the pole-cancelling factor. -/
def inghamDetectorRight (X : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  (720/(2*π):ℂ)*(∫ v : ℝ, inghamRieszLine X 6 ρ Y v*(1+((2:ℂ)+v*I)/(ρ-1)))

theorem inghamDetectorRight_eq {X : ℕ} {Y : ℝ} (hY : 0<Y) {ρ : ℂ} (hρ : 0≤ρ.re)
    (hne : ρ≠1) :
    inghamDetectorRight X Y ρ = inghamRieszSum X 6 Y ρ+
      6/(ρ-1)*(inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ) := by
  let F := fun k => inghamRieszLine X k ρ Y
  obtain ⟨i₅,h₅⟩ := ingham_riesz_inversion X 5 (by decide) hρ hY
  obtain ⟨i₆,h₆⟩ := ingham_riesz_inversion X 6 (by decide) hρ hY
  change (120/(2*π):ℂ)*(∫ v,F 5 v)=inghamRieszSum X 5 Y ρ at h₅
  change (720/(2*π):ℂ)*(∫ v,F 6 v)=inghamRieszSum X 6 Y ρ at h₆
  have he (v : ℝ) : F 6 v*(1+((2:ℂ)+v*I)/(ρ-1)) =
      F 6 v+(F 5 v-6*F 6 v)*(ρ-1)⁻¹ := by
    let w := (2:ℂ)+(v:ℂ)*I
    have hj : w+6≠0 := by intro hz; have := congrArg Complex.re hz; norm_num [w] at this
    have hden : rieszDenom 5 w≠0 := by
      have h := norm_rieszDenom_ge (k:=5) (c:=2) (by decide) (by norm_num) v
      change 2^2+v^2≤‖rieszDenom 5 w‖ at h
      intro h0; rw [h0,norm_zero] at h; nlinarith [sq_nonneg v]
    have hsucc : rieszDenom 6 w=rieszDenom 5 w*(w+6) := by
      unfold rieszDenom; rw [Finset.prod_range_succ]; norm_num
    dsimp only [F,inghamRieszLine]; change _/(rieszDenom 6 w)*(1+w/(ρ-1))=
      _/(rieszDenom 6 w)+(_/(rieszDenom 5 w)-6*(_/(rieszDenom 6 w)))*(ρ-1)⁻¹
    rw [hsucc]; field_simp [hden,hj,sub_ne_zero.mpr hne]; ring
  unfold inghamDetectorRight
  change _*(∫ v,F 6 v*(1+((2:ℂ)+v*I)/(ρ-1)))=_
  simp_rw [he]
  have hi : Integrable (fun v => (F 5 v-6*F 6 v)*(ρ-1)⁻¹) := (i₅.sub (i₆.const_mul 6)).mul_const _
  change Integrable (F 6) at i₆
  change Integrable (F 5) at i₅
  rw [integral_add i₆ hi,integral_mul_const,
    integral_sub i₅ (i₆.const_mul 6),integral_const_mul,←h₅,←h₆]
  ring

theorem inghamRieszSum_six_split {X : ℕ} (hX : 1≤X) {Y : ℝ} (hXY : (X:ℝ)≤Y) (ρ : ℂ) :
    inghamRieszSum X 6 Y ρ=(inghamRieszWeight 6 Y 1:ℂ)+
      ∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ) := by
  have hY : 0≤Y := (Nat.cast_nonneg X).trans hXY
  have hN := (Nat.le_floor_iff hY).mpr hXY
  have hunion : Icc 1 ⌊Y⌋₊=Icc 1 X ∪ Ioc X ⌊Y⌋₊ := by ext n; simp; omega
  have hdisj : Disjoint (Icc 1 X) (Ioc X ⌊Y⌋₊) := Finset.disjoint_left.mpr (by
    intro n hn hm; simp only [mem_Icc,mem_Ioc] at hn hm; omega)
  rw [inghamRieszSum,hunion,sum_union hdisj]
  congr 1
  · rw [sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hX⟩)]
    · simp [inghamDetectorCoeff_small hX]
    · intro n hn hn1; simp [inghamDetectorCoeff_small (mem_Icc.mp hn).2,hn1]
  · apply sum_congr rfl; intro n hn
    rw [inghamRieszCoeff,ite_eq_left (mem_Ioc.mp hn).2]; ring

private theorem sum_divisors_le {Y : ℝ} (hY : 1≤Y) :
    ∑ n∈Icc 1 ⌊Y⌋₊,(n.divisors.card:ℝ) ≤ Y*(1+Real.log Y)^3 := by
  have hN : 1≤⌊Y⌋₊ := (Nat.one_le_floor_iff _).mpr hY
  have hfloor := Nat.floor_le (by linarith : 0≤Y)
  have hlog := Real.log_nonneg hY
  calc _ ≤ ∑ n∈Icc 1 ⌊Y⌋₊,(n.divisors.card:ℝ)^2 := by
          refine sum_le_sum fun n hn => ?_
          exact_mod_cast Nat.le_self_pow (by decide : 2≠0) n.divisors.card
       _ ≤ _ := ExponentialSums.sum_Icc_card_divisors_sq_le _
       _ ≤ _ := by rw [max_eq_left hN]; gcongr

/-- The first difference of the two Riesz means has one extra power of n/Y. -/
theorem norm_inghamRieszSum_sub {X : ℕ} {Y : ℝ} (hY : 1≤Y) {ρ : ℂ} (hβ : ρ.re≤1) :
    ‖inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ‖≤Y^(1-ρ.re)*(1+Real.log Y)^3 := by
  have hYp : 0<Y := by linarith
  rw [inghamRieszSum,inghamRieszSum,←sum_sub_distrib]
  calc _ ≤ ∑ n∈Icc 1 ⌊Y⌋₊, _ := norm_sum_le ..
       _ ≤ ∑ n∈Icc 1 ⌊Y⌋₊,(n.divisors.card:ℝ)*Y^(-ρ.re) := by
          apply sum_le_sum; intro n hn
          obtain ⟨hn1,hnY⟩ := mem_Icc.mp hn
          have hn0 : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
          have hnle := (Nat.le_floor_iff hYp.le).mp hnY
          obtain ⟨ha,hb⟩ := weight_mem hYp hnY
          rw [←mul_sub,←Complex.ofReal_sub,inghamRieszWeight,inghamRieszWeight,
            show (1-(n:ℝ)/Y)^5-(1-n/Y)^6=(n/Y)*(1-n/Y)^5 by ring,
            norm_mul,norm_mul,Complex.norm_natCast_cpow_of_pos (by omega),Complex.neg_re,
            Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
          have hfac : (n:ℝ)^(-ρ.re)*(n/Y) ≤ Y^(-ρ.re) := by
            calc (n:ℝ)^(-ρ.re)*(n/Y) = (n:ℝ)^(1-ρ.re)/Y := by
                   rw [sub_eq_add_neg,Real.rpow_add hn0,Real.rpow_one]; ring
                 _ ≤ Y^(1-ρ.re)/Y := by gcongr
                 _ = Y^(-ρ.re) := by rw [sub_eq_add_neg,Real.rpow_add hYp,Real.rpow_one]; field_simp
          calc _ = ‖inghamDetectorCoeff X n‖*((n:ℝ)^(-ρ.re)*(n/Y))*(1-n/Y)^5 := by ring
               _ ≤ (n.divisors.card:ℝ)*Y^(-ρ.re)*1 := by
                    gcongr
                    · exact norm_inghamDetectorCoeff X n
                    · exact pow_le_one₀ ha hb
               _ = _ := mul_one _
       _ = (∑ n∈Icc 1 ⌊Y⌋₊,(n.divisors.card:ℝ))*Y^(-ρ.re) := (sum_mul ..).symm
       _ ≤ (Y*(1+Real.log Y)^3)*Y^(-ρ.re) := by gcongr; exact sum_divisors_le hY
       _ = _ := by rw [sub_eq_add_neg,Real.rpow_add hYp,Real.rpow_one]; ring



/-- On the height band the correction imposed by the pole at one is uniformly
small for every Riesz cutoff between X and X to the power 3/2. -/
theorem ingham_pole_correction_uniform : ∀ᶠ T : ℕ in atTop,
    ∀ (X : ℕ) (Y : ℝ) (ρ : ℂ), 1≤Y → Y≤(T:ℝ)^(3/2:ℝ) →
      1/2≤ρ.re → ρ.re≤1 → (T:ℝ)≤ρ.im →
      ‖6/(ρ-1)*(inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ)‖≤1/16 := by
  have ht := ((isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ)<1/4)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hs := ht.eventually_le_const (by norm_num : (0:ℝ)<1/(16*162))
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hs,hl,eventually_ge_atTop 2] with T hsmall hlog hX X Y ρ hXY hY hβ hβ' hγ
  have hx : (2:ℝ)≤T := by exact_mod_cast hX
  have hxp : (0:ℝ)<T := by linarith
  have hy : 1≤Y := hXY
  change 1≤Real.log (T:ℝ) at hlog
  change Real.log (T:ℝ)^(3:ℝ)/(T:ℝ)^(1/4:ℝ) ≤ _ at hsmall
  rw [Real.rpow_ofNat] at hsmall
  have him : (T:ℝ)≤‖ρ-1‖ := hγ.trans (by simpa using Complex.im_le_norm (ρ-1))
  have hlogY : 1+Real.log Y≤3*Real.log (T:ℝ) := by
    have h := Real.log_le_log (by linarith : 0<Y) hY
    rw [Real.log_rpow hxp] at h; linarith
  have hpowY : Y^(1-ρ.re)≤(T:ℝ)^(3/4:ℝ) := by
    calc _ ≤ Y^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
         _ ≤ ((T:ℝ)^(3/2:ℝ))^(1/2:ℝ) := Real.rpow_le_rpow (by linarith) hY (by norm_num)
         _ = _ := by rw [←Real.rpow_mul hxp.le]; norm_num
  have hxsplit : (T:ℝ)=(T:ℝ)^(3/4:ℝ)*(T:ℝ)^(1/4:ℝ) := by
    rw [←Real.rpow_add hxp]; norm_num
  have h1 : 0≤1+Real.log Y := by linarith [Real.log_nonneg hy]
  rw [norm_mul,norm_div,show ‖(6:ℂ)‖=(6:ℝ) by norm_num]
  calc _ ≤ (6/(T:ℝ))*(Y^(1-ρ.re)*(1+Real.log Y)^3) := by
          gcongr; exact norm_inghamRieszSum_sub hy hβ'
       _ ≤ (6/(T:ℝ))*((T:ℝ)^(3/4:ℝ)*(3*Real.log (T:ℝ))^3) := by gcongr
       _ = 162*(Real.log (T:ℝ)^3/(T:ℝ)^(1/4:ℝ)) := by
          conv_lhs => enter [1,2]; rw [hxsplit]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hxp (3/4:ℝ)),
            ne_of_gt (Real.rpow_pos_of_pos hxp (1/4:ℝ))]; ring
       _ ≤ _ := by linarith

/-- Pole correction when the mollifier length is the band height. -/
theorem ingham_pole_correction_small : ∀ᶠ X : ℕ in atTop,
    ∀ (Y : ℝ) (ρ : ℂ), (X:ℝ)≤Y → Y≤(X:ℝ)^(3/2:ℝ) →
      1/2≤ρ.re → ρ.re≤1 → (X:ℝ)≤ρ.im →
      ‖6/(ρ-1)*(inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ)‖≤1/16 := by
  filter_upwards [ingham_pole_correction_uniform,eventually_ge_atTop 1] with X H hX Y ρ hXY
  exact H X Y ρ ((by exact_mod_cast hX : (1:ℝ)≤X).trans hXY)

/-- At every sufficiently large height band, either the common finite polynomial
is large or the normalized Mellin integral is large. -/
theorem ingham_right_dichotomy_uniform : ∀ᶠ T : ℕ in atTop,
    ∀ (X : ℕ) (Y : ℝ) (ρ : ℂ), 1≤X → (X:ℝ)≤Y → 16≤Y → Y≤(T:ℝ)^(3/2:ℝ) →
      1/2≤ρ.re → ρ.re≤1 → (T:ℝ)≤ρ.im →
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨
      1/4≤‖inghamDetectorRight X Y ρ‖ := by
  filter_upwards [ingham_pole_correction_uniform,eventually_ge_atTop 16] with T hc hT X Y ρ hX hXY hy hY hβ hβ' hγ
  have hx : (16:ℝ)≤T := by exact_mod_cast hT
  have hYp : 0<Y := by linarith
  have hne : ρ≠1 := by intro he; rw [he,Complex.one_im] at hγ; linarith
  let S := ∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)
  let E := 6/(ρ-1)*(inghamRieszSum X 5 Y ρ-inghamRieszSum X 6 Y ρ)
  let W : ℂ := (inghamRieszWeight 6 Y 1:ℂ)
  have heq : inghamDetectorRight X Y ρ=W+S+E := by
    rw [inghamDetectorRight_eq hYp (by linarith) hne]
    exact congrArg (fun z => z+E) (inghamRieszSum_six_split (by omega : 1≤X) hXY ρ)
  have hW : 1/2≤‖W‖ := by
    have hrec : 1/Y≤1/16 := by gcongr
    have hbase : 15/16≤1-1/Y := by linarith
    have hpow : (15/16:ℝ)^6 ≤ (1-1/Y)^6 := by gcongr
    change _≤‖((inghamRieszWeight 6 Y 1:ℝ):ℂ)‖
    rw [Complex.norm_real,Real.norm_eq_abs,inghamRieszWeight,Nat.cast_one,
      abs_of_nonneg (by positivity : 0≤(1-1/Y)^6)]
    norm_num at hpow ⊢; linarith
  have hE : ‖E‖≤1/16 := hc X Y ρ (by linarith) hY hβ hβ' hγ
  change 1/8≤‖S‖ ∨ _
  by_cases hS : 1/8≤‖S‖
  · exact Or.inl hS
  right
  have htri : ‖W‖≤‖inghamDetectorRight X Y ρ‖+‖E‖+‖S‖ := by
    calc _ = ‖(inghamDetectorRight X Y ρ-E)-S‖ := by rw [heq]; abel_nf
         _ ≤ ‖inghamDetectorRight X Y ρ-E‖+‖S‖ := norm_sub_le ..
         _ ≤ _ := add_le_add (norm_sub_le ..) le_rfl
  linarith

/-- The preceding dichotomy at mollifier length equal to the band height. -/
theorem ingham_right_dichotomy : ∀ᶠ X : ℕ in atTop,
    ∀ (Y : ℝ) (ρ : ℂ), (X:ℝ)≤Y → Y≤(X:ℝ)^(3/2:ℝ) →
      1/2≤ρ.re → ρ.re≤1 → (X:ℝ)≤ρ.im →
      1/8≤‖∑ n∈Ioc X ⌊Y⌋₊,inghamRieszCoeff X Y n*(n:ℂ)^(-ρ)‖ ∨
      1/4≤‖inghamDetectorRight X Y ρ‖ := by
  filter_upwards [ingham_right_dichotomy_uniform,eventually_ge_atTop 16] with X H hX Y ρ hXY
  exact H X Y ρ (by omega) hXY ((by exact_mod_cast hX : (16:ℝ)≤X).trans hXY)

end AnalyticNumberTheory.PrimeDistribution
