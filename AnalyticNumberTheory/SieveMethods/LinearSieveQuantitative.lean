import AnalyticNumberTheory.SieveMethods.LinearSieveRateCutoff
import AnalyticNumberTheory.SieveMethods.LinearSieveEstimate

/-! # Quantitative fundamental theorem of the dimension-one linear sieve

For a fixed upper dimension bound A, local separation B, and dimension-loss
coefficient D, the lower dimension parameter may grow up to D log y /
(log log y)⁵. Throughout 2 ≤ z ≤ √y the error in both sieve profiles is
O((log log y)^(−3/10)). Arithmetic remainders retain coefficient one.
-/
noncomputable section
open Real Finset Set Filter
open scoped Topology
namespace AnalyticNumberTheory.SieveMethods

/-- Quantitative upper and lower errors, in terms of the logarithmic level Y. -/
theorem linearSieve_logLevel_rate {A B D : ℝ} (hA : 0≤A) (hB : 0<B) (hD : 0≤D) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ Y : ℝ in atTop, ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) →
      0≤s.X → (∀p∈P,s.density p≤1-1/B) → ∀ {L z : ℝ}, 0≤L → L≤D*Y/(log Y)^5 →
      2≤z → log z≤Y → SieveLogMassBounds P s.density 2 z L A →
      ∀ b : Bool, (if b then (1:ℝ) else 2)≤Y/log z →
        let V := sieveEulerBelow P s.density z
        linearSieveSign b ((siftedCountOf s.A (sieveProductBelow P z):ℝ)-
          s.X*V*linearSieveFunction b (Y/log z)) ≤
          c*(log Y)^(-(3/10:ℝ))*s.X*V +
            ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<exp Y),|s.rem d| := by
  let k := linearSieveEulerConstant A B
  let K := exp (2*k)
  let J := K*(D+120*k)
  have hk : 0≤k := by dsimp [k,linearSieveEulerConstant]; positivity
  have hK : 1≤K := Real.one_le_exp (by positivity)
  have hKp : 0<K := exp_pos _
  have hJ : 0≤J := by dsimp [J]; positivity
  obtain ⟨C,hC,hf⟩ := linearSieve_two_cutoff_sharp hK
  let c := 6*exp eulerMascheroniConstant*J*K^2+C*(40*K^2*(Nat.factorial 53:ℝ)+5120)
  have hcp : 0<c := by dsimp [c]; positivity
  refine ⟨c,hcp,?_⟩
  have hvtop : Tendsto (fun Y : ℝ => (log Y)^(1/20:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).comp Real.tendsto_log_atTop
  filter_upwards [hvtop.eventually_ge_atTop (max 120 (10000*J)),eventually_gt_atTop (1:ℝ)] with Y hvY hY
  intro s P hP hX hsep L z hL hLY hz hzY H b hu V
  let v := (log Y)^(1/20:ℝ)
  have hv : 120≤v := (le_max_left ..).trans hvY
  have hv₀ : 0<v := by linarith
  have hv₁ : 1≤v := by linarith
  have hJv : 10000*J≤v := (le_max_right ..).trans hvY
  have hlog := log_pos hY
  have hv20 : v^20=log Y := by
    rw [show v^20=v^(20:ℝ) by norm_num,show v=(log Y)^(1/20:ℝ) by rfl,← Real.rpow_mul hlog.le]
    norm_num
  have hv100 : v^100≤120*Y := by
    have H := Real.pow_div_factorial_le_exp (log Y) hlog.le 5
    rw [Real.exp_log (by linarith),←hv20] at H
    norm_num [Nat.factorial] at H
    rw [←pow_mul] at H
    norm_num at H
    linarith
  have hLv : L*v^100≤D*Y := by
    have H := (le_div_iff₀ (pow_pos hlog 5)).mp hLY
    rwa [←hv20,←pow_mul] at H
  let w := min z (exp (Y/v^23))
  let η := J/v^54
  let r := log z/log w
  let u := Y/log z
  let m := ⌊20*log v⌋₊
  obtain ⟨hw,hwz,hdim,ha,hr',hur⟩ := linearSieve_rate_cutoff hA hB hD hL hv hv100 hz hzY hLv s P hP hsep H
  have hη : 0≤η := div_nonneg hJ (pow_nonneg hv₀.le _)
  have hη' : η≤1/10000 := by
    apply (div_le_iff₀ (pow_pos hv₀ _)).mpr
    have hv54 : v≤v^54 := by simpa using pow_le_pow_right₀ hv₁ (by norm_num : 1≤54)
    linarith
  have hV := (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z).le
  have hz₁ : 1<z := by linarith
  have hw₁ : 1<w := by change 2≤w at hw; linarith
  have hr : 0≤r := div_nonneg (Real.log_pos hz₁).le (Real.log_pos hw₁).le
  have hu₁ : 1≤u := by dsimp [u]; cases b <;> simp_all <;> linarith
  have hE : η*(K*r)^2 ≤ J*K^2/v^6 := by
    calc _ ≤ η*(K*v^23)^2 := by gcongr
         _ = J*K^2/v^8 := by dsimp [η]; field_simp [hv₀.ne'] <;> ring
         _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hv₁ (by norm_num))
  have hshort := linearSieve_rate_short hKp.le hv₁ hr hr' hur
  have hdeep := (linearSieve_rate_depth hv₁).2.2
  have hcoeff : 6*exp eulerMascheroniConstant*η*(K*r)^2 +
      C*((2*m:ℕ)*(K*r)^2*exp (-(u*r/3^m))+2560*(74/100:ℝ)^m) ≤ c/v^6 := by
    change (74/100:ℝ)^m≤2/v^6 at hdeep
    change ((2*m:ℕ):ℝ)*(K*r)^2*exp (-(u*r/3^m))≤_ at hshort
    dsimp only [c]
    have h₁ := mul_le_mul_of_nonneg_left hE (show 0≤6*exp eulerMascheroniConstant by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (add_le_add hshort (mul_le_mul_of_nonneg_left hdeep (by norm_num : (0:ℝ)≤2560))) hC.le
    convert add_le_add h₁ h₂ using 1 <;> ring
  have hpow : (log Y)^(-(3/10:ℝ))=(v^6)⁻¹ := by
    rw [Real.rpow_neg hlog.le]
    congr 1
    rw [show v^6=v^(6:ℝ) by norm_num,show v=(log Y)^(1/20:ℝ) from rfl,← Real.rpow_mul hlog.le]
    norm_num
  have T := hf s P hP hX hw hwz (by linarith : 0<Y) hη hη' hdim ha m b hu
  dsimp only at T
  rw [linearSieveProfile,max_eq_right hu₁] at T
  apply T.trans
  apply add_le_add_left
  rw [hpow]
  convert mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hX hV) using 1 <;> ring

/-- The quantitative dimension-one linear sieve with ordinary arithmetic
remainders below y. The level and the sifting cutoff may vary independently. -/
theorem linearSieve_quantitative_bounds {A B D : ℝ} (hA : 0≤A) (hB : 0<B) (hD : 0≤D) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ y : ℝ in atTop, ∀ (s : SieveData) (P : Finset ℕ), (∀p∈P,p.Prime) →
      0≤s.X → (∀p∈P,s.density p≤1-1/B) → ∀ {L z : ℝ}, 0≤L →
      L≤D*log y/(log (log y))^5 → 2≤z → z≤y → SieveLogMassBounds P s.density 2 z L A →
      let u := log y/log z
      let X := s.X*sieveEulerBelow P s.density z
      let E := c*(log (log y))^(-(3/10:ℝ))
      let R := ∑d∈(sieveProductBelow P z).divisors.filter (fun d : ℕ => (d:ℝ)<y),|s.rem d|
      X*(linearSieveLower u-E)-R≤(siftedCountOf s.A (sieveProductBelow P z):ℝ) ∧
        (siftedCountOf s.A (sieveProductBelow P z):ℝ)≤X*(linearSieveUpper u+E)+R := by
  obtain ⟨c,hc,H⟩ := linearSieve_logLevel_rate hA hB hD
  refine ⟨c,hc,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually H, Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with y hy hy₁
  intro s P hP hX hsep L z hL hLy hz hzy hdim u X E R
  have hz' : 0<z := by linarith
  have hy' : 0<y := hz'.trans_le hzy
  have hlog := Real.log_le_log hz' hzy
  have hu : 1≤u := (one_le_div (Real.log_pos (show 1<z by linarith))).2 hlog
  let S : ℝ := siftedCountOf s.A (sieveProductBelow P z)
  let V := sieveEulerBelow P s.density z
  have H' := hy s P hP hX hsep hL hLy hz hlog hdim
  rw [Real.exp_log hy'] at H'
  have hup := H' true hu
  change S-X*linearSieveUpper u ≤ E*s.X*V+R at hup
  have hV := (sieveEulerBelow_pos P (fun p hp => s.density_lt_one_of_prime (hP p hp)) z).le
  have hXV : 0≤X := mul_nonneg hX hV
  have hE : 0≤E := mul_nonneg hc.le (Real.rpow_nonneg (Real.log_nonneg hy₁) _)
  have hR : 0≤R := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hS : 0≤S := Nat.cast_nonneg _
  change X*(linearSieveLower u-E)-R≤S ∧ S≤X*(linearSieveUpper u+E)+R
  have hprod : E*s.X*V=X*E := by dsimp only [X,V]; ring
  rw [hprod] at hup
  constructor
  · by_cases hu₂ : 2≤u
    · have hlo := H' false hu₂
      change -(S-X*linearSieveLower u)≤E*s.X*V+R at hlo
      rw [hprod] at hlo
      linarith only [hlo]
    · rw [(linearSieve_initial ⟨hu,(not_le.mp hu₂).le⟩).2]
      nlinarith only [mul_nonneg hXV hE,hR,hS]
  · linarith only [hup]

end AnalyticNumberTheory.SieveMethods
