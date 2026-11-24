import AnalyticNumberTheory.PrimeDistribution.LeastPrimeDensityBound
import AnalyticNumberTheory.DirichletLFunctions.FamilyZeroRepulsion

/-!
# The high zero moment for the least prime in a residue class

A simple exceptional real zero is separated from the family. The remaining
zeros receive the logarithmic Deuring–Heilbronn saving. A polynomial lower
bound on the exceptional gap handles the fixed-width cap in repulsion.
-/

noncomputable section
open Finset Complex
open scoped Classical
open AnalyticNumberTheory.DirichletLFunctions
namespace AnalyticNumberTheory.PrimeDistribution

private lemma positive_gap_of_repulsion {D L u d : ℝ} (hD : 0<D) (hL : 0<L)
    (hu : 0<u) (hu1 : u≤1) (huD : u≤1/(max (2*D) 1)^2)
    (huL : Real.exp (-(2*L))≤u)
    (hr : min (1/32) (Real.log (1/(2*D*u))/(2*D*L)) ≤ d) :
    min (1/64) (1/(4*D))*Real.log (1/u) ≤ d*L := by
  let H := max (2*D) 1
  have hH : 1≤H := le_max_right ..
  have hHp : 0<H := by linarith
  have h2D : 0<2*D := by positivity
  have hlog : 0≤Real.log (1/u) := Real.log_nonneg ((one_le_div hu).mpr hu1)
  have hlU : Real.log (1/u) ≤ 2*L := by
    have hh := Real.log_le_log (Real.exp_pos _) huL
    rw [Real.log_exp] at hh
    rw [Real.log_div one_ne_zero hu.ne',Real.log_one]; linarith
  have hlD : 2*Real.log (2*D) ≤ Real.log (1/u) := by
    have huH := (le_div_iff₀ (sq_pos_of_pos hHp)).mp huD
    have hpow : H^2≤1/u := (le_div_iff₀ hu).mpr (by linarith)
    have hlogH := Real.log_le_log (sq_pos_of_pos hHp) hpow
    rw [Real.log_pow] at hlogH
    have hmono := Real.log_le_log h2D (show 2*D≤H from le_max_left ..)
    norm_num only [Nat.cast_ofNat] at hlogH; linarith
  have hle := mul_le_mul_of_nonneg_right hr hL.le
  rw [min_mul_of_nonneg _ _ hL.le] at hle
  apply le_trans _ hle
  apply le_min
  · have h := mul_le_mul_of_nonneg_right (min_le_left (1/64:ℝ) (1/(4*D))) hlog
    linarith
  · have he : Real.log (1/(2*D*u)) = Real.log (1/u)-Real.log (2*D) := by
      rw [Real.log_div one_ne_zero (mul_pos h2D hu).ne',Real.log_div one_ne_zero hu.ne',Real.log_mul h2D.ne' hu.ne']; ring
    rw [he,show (Real.log (1/u)-Real.log (2*D))/(2*D*L)*L = (Real.log (1/u)-Real.log (2*D))/(2*D) by field_simp]
    apply (mul_le_mul_of_nonneg_right (min_le_right (1/64:ℝ) (1/(4*D))) hlog).trans
    apply (le_div_iff₀ h2D).mpr
    have heq : 1/(4*D)*Real.log (1/u)*(2*D) = Real.log (1/u)/2 := by field_simp; ring
    rw [heq]; linarith

private lemma small_gap_exponential {u : ℝ} (hu : 0<u) (hu1 : u≤1) :
    Real.exp (-u) ≤ 1-u/2 := by
  rw [Real.exp_neg]
  apply (inv_anti₀ (by linarith : 0<1+u) (by linarith [Real.add_one_le_exp u] : 1+u ≤ Real.exp u)).trans
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0<1+u)).mpr
  nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]

private lemma repelled_exponential {b k u x K : ℝ} (hb : 0≤b) (hbk : 2 ≤ b*k)
    (hK : 0<K) (hu : 0<u) (hu1 : u≤1) (huK : u≤1/(4*K))
    (hx : k*Real.log (1/u) ≤ x) : K*Real.exp (-b*x) ≤ u/4 := by
  have hlog := Real.log_nonneg ((one_le_div hu).mpr hu1)
  have harg : -b*x ≤ -(2*Real.log (1/u)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hx hb,mul_le_mul_of_nonneg_right hbk hlog]
  have hex : Real.exp (-(2*Real.log (1/u)))=u^2 := by
    rw [Real.log_div one_ne_zero hu.ne',Real.log_one,show -(2*(0-Real.log u))=(2:ℕ)*Real.log u by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log hu]
  have hKu := (le_div_iff₀ (by positivity : 0<4*K)).mp huK
  calc
    _ ≤ K*Real.exp (-(2*Real.log (1/u))) := by gcongr
    _ = K*u^2 := by rw [hex]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hKu hu.le]



private lemma two_le_nonprincipal_level {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ≠1) : 2≤d := by
  by_contra! hh
  have hd : d=1 := by have := NeZero.pos d; omega
  subst d
  exact hχ (Subsingleton.elim ..)

/-- At height one, an exceptionally small scaled gap belongs to a simple real
zero. All other scaled gaps grow at least logarithmically in its reciprocal. -/
theorem linnik_small_gap_repulsion :
    ∃ k > 0, ∃ c > 0, ∃ θ > 0, ∃ Q₀ : ℕ, 1≤Q₀ ∧ ∀ {Q : ℕ}, Q₀≤Q →
    ∀ j₀ ∈ linnikZeroFamily Q 0, linnikScaledGap Q j₀ ≤ θ →
    let u := linnikScaledGap Q j₀
    0<u ∧ u≤1 ∧ c/(Q:ℝ)≤u ∧ linnikZeroWeight j₀=1 ∧
      ∀ j ∈ (linnikZeroFamily Q 0).erase j₀, k*Real.log (1/u) ≤ linnikScaledGap Q j := by
  obtain ⟨D,hD,HR⟩ := deuring_heilbronn_family
  obtain ⟨c,hc,HS⟩ := siegel_zero_bound 1 (by norm_num)
  obtain ⟨g,hg,HZ⟩ := zeroFreeRegion
  let k := min (1/64) (1/(4*D))
  let θ := min 1 (min g (1/(max (2*D) 1)^2))
  let Q₀ := ⌈max 4 (1/c)⌉₊
  have hQ₀ : (4:ℝ)≤Q₀ := (le_max_left ..).trans (Nat.le_ceil _)
  have hQ₀' : 1≤Q₀ := by exact_mod_cast (by linarith : (1:ℝ)≤Q₀)
  refine ⟨k,by dsimp [k]; positivity,c,hc,θ,by dsimp [θ]; positivity,Q₀,hQ₀',?_⟩
  intro Q hQ j₀ hj₀ hθ
  let L := linnikScale Q
  let u := linnikScaledGap Q j₀
  have hq := linnik_zero_level hj₀
  let : NeZero j₀.1.1 := ⟨by omega⟩
  obtain ⟨hp₀,hn₀,hz₀,hr₀,_,hr₁,ht₀⟩ := linnik_zero_properties hj₀
  have hQ' : (Q₀:ℝ)≤Q := by exact_mod_cast hQ
  have hQ4 : (4:ℝ)≤Q := hQ₀.trans hQ'
  have hQc : 1/c ≤ (Q:ℝ) := ((le_max_right ..).trans (Nat.le_ceil _)).trans hQ'
  have hQp : 0<(Q:ℝ) := by linarith
  have hQone : 1≤Q := hQ₀'.trans hQ
  have hL : 1≤L := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h4 := Real.log_le_log (by norm_num : 0<(2:ℝ)^2) (by linarith : (2:ℝ)^2 ≤ 3*Q)
    rw [Real.log_pow] at h4; norm_num only [Nat.cast_ofNat] at h4; norm_num at h
    change 1≤Real.log (3*Q); linarith
  have hLp : 0<L := by linarith
  have hu : 0<u := mul_pos (sub_pos.mpr hr₁) hLp
  have hu1 : u≤1 := hθ.trans (min_le_left ..)
  have hug : u≤g := hθ.trans ((min_le_right ..).trans (min_le_left ..))
  have huD : u≤1/(max (2*D) 1)^2 := hθ.trans ((min_le_right ..).trans (min_le_right ..))
  have hqR : (j₀.1.1:ℝ)≤Q := by exact_mod_cast hq.2
  have hqR' : (1:ℝ)≤j₀.1.1 := by exact_mod_cast hq.1
  let v := Real.log ((j₀.1.1:ℝ)*(|j₀.2.im|+2))
  have hv : 0<v := Real.log_pos (by nlinarith [abs_nonneg j₀.2.im,mul_nonneg (sub_nonneg.mpr hqR') (abs_nonneg j₀.2.im)])
  have hvL : v≤L := by
    apply Real.log_le_log (by positivity)
    rw [mul_comm 3]
    exact mul_le_mul hqR (by linarith) (by positivity) hQp.le
  have hgap : 1-g/v ≤ j₀.2.re := by
    have h := (mul_le_mul_of_nonneg_left hvL (sub_nonneg.mpr hr₁.le)).trans hug
    have := (le_div_iff₀ hv).mpr h; linarith
  obtain ⟨hreal,_,him,_,hsimple,_⟩ := HZ j₀.1.2 j₀.2 (.inl hn₀) hgap hz₀
  have he₀ : (j₀.2.re:ℂ)=j₀.2 := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
  have hzα : DirichletCharacter.LFunction j₀.1.2 (j₀.2.re:ℂ)=0 := by rw [he₀]; exact hz₀
  have hcut := HS (two_le_nonprincipal_level hn₀) hreal hn₀ j₀.2.re hzα
  rw [Real.rpow_neg (by positivity),Real.rpow_one] at hcut
  have hcg : c/(Q:ℝ) ≤ u := by
    calc
      _ ≤ c/(j₀.1.1:ℝ) := div_le_div_of_nonneg_left hc.le (by positivity) hqR
      _ ≤ 1-j₀.2.re := by rw [div_eq_mul_inv]; linarith
      _ ≤ (1-j₀.2.re)*L := le_mul_of_one_le_right (sub_nonneg.mpr hr₁.le) hL
  have hlow : Real.exp (-(2*L))≤u := by
    rw [Real.exp_neg,show (2:ℝ)*L = (2:ℕ)*L by norm_num,Real.exp_nat_mul,show Real.exp L=3*Q from Real.exp_log (by positivity)]
    apply le_trans _ hcg
    rw [inv_eq_one_div,div_le_div_iff₀ (by positivity) hQp]
    have hh := (div_le_iff₀ hc).mp hQc
    nlinarith only [mul_le_mul_of_nonneg_left hh hQp.le,mul_nonneg (sq_nonneg (Q:ℝ)) hc.le]
  refine ⟨hu,hu1,hcg,?_,?_⟩
  · simp [linnikZeroWeight,characterZeroMultiplicity,NeZero.ne j₀.1.1,hsimple]
  intro j hj
  have hj' := mem_of_mem_erase hj
  have hℓ := linnik_zero_level hj'
  let : NeZero j.1.1 := ⟨by omega⟩
  obtain ⟨hp,hn,hz,hleft,_,hright,ht⟩ := linnik_zero_properties hj'
  have hdis : j₀.1≠⟨j.1.2.conductor,j.1.2.primitiveCharacter⟩ ∨ j.2≠(j₀.2.re:ℂ) := by
    rw [primitive_character_pair hp,he₀]
    by_contra! hh
    exact (ne_of_mem_erase hj) (Prod.ext hh.1.symm hh.2)
  have hℓR : (j.1.1:ℝ)≤Q := by exact_mod_cast hℓ.2
  have hdpos : 0<(j₀.1.1:ℝ) := by linarith
  have hdpos' : 0<(j.1.1:ℝ) := by exact_mod_cast hℓ.1
  have hscale : Real.log ((j₀.1.1:ℝ)*j.1.2.conductor*(|j.2.im|+2)) ≤ 2*L := by
    change _ ≤ 2*Real.log (3*Q)
    rw [show 2*Real.log (3*(Q:ℝ)) = Real.log ((3*(Q:ℝ))^2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by rw [show j.1.2.conductor=j.1.1 from hp]; positivity)
    rw [show j.1.2.conductor=j.1.1 from hp]
    calc
      _ ≤ (Q:ℝ)*Q*3 := by gcongr <;> linarith
      _ ≤ _ := by nlinarith [sq_nonneg (Q:ℝ)]
  have hh := HR j.1.2 hp₀ hreal hn₀ hzα hz hleft hright hdis hscale
  have hrep : min (1/32) (Real.log (1/(2*D*u))/(2*D*L)) ≤ 1-j.2.re := by
    change min (1/32) (Real.log (1/(D*(1-j₀.2.re)*(2*L)))/(D*(2*L))) ≤ 1-j.2.re at hh
    rw [show D*(1-j₀.2.re)*(2*L)=2*D*u by change _=2*D*((1-j₀.2.re)*L); ring,show D*(2*L)=2*D*L by ring] at hh
    exact hh
  exact positive_gap_of_repulsion hD hLp hu hu1 huD hlow hrep



/-- At every sufficiently large modulus the complete zero contribution to the
least-prime moment lies a distance at least `κ/Q` below the principal term.
The estimate remains valid for every larger order. -/
theorem linnik_zero_sum_le :
    ∃ κ > 0, ∃ M > 0, ∃ Q₀ : ℕ, ∀ {Q : ℕ}, Q₀≤Q → ∀ m : ℕ,
      M*Real.log (3*(Q:ℝ)) ≤ m →
      ∑ j ∈ linnikZeroFamily Q 0,(characterZeroMultiplicity j.1.2 j.2:ℝ)*‖leastPrimeZeroRatio j.2‖^(m+1) ≤
        1-κ/(Q:ℝ) := by
  obtain ⟨A,hA,K,hK,HM⟩ := linnik_zero_moment_of_gap
  obtain ⟨k,hk,c,hc,θ,hθ,Q₀,hQ₀,HR⟩ := linnik_small_gap_repulsion
  let v := min θ (1/(4*K))
  have hv : 0<v := by dsimp [v]; positivity
  let b := max (2/k) ((|Real.log (2*K)|+1)/v)
  have hbk : 2 ≤ b*k := (div_le_iff₀ hk).mp (le_max_left ..)
  have hbv : |Real.log (2*K)|+1 ≤ b*v := (div_le_iff₀ hv).mp (le_max_right ..)
  have hb : 0<b := lt_of_lt_of_le (by positivity : 0<2/k) (le_max_left ..)
  let κ := min c 1 / 4
  have hκ : 0<κ := by dsimp [κ]; positivity
  let M := A+1+b
  have hM : 1 ≤ M := by dsimp [M]; linarith
  refine ⟨κ,hκ,M,by linarith,Q₀,?_⟩
  intro Q hQ m hm
  have hQone := hQ₀.trans hQ
  have hqR : (1:ℝ) ≤ Q := by exact_mod_cast hQone
  have hqpos : 0<(Q:ℝ) := by linarith
  let S := linnikZeroFamily Q 0
  let L := linnikScale Q
  have hL : 0<L := linnikScale_pos hQone
  have hm' : (A+1+b)*L ≤ (m:ℝ)+1 := by linarith only [show (A+1+b)*L≤m from hm]
  have hLm : L≤(m:ℝ)+1 := (le_mul_of_one_le_left hL.le hM).trans hm'
  let W (j : LinnikZeroIndex) := linnikZeroWeight j*‖leastPrimeZeroRatio j.2‖^(m+1)
  change ∑ j ∈ S,W j ≤ _
  by_cases hsmall : ∃ j ∈ S,linnikScaledGap Q j≤v
  · obtain ⟨j₀,hj₀,hv₀⟩ := hsmall
    let u := linnikScaledGap Q j₀
    obtain ⟨hu,hu1,huc,hw,hsep⟩ := HR hQ j₀ hj₀ (hv₀.trans (min_le_left ..))
    have hu' : 0<u := hu
    have herr := HM hQone (S.erase j₀) (erase_subset ..) hb.le hsep hm'
    have hrep := repelled_exponential hb.le hbk hK hu' hu1 (hv₀.trans (min_le_right ..)) (le_refl (k*Real.log (1/u)))
    have hrest : ∑ j ∈ S.erase j₀,W j ≤ u/4 := herr.trans hrep
    have hℓ := linnik_zero_level hj₀
    let : NeZero j₀.1.1 := ⟨by omega⟩
    obtain ⟨_,_,_,h0,_,h1,_⟩ := linnik_zero_properties hj₀
    have hsingle : W j₀ ≤ 1-u/2 := by
      dsimp only [W]; rw [hw,one_mul]
      apply le_trans _ (small_gap_exponential hu' hu1)
      calc
        _ ≤ Real.exp (-(1-j₀.2.re))^(m+1) := pow_le_pow_left₀ (norm_nonneg _) (norm_leastPrimeZeroRatio_le_exp h0.le h1.le) _
        _ ≤ _ := by
          rw [←Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
          change (↑(m+1):ℝ)* -(1-j₀.2.re) ≤ -((1-j₀.2.re)*L)
          push_cast; nlinarith only [mul_le_mul_of_nonneg_right hLm (sub_nonneg.mpr h1.le)]
    have hκc : κ/(Q:ℝ) ≤ u/4 := by
      have hh := div_le_div_of_nonneg_right (min_le_left c 1) hqpos.le
      change min c 1 / 4 / (Q:ℝ) ≤ u/4
      rw [div_right_comm]; exact div_le_div_of_nonneg_right (hh.trans huc) (by norm_num)
    rw [←sum_erase_add _ _ hj₀]
    linarith only [hrest,hsingle,hκc]
  · have hsep (j : LinnikZeroIndex) (hj : j∈S) : v≤linnikScaledGap Q j :=
      le_of_lt (lt_of_not_ge (fun hh => hsmall ⟨j,hj,hh⟩))
    have hh := HM hQone S (le_refl _) hb.le hsep hm'
    have hconst : K*Real.exp (-b*v) ≤ 1/2 := by
      have hbnd : -b*v ≤ -Real.log (2*K) := by linarith [le_abs_self (Real.log (2*K))]
      calc
        _ ≤ K*Real.exp (-Real.log (2*K)) := by gcongr
        _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity)]; field_simp
    have hκq : κ/(Q:ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ hqpos).mpr
      dsimp only [κ]; linarith [min_le_right c 1]
    exact (hh.trans hconst).trans (by linarith)



end AnalyticNumberTheory.PrimeDistribution
