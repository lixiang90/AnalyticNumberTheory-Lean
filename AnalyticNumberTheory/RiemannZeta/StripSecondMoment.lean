import AnalyticNumberTheory.RiemannZeta.StripMomentApproximation
import AnalyticNumberTheory.SieveMethods.WeightedMeanValues
import AnalyticNumberTheory.AnalyticTools.PowerWeightedIntegrals

/-!
# An effective second moment to the right of the critical line

For each fixed 1/2 < σ < 1 the integral has main term T ζ(2σ) and
error O(T^(2−2σ)). Individual spacings in the mean value theorem
remove the logarithm from the off-diagonal terms.
-/
open Real Complex Finset MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.DirichletSeries AnalyticNumberTheory.SieveMethods AnalyticNumberTheory.AnalyticTools
namespace AnalyticNumberTheory.RiemannZeta

/-- Continuity of zeta on a vertical line away from its pole. -/
theorem continuous_vertical_zeta {σ : ℝ} (hσ : σ≠1) : Continuous (fun t : ℝ => riemannZeta ((σ:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : (σ:ℂ)+t*I≠1 := fun h => hσ (by simpa using congrArg Complex.re h)
  exact (differentiableAt_riemannZeta hs).continuousAt.comp (f:=fun t : ℝ => (σ:ℂ)+t*I) (by fun_prop)

private theorem local_second_moment {σ : ℝ} (hσ : 1/2<σ) (hσ' : σ<1) :
    ∃ C : ℝ,0<C ∧ ∀ {N : ℕ} {A B : ℝ},1≤N → 1≤A → (N:ℝ)/2≤A → A≤B → B≤2*N →
    |(∫ t in A..B,‖riemannZeta ((σ:ℂ)+t*I)‖^2)-(B-A)*(riemannZeta ((2*σ:ℝ):ℂ)).re|≤
      C*(N:ℝ)^(2-2*σ) := by
  obtain ⟨K,hK,Ha⟩ := strip_long_polynomial_bounds (by linarith : 0<σ) hσ'
  obtain ⟨D,hD,Hd⟩ := sum_nat_neg_rpow_strip_bound (p:=2*σ-1) (by linarith) (by linarith)
  let E := 1+1/(2*σ-1)
  have hden : 0<2*σ-1 := by linarith
  have hE : 0<E := by dsimp [E];positivity
  refine ⟨6*K^2+4*weightedHilbertConstant*D+2*E,by positivity [weightedHilbertConstant_pos],?_⟩
  intro N A B hN hA hNA hAB hBN
  let z := fun t : ℝ => riemannZeta ((σ:ℂ)+t*I)
  let p := fun t : ℝ => dirichletPoly (fun _ => 1) N ((σ:ℂ)+t*I)
  let d := ∑n∈Finset.Icc 1 N,(n:ℝ)^(-2*σ)
  let diagonal := (riemannZeta ((2*σ:ℝ):ℂ)).re
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hc : Continuous p := by
    dsimp only [p,dirichletPoly]
    apply continuous_finsetSum
    intro n hn
    rw [show (fun t : ℝ => (1:ℂ)*(n:ℂ)^(-((σ:ℂ)+t*I)))=(fun t : ℝ => Complex.exp (Complex.log (n:ℂ)*(-((σ:ℂ)+t*I)))) by
      funext t;rw [one_mul,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hn).1))] ]
    fun_prop
  have hz : Continuous z := continuous_vertical_zeta hσ'.ne
  have hpowers : (N:ℝ)^(1-2*σ)*N=(N:ℝ)^(2-2*σ) := by
    rw [←Real.rpow_add_one hp.ne'];congr 1;ring
  have hpt : ∀t∈uIoc A B, |‖z t‖^2-‖p t‖^2|≤3*K^2*(N:ℝ)^(1-2*σ) := by
    intro t ht
    rw [uIoc_of_le hAB] at ht
    obtain ⟨he,hp',hz'⟩ := Ha hN (hA.trans ht.1.le) (hNA.trans ht.1.le) (ht.2.trans hBN)
    change ‖z t-p t‖≤_ at he
    change ‖p t‖≤_ at hp'
    change ‖z t‖≤_ at hz'
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),mul_comm (‖z t‖+‖p t‖)]
    calc |‖z t‖-‖p t‖| *(‖z t‖+‖p t‖) ≤ (K*(N:ℝ)^(-σ))*(3*K*(N:ℝ)^(1-σ)) :=
           mul_le_mul ((abs_norm_sub_norm_le ..).trans he) (by linarith) (by positivity) (by positivity)
         _ = _ := by
           rw [show 1-2*σ= -σ+(1-σ) by ring,Real.rpow_add hp];ring
  have Herr := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t => ‖z t‖^2-‖p t‖^2)
    (a:=A) (b:=B) (fun t ht => by simpa only [Real.norm_eq_abs] using hpt t ht)
  rw [intervalIntegral.integral_sub (f:=fun t => ‖z t‖^2) (g:=fun t => ‖p t‖^2) ((hz.norm.pow 2).intervalIntegrable ..) ((hc.norm.pow 2).intervalIntegrable ..),
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hAB)] at Herr
  have He : |(∫t in A..B,‖z t‖^2)-(∫t in A..B,‖p t‖^2)|≤6*K^2*(N:ℝ)^(2-2*σ) := by
    apply Herr.trans
    rw [←hpowers]
    have hh := mul_le_mul_of_nonneg_left (show B-A≤2*N by linarith) (show 0≤3*K^2*(N:ℝ)^(1-2*σ) by positivity)
    linarith only [hh]
  have Hm := weighted_dirichletPoly_mean_square (fun _ => 1) N σ A B
  simp only [norm_one,one_pow,one_mul,mul_one] at Hm
  change |(∫t in A..B,‖p t‖^2)-(B-A)*d|≤_ at Hm
  have hd := Hd hN
  have hm (n : ℕ) (hn : n∈Finset.Icc 1 N) : (n:ℝ)*(n:ℝ)^(-2*σ)=(n:ℝ)^(-(2*σ-1)) := by
    have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
    rw [show -(2*σ-1)=1+(-2*σ) by ring,Real.rpow_add hn',Real.rpow_one]
  rw [sum_congr rfl hm] at Hm
  rw [show 1-(2*σ-1)=2-2*σ by ring] at hd
  have Hm' := Hm.trans (mul_le_mul_of_nonneg_left hd (by positivity [weightedHilbertConstant_pos]))
  have Ht := abs_zeta_diagonal_tail_le (p:=2*σ) (by linarith) hN
  rw [show -(2*σ)= -2*σ by ring] at Ht
  change |d-diagonal|≤E*(N:ℝ)^(1-2*σ) at Ht
  have htail : |(B-A)*d-(B-A)*diagonal|≤2*E*(N:ℝ)^(2-2*σ) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hAB),←hpowers]
    have hh := mul_le_mul (show B-A≤2*N by linarith) Ht (abs_nonneg _) (show 0≤2*(N:ℝ) by positivity)
    linarith only [hh]
  change |(∫t in A..B,‖z t‖^2)-(B-A)*diagonal|≤_
  linarith only [abs_sub_le (∫t in A..B,‖z t‖^2) (∫t in A..B,‖p t‖^2) ((B-A)*diagonal),
    abs_sub_le (∫t in A..B,‖p t‖^2) ((B-A)*d) ((B-A)*diagonal),He,Hm',htail]

/-- Effective mean-square asymptotic on the open strip to the right
of the critical line, with the convergent zeta diagonal as its coefficient. -/
theorem riemannZeta_right_strip_second_moment {σ : ℝ} (hσ : 1/2<σ) (hσ' : σ<1) :
    ∃ C : ℝ,0<C ∧ ∀ {T : ℝ},1≤T →
    |(∫t in (1:ℝ)..T,‖riemannZeta ((σ:ℂ)+t*I)‖^2)-(T-1)*(riemannZeta ((2*σ:ℝ):ℂ)).re|≤
      C*T^(2-2*σ) := by
  obtain ⟨C,hC,h⟩ := local_second_moment hσ hσ'
  let f := fun t : ℝ => ‖riemannZeta ((σ:ℂ)+t*I)‖^2
  let d := (riemannZeta ((2*σ:ℝ):ℂ)).re
  let F := fun T : ℝ => (∫t in (1:ℝ)..T,f t)-(T-1)*d
  have hfc : Continuous f := (continuous_vertical_zeta hσ'.ne).norm.pow 2
  have hk : 0<2-2*σ := by linarith
  have H {t u : ℝ} (ht : 1≤t) (htu : t≤u) (hu : u≤2*t) :
      |F u-F t|≤(C*2^(2-2*σ))*t^(2-2*σ) := by
    let N := ⌊t⌋₊+1
    have htN : t≤(N:ℝ) := by dsimp [N];push_cast;linarith [Nat.lt_floor_add_one t]
    have hNt : (N:ℝ)≤2*t := by dsimp [N];push_cast;linarith [Nat.floor_le (by linarith : 0≤t)]
    have he : F u-F t=(∫z in t..u,f z)-(u-t)*d := by
      dsimp only [F]
      rw [←intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable (μ:=volume) 1 t)
        (hfc.intervalIntegrable (μ:=volume) t u)]
      ring
    rw [he]
    apply (h (N:=N) (by dsimp [N];omega) ht (by linarith) htu (by linarith)).trans
    rw [mul_assoc,←Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by linarith : 0≤t)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hNt hk.le) hC.le
  obtain ⟨K,hK,h'⟩ := power_bound_of_dyadic_increments (F:=F) zero_lt_one hk
    (show 0≤C*2^(2-2*σ) by positivity) H
  exact ⟨K,hK,fun hT => by simpa [F,f,d] using h' hT⟩

end AnalyticNumberTheory.RiemannZeta
