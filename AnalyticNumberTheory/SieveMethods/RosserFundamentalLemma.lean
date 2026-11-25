import AnalyticNumberTheory.SieveMethods.RosserFactorBounds

/-!
# The fundamental lemma for Rosser weights

For a finite list of sifting primes, the sieve dimension controls the
reciprocal Euler product on every terminal prime interval. At level
`z^u`, with truncation exponent `1+u/3`, the relative error of the
upper and lower main terms decays as `exp (−u log u / 2)`.
-/
noncomputable section
open Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The usual sieve dimension bound on the sifting primes in [w,z]. -/
def SieveDimensionBound (L : List ℕ) (z : ℝ) (g : ℕ → ℝ) (A κ : ℝ) : Prop :=
  ∀ w : ℝ, 2≤w → w≤z →
    sieveWindowFactor L (fun p => w≤p) g ≤ A*(log z/log w)^κ

private theorem window_of_dimension {L : List ℕ} {z A κ : ℝ} {g : ℕ → ℝ}
    (hz : 2≤z) (hA : 0≤A) (hκ : 0≤κ) (hp : ∀p∈L,p.Prime)
    (hd : SieveDimensionBound L z g A κ) {v : ℝ} (hv : 0≤v) :
    sieveWindowFactor L (fun p => log z*exp (-v)≤log p) g ≤ A*exp (κ*v) := by
  let t := log z*exp (-v)
  let w := max 2 (exp t)
  have hz' : 0<z := by linarith
  have hlog : 0<log z := Real.log_pos (by linarith)
  have ht : 0<t := mul_pos hlog (Real.exp_pos _)
  have ht' : t≤log z := mul_le_of_le_one_right hlog.le (Real.exp_le_one_iff.mpr (by linarith))
  have hw : w≤z := max_le hz ((Real.exp_le_exp.mpr ht').trans_eq (Real.exp_log hz'))
  have hw' : t≤log w := by
    rw [←Real.log_exp t]; exact Real.log_le_log (Real.exp_pos _) (le_max_right ..)
  have heq : sieveWindowFactor L (fun p => log z*exp (-v)≤log p) g =
      sieveWindowFactor L (fun p => w≤p) g := by
    unfold sieveWindowFactor
    congr 1; apply List.map_congr_left; intro p hpL
    have hple : (2:ℝ)≤p := by exact_mod_cast (hp p hpL).two_le
    have hpp : (0:ℝ)<p := by linarith
    have he : w≤p ↔ t≤log p := by
      rw [show w=max 2 (exp t) by rfl,max_le_iff,←Real.le_log_iff_exp_le hpp]
      exact and_iff_right hple
    change (if t≤log p then _ else _)=(if w≤p then _ else _)
    by_cases h : w≤p
    · rw [ite_eq_left (he.mp h),ite_eq_left h]
    · rw [ite_eq_right (fun h2 => h (he.mpr h2)),ite_eq_right h]
  have hr : log z/log w≤exp v := by
    apply (div_le_iff₀ (ht.trans_le hw')).mpr
    calc _ = exp v*t := by dsimp [t]; rw [Real.exp_neg]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left hw' (Real.exp_pos _).le
  rw [heq]
  apply (hd w (le_max_left ..) hw).trans
  apply mul_le_mul_of_nonneg_left _ hA
  rw [mul_comm κ v,Real.exp_mul]
  exact Real.rpow_le_rpow (div_nonneg hlog.le (ht.trans_le hw').le) hr hκ

private theorem spacing_ratio {u : ℝ} (hu : 12≤u) (k : ℕ) :
    exp (-(3*k/u)) ≤ (((1+u/3)-1)/((1+u/3)+1))^(k/2) := by
  have hu' : 0<u := by linarith
  have hd : 0<1+6/u := by positivity
  have hid : (((1+u/3)-1)/((1+u/3)+1))=(1+6/u)⁻¹ := by
    field_simp; ring
  have hlog : log (1+6/u)≤6/u := by linarith [Real.log_le_sub_one_of_pos hd]
  have hhalf : (k/2:ℕ)*2≤k := by omega
  have hhalf' : ((k/2:ℕ):ℝ)*2≤k := by exact_mod_cast hhalf
  rw [hid,←Real.exp_log (inv_pos.mpr hd),←Real.exp_nat_mul,Real.log_inv,Real.exp_le_exp]
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (k/2) : (0:ℝ)≤_)
  have hdiv : ((k/2:ℕ):ℝ)*(6/u)≤3*k/u := by
    rw [←mul_div_assoc,div_le_div_iff_of_pos_right hu']; linarith
  linarith

private theorem failure_window {L : List ℕ} {z u : ℝ} {b : Bool}
    (hz : 2≤z) (hu : 12≤u) (hL : L.Pairwise (·>·)) (hp : ∀p∈L,p.Prime)
    (hpz : ∀p∈L,(p:ℝ)≤z) {e : List ℕ × List ℕ}
    (he : e∈rosserFirstFailures L b (fun l => rosserTruncationFactor (1+u/3) l<z^u)) :
    7*u/12≤e.1.length ∧ ∀p∈e.1,log z*exp (-(3*e.1.length/u))≤log p := by
  have hz' : 1<z := by linarith
  have hβ : 2≤1+u/3 := by linarith
  have hsize := (Real.rpow_le_rpow_left_iff hz').mp (betaSieve_failure_length hz' (by linarith : 0≤1+u/3) hpz he)
  refine ⟨by linarith,?_⟩
  have hlevel (p : ℕ) (hpL : p∈L) : (p:ℝ)^2≤z^u := by
    calc (p:ℝ)^2 ≤ z^2 := by gcongr; exact hpz _ hpL
         _ = z^(2:ℝ) := by norm_num
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz'.le (by linarith)
  have hspace := betaSieve_failure_smallest_prime hβ (Real.one_le_rpow hz'.le (by linarith : 0≤u)) hL hp hlevel he
  rw [Real.log_rpow (by linarith : 0<z)] at hspace
  obtain ⟨hsub,_,hne,_,_,_⟩ := rosserFirstFailures_spec he
  have hh : ∀ (l : List ℕ) (hl : l≠[]), l.getLastD 1=l.getLast hl := by
    rintro (_|⟨p,t⟩) hl
    · contradiction
    · rfl
  have hlast := hh e.1 hne
  have hpm : (e.1.getLastD 1).Prime := by rw [hlast]; exact hp _ (hsub.subset (List.getLast_mem hne))
  have hnon : 0≤log (e.1.getLastD 1) := Real.log_nonneg (by exact_mod_cast hpm.one_le)
  have hm := (spacing_ratio hu e.1.length)
  have hs : u/2*(log z*exp (-(3*e.1.length/u))) ≤ u/2*log (e.1.getLastD 1) := calc
    _ ≤ (u*log z/2)*(((1+u/3)-1)/((1+u/3)+1))^(e.1.length/2) := by
          rw [show u/2*(log z*exp (-(3*e.1.length/u)))=(u*log z/2)*exp (-(3*e.1.length/u)) by ring]
          exact mul_le_mul_of_nonneg_left hm (by positivity [Real.log_pos hz'])
    _ ≤ _ := hspace.trans (mul_le_mul_of_nonneg_right (by linarith) hnon)
  intro p hpl
  have hrel : e.1.Pairwise (·≥·) := (hL.sublist hsub).imp (fun h => h.le)
  exact ((le_of_mul_le_mul_left hs (by linarith : 0<u/2))).trans (Real.log_le_log
    (by exact_mod_cast hpm.pos) (by rw [hlast]; exact_mod_cast hrel.rel_getLast hpl))


private theorem layer_decay {A κ u : ℝ} (hA : 1≤A) (hκ : 0≤κ) (hu : 12≤u)
    (hu' : 7*(log 2+2*log A+6*κ)≤log u) {k : ℕ} (hk : 7*u/12≤k) :
    let v := 3*(k:ℝ)/u
    let D := A*exp (κ*v)
    D*exp (u*log D)/u^k ≤ A*(1/2:ℝ)^k*exp (-(u/2)*log u) := by
  dsimp only
  have hA' : 0<A := by linarith
  have hu₀ : 0<u := by linarith
  have hk₀ : (0:ℝ)≤k := Nat.cast_nonneg _
  have hlogA := Real.log_nonneg hA
  have hlogu := Real.log_nonneg (show 1≤u by linarith)
  have hv : 3*(k:ℝ)/u≤3*k := div_le_self (by positivity) (by linarith)
  have hab : κ*(3*k/u)≤3*κ*k := by nlinarith only [mul_le_mul_of_nonneg_left hv hκ]
  have hau : u*log A≤2*k*log A := by gcongr; linarith
  have hku : u*(κ*(3*k/u))=3*κ*k := by field_simp
  have hr := mul_le_mul_of_nonneg_left hu' hk₀
  have hl := mul_le_mul_of_nonneg_right hk hlogu
  have hexp : κ*(3*k/u)+u*(log A+κ*(3*k/u))-k*log u ≤ -(k*log 2)+(-(u/2)*log u) := by
    nlinarith only [hab,hau,hku,hr,hl]
  have hup : u^k=exp ((k:ℝ)*log u) := by rw [Real.exp_nat_mul,Real.exp_log hu₀]
  have hhalf : (1/2:ℝ)^k=exp (-((k:ℝ)*log 2)) := by
    rw [show -((k:ℝ)*log 2)=(k:ℝ)*(-log 2) by ring, Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [Real.log_mul hA'.ne' (Real.exp_pos _).ne',Real.log_exp,hup,hhalf]
  rw [mul_assoc,←Real.exp_add,mul_div_assoc,←Real.exp_sub,mul_assoc,←Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hA'.le

private theorem sum_by_length {ι : Type*} (S : List ι) (f : ι → ℝ) (degree : ι → ℕ) (N : ℕ)
    (h : ∀x∈S,degree x<N) :
    (S.map f).sum=∑k∈range N,(S.map (fun x => if degree x=k then f x else 0)).sum := by
  induction S with
  | nil => simp
  | cons x S ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq,ite_eq_left (mem_range.mpr (h x (by simp))),
      ih (fun t ht => h t (by simp [ht]))]

/-- The large-parameter fundamental lemma on a finite descending prime list.
The threshold on u depends only on the two dimension constants. -/
theorem rosser_fundamental_lemma {A κ : ℝ} (hA : 1≤A) (hκ : 0≤κ) :
    ∃ u₀ : ℝ, ∀ {u z : ℝ}, u₀≤u → 2≤z → ∀ (L : List ℕ) (g : ℕ → ℝ) (b : Bool),
      L.Pairwise (·>·) → (∀p∈L,p.Prime) → (∀p∈L,(p:ℝ)≤z) →
      (∀p,0≤g p) → (∀p∈L,g p<1) → SieveDimensionBound L z g A κ →
      rosserRemainder g (fun l => rosserTruncationFactor (1+u/3) l<z^u) b L ≤
        2*A*(L.map (fun p => 1-g p)).prod*exp (-(u/2)*log u) := by
  refine ⟨max 12 (exp (7*(log 2+2*log A+6*κ))),?_⟩
  intro u z hu hz L g b hL hp hpz hg hg₁ hd
  have hu₁ := (max_le_iff.mp hu).1
  have hu₀ : 0<u := by linarith
  have hu₂ := (Real.le_log_iff_exp_le hu₀).mpr (max_le_iff.mp hu).2
  let C := fun l => rosserTruncationFactor (1+u/3) l<z^u
  let V := (L.map (fun p => 1-g p)).prod
  let E := exp (-(u/2)*log u)
  have hV : 0≤V := List.prod_nonneg (by
    intro x hx; obtain ⟨p,hpL,rfl⟩ := List.mem_map.mp hx; exact (sub_pos.mpr (hg₁ p hpL)).le)
  have hAE : 0≤A*E := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hlayer (k : ℕ) : rosserRemainderSlice g C b L k≤(V*(A*E))*(1/2:ℝ)^k := by
    by_cases hex : ∃e∈rosserFirstFailures L b C,e.1.length=k
    · obtain ⟨e,he,heq⟩ := hex
      have hk := (failure_window hz hu₁ hL hp hpz he).1
      rw [heq] at hk
      let v := 3*(k:ℝ)/u
      let W := fun p : ℕ => log z*exp (-v)≤log p
      have hD := window_of_dimension hz (by linarith : 0≤A) hκ hp hd (show 0≤v by dsimp [v]; positivity)
      have hw (e' : List ℕ × List ℕ) (he' : e'∈rosserFirstFailures L b C) (hlen : e'.1.length=k) :
          ∀p∈e'.1,W p := by simpa only [W,v,hlen] using (failure_window hz hu₁ hL hp hpz he').2
      have hbound := rosser_slice_window_bound L hL C b W g hg hg₁ hu₀ hD (fun p hpL q _ hpq hw =>
        hw.trans (Real.log_le_log (by exact_mod_cast (hp p hpL).pos) (by exact_mod_cast hpq))) hw
      apply hbound.trans
      have hnum := mul_le_mul_of_nonneg_left (layer_decay hA hκ hu₁ hu₂ hk) hV
      dsimp [V,E,v] at hnum ⊢
      simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hnum
    · have hzslice : rosserRemainderSlice g C b L k=0 := by
        unfold rosserRemainderSlice
        apply List.sum_eq_zero
        intro x hx; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
        exact ite_eq_right (fun h => hex ⟨e,he,h⟩)
      rw [hzslice]; exact mul_nonneg (mul_nonneg hV hAE) (by positivity)
  let N := L.length+1
  have hsum : rosserRemainder g C b L=∑k∈range N,rosserRemainderSlice g C b L k :=
    sum_by_length (rosserFirstFailures L b C) _ (fun e => e.1.length) N
      (fun e he => Nat.lt_succ_of_le (rosserFirstFailures_spec he).1.length_le)
  have hgeom : ∑k∈range N,(1/2:ℝ)^k ≤ 2 := by
    have hh := geom_sum_mul (1/2:ℝ) N
    linarith only [hh,pow_nonneg (by norm_num : (0:ℝ)≤1/2) N]
  change rosserRemainder g C b L≤2*A*V*E
  rw [hsum]
  calc _ ≤ ∑k∈range N,(V*(A*E))*(1/2:ℝ)^k := Finset.sum_le_sum (fun k _ => hlayer k)
       _ = (V*(A*E))*∑k∈range N,(1/2:ℝ)^k := by rw [Finset.mul_sum]
       _ ≤ _ := (mul_le_mul_of_nonneg_left hgeom (mul_nonneg hV hAE)).trans_eq (by ring)

end AnalyticNumberTheory.SieveMethods
