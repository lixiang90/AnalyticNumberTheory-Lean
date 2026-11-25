import AnalyticNumberTheory.SieveMethods.RosserPrimeSpacing

/-!
# Estimating the branches of the Rosser sieve

The first-failure branches form a subfamily of all prime selections.
Exponential weighting bounds those with a prescribed number of selected
primes by a product involving only an admissible prime window.
-/
noncomputable section
open Finset Real
namespace AnalyticNumberTheory.SieveMethods
open Classical

/-- The complementary Euler factors after a first failure are precisely the
primes strictly smaller than the last selected prime. -/
theorem rosser_failure_tail {L : List ℕ} (hL : L.Pairwise (·>·)) (C : List ℕ → Prop) (b : Bool)
    {e : List ℕ × List ℕ} (he : e∈rosserFirstFailures L b C) :
    e.2=L.filter (fun p => p<e.1.getLastD 1) := by
  induction L generalizing C b e with
  | nil => simp [rosserFirstFailures] at he
  | cons p L ih =>
    rw [rosserFirstFailures,List.mem_append] at he
    rcases he with h | h
    · obtain ⟨h₁,_,hne,_,_,_⟩ := rosserFirstFailures_spec h
      have hm : e.1.getLastD 1∈e.1 := by cases he : e.1 with
        | nil => contradiction
        | cons a t => exact List.getLast_mem (by simp)
      have hlt := (List.pairwise_cons.mp hL).1 _ (h₁.subset hm)
      rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using not_lt.mpr hlt.le)]
      exact ih (List.pairwise_cons.mp hL).2 C b h
    split_ifs at h with hpass
    · obtain ⟨e',he',rfl⟩ := List.mem_map.mp h
      obtain ⟨h₁,_,hne,_,_,_⟩ := rosserFirstFailures_spec he'
      have hf := ih (List.pairwise_cons.mp hL).2 _ _ he'
      have hlast : (p::e'.1).getLastD 1=e'.1.getLastD 1 := by
        rw [List.getLastD_eq_getLast?,List.getLastD_eq_getLast?,List.getLast?_cons_of_ne_nil hne]
      have hm : e'.1.getLastD 1∈e'.1 := by cases he : e'.1 with
        | nil => contradiction
        | cons a t => exact List.getLast_mem (by simp)
      have hlt := (List.pairwise_cons.mp hL).1 _ (h₁.subset hm)
      change e'.2=(p::L).filter (fun q => q<(p::e'.1).getLastD 1)
      rw [hlast,List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using not_lt.mpr hlt.le)]
      exact hf
    · obtain rfl := List.mem_singleton.mp h
      simp only [List.getLastD_eq_getLast?,List.getLast?_singleton,Option.getD_some,
        List.filter_cons,lt_irrefl,decide_false]
      symm; exact List.filter_eq_self.mpr (fun a ha => by simpa using (List.pairwise_cons.mp hL).1 a ha)

/-- Sum any nonnegative function over all first-failure prefixes by majorizing
with its sum over all sublists. Multiplicities of list entries are respected. -/
theorem rosser_failure_sum_le_sublists (L : List ℕ) (C : List ℕ → Prop) (b : Bool)
    (F : List ℕ → ℝ) (hF : ∀ l,0≤F l) :
    ((rosserFirstFailures L b C).map (fun e => F e.1)).sum≤(L.sublists.map F).sum := by
  induction L generalizing C b F with
  | nil => simpa [rosserFirstFailures] using hF []
  | cons p L ih =>
    rw [rosserFirstFailures,List.map_append,List.sum_append,sum_sublists_cons]
    apply add_le_add (ih C b F hF)
    split_ifs with h
    · simpa only [List.map_map,Function.comp_def] using ih (fun l => C (p::l)) (!b)
        (fun l => F (p::l)) (fun l => hF _)
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      apply List.single_le_sum
      · intro a ha; obtain ⟨l,_,rfl⟩ := List.mem_map.mp ha; exact hF _
      · exact List.mem_map.mpr ⟨[],List.mem_sublists.mpr (List.nil_sublist L),rfl⟩

private theorem sum_sublists_product (L : List ℕ) (h : ℕ → ℝ) :
    (L.sublists.map (fun l => (l.map h).prod)).sum=(L.map (fun p => 1+h p)).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [sum_sublists_cons]; simp only [List.map_cons,List.prod_cons,List.sum_map_mul_left,ih]; ring

private theorem list_sum_map_le {ι : Type*} (l : List ι) (f g : ι → ℝ)
    (h : ∀ x∈l, f x≤g x) : (l.map f).sum≤(l.map g).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-- Rankin's bound for failure prefixes of length k all of whose selected
primes belong to a specified window. -/
theorem rosser_failure_rankin (L : List ℕ) (C : List ℕ → Prop) (b : Bool) (k : ℕ)
    (W : ℕ → Prop) (g : ℕ → ℝ) (hg : ∀ p,0≤g p) {a : ℝ} (ha : 0<a) :
    ((rosserFirstFailures L b C).map (fun e =>
      if e.1.length=k ∧ ∀p∈e.1,W p then (e.1.map g).prod else 0)).sum ≤
      (L.map (fun p => if W p then 1+a*g p else 1)).prod / a^k := by
  let h (p : ℕ) := if W p then a*g p else 0
  have hh (p : ℕ) : 0≤h p := by dsimp [h]; split_ifs; exact mul_nonneg ha.le (hg p); exact le_rfl
  have hprod (l : List ℕ) (hw : ∀p∈l,W p) : (l.map h).prod=a^l.length*(l.map g).prod := by
    induction l with
    | nil => simp
    | cons p t ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,h,ite_eq_left (hw p (by simp))]
      rw [ih (fun q hq => hw q (by simp [hq]))]; ring
  let F (l : List ℕ) : ℝ := if l.length=k ∧ ∀p∈l,W p then (l.map g).prod else 0
  have ht (l : List ℕ) : a^k*F l≤(l.map h).prod := by
    dsimp [F]; split_ifs with hW
    · rw [hprod l hW.2,hW.1]
    · rw [mul_zero]; apply List.prod_nonneg
      intro x hx; obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx; exact hh q
  rw [le_div_iff₀ (pow_pos ha k),mul_comm,←List.sum_map_mul_left]
  calc _ ≤ ((rosserFirstFailures L b C).map (fun e => (e.1.map h).prod)).sum := by
           apply list_sum_map_le
           intro e _; exact ht e.1
       _ ≤ _ := rosser_failure_sum_le_sublists L C b _ (fun l => List.prod_nonneg (by
           intro x hx; obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx; exact hh q))
       _ = _ := by rw [sum_sublists_product]; congr 1; apply List.map_congr_left
                   intro p hp; dsimp [h]; split_ifs <;> simp



/-- Reciprocal Euler product over a window of sifting primes. -/
def sieveWindowFactor (L : List ℕ) (W : ℕ → Prop) (g : ℕ → ℝ) : ℝ :=
  (L.map (fun p => if W p then (1-g p)⁻¹ else 1)).prod

/-- Contribution from first rejected prefixes with exactly k selected primes. -/
def rosserRemainderSlice (g : ℕ → ℝ) (C : List ℕ → Prop) (b : Bool) (L : List ℕ) (k : ℕ) : ℝ :=
  ((rosserFirstFailures L b C).map (fun e =>
    if e.1.length=k then (e.1.map g).prod*(e.2.map (fun p => 1-g p)).prod else 0)).sum

private theorem prod_map_mono (L : List ℕ) (f g : ℕ → ℝ) (h : ∀ p∈L,0≤f p ∧ f p≤g p) :
    (L.map f).prod≤(L.map g).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := h p (by simp)
    rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons]
    apply mul_le_mul hp.2 (ih (fun q hq => h q (by simp [hq]))) _ (hp.1.trans hp.2)
    apply List.prod_nonneg
    intro x hx; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx; exact (h q (by simp [hq])).1

private theorem masked_euler (L : List ℕ) (W : ℕ → Prop) (g : ℕ → ℝ) (hg : ∀p∈L,g p<1) :
    (L.map (fun p => if W p then 1 else 1-g p)).prod=
      (L.map (fun p => 1-g p)).prod*sieveWindowFactor L W g := by
  rw [sieveWindowFactor,←List.prod_map_mul]
  congr 1; apply List.map_congr_left; intro p hp
  by_cases h : W p <;> simp [h,(sub_pos.mpr (hg p hp)).ne']

private theorem masked_moment (L : List ℕ) (W : ℕ → Prop) (g : ℕ → ℝ)
    (hg : ∀p∈L,0≤g p ∧ g p<1) {a : ℝ} (ha : 0≤a) :
    (L.map (fun p => if W p then 1+a*g p else 1)).prod≤exp (a*log (sieveWindowFactor L W g)) := by
  induction L with
  | nil => simp [sieveWindowFactor]
  | cons p L ih =>
    have hp := hg p (by simp)
    have ht : ∀q∈L,0≤g q ∧ g q<1 := fun q hq => hg q (by simp [hq] : q∈p::L)
    have hZ : 0<sieveWindowFactor L W g := by
      apply List.prod_pos; intro x hx; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
      split_ifs <;> first | exact inv_pos.mpr (sub_pos.mpr (ht q hq).2) | exact zero_lt_one
    rw [List.map_cons,List.prod_cons]
    by_cases hw : W p
    · have h1 : 0<1-g p := sub_pos.mpr hp.2
      have hlog : g p≤log ((1-g p)⁻¹) := by rw [Real.log_inv]; linarith [Real.log_le_sub_one_of_pos h1]
      have he : 1+a*g p≤exp (a*log ((1-g p)⁻¹)) :=
        (by linarith [Real.add_one_le_exp (a*g p)] : _≤exp (a*g p)) |>.trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog ha))
      have hZ' : sieveWindowFactor (p::L) W g=(1-g p)⁻¹*sieveWindowFactor L W g := by simp [sieveWindowFactor,hw]
      rw [ite_eq_left hw,hZ',Real.log_mul (inv_ne_zero h1.ne') hZ.ne',mul_add,Real.exp_add]
      apply mul_le_mul he (ih ht) _ (Real.exp_pos _).le
      apply List.prod_nonneg; intro x hx; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
      split_ifs <;> first | exact add_nonneg zero_le_one (mul_nonneg ha (ht q hq).1) | exact zero_le_one
    · have hZ' : sieveWindowFactor (p::L) W g=sieveWindowFactor L W g := by simp [sieveWindowFactor,hw]
      simpa only [hw,ite_false,one_mul,hZ'] using ih ht

/-- The relative contribution of a fixed length k is bounded by a Rankin
moment on any upper window containing all the selected primes of that length. -/
theorem rosser_slice_window_bound (L : List ℕ) (hL : L.Pairwise (·>·)) (C : List ℕ → Prop) (b : Bool)
    (W : ℕ → Prop) (g : ℕ → ℝ) (hg₀ : ∀ p,0≤g p) (hg₁ : ∀ p∈L,g p<1)
    {k : ℕ} {a D : ℝ} (ha : 0<a) (hD : sieveWindowFactor L W g≤D)
    (hup : ∀ p∈L, ∀ q∈L, p≤q → W p → W q)
    (hwindow : ∀ e∈rosserFirstFailures L b C,e.1.length=k → ∀p∈e.1,W p) :
    rosserRemainderSlice g C b L k≤
      (L.map (fun p => 1-g p)).prod*D*exp (a*log D)/a^k := by
  let V := (L.map (fun p => 1-g p)).prod
  have hV : 0<V := by
    apply List.prod_pos; intro x hx; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact sub_pos.mpr (hg₁ p hp)
  have hZ : 0<sieveWindowFactor L W g := by
    apply List.prod_pos; intro x hx; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    split_ifs <;> first | exact inv_pos.mpr (sub_pos.mpr (hg₁ p hp)) | exact zero_lt_one
  let U (e : List ℕ × List ℕ) := if e.1.length=k ∧ ∀p∈e.1,W p then (e.1.map g).prod else 0
  have hterm (e : List ℕ × List ℕ) (he : e∈rosserFirstFailures L b C) (hsize : e.1.length=k) :
      (e.2.map (fun p => 1-g p)).prod ≤ V*D := by
    obtain ⟨hsub,_,hne,_,_,_⟩ := rosserFirstFailures_spec he
    have hm : e.1.getLastD 1∈e.1 := by cases hx : e.1 with
      | nil => contradiction
      | cons p t => exact List.getLast_mem (by simp)
    have hl := hwindow e he hsize _ hm
    rw [rosser_failure_tail hL C b he]
    have hmprod (l : List ℕ) : ((l.filter (fun p => p<e.1.getLastD 1)).map (fun p => 1-g p)).prod=
        (l.map (fun p => if p<e.1.getLastD 1 then 1-g p else 1)).prod := by
      induction l with
      | nil => simp
      | cons p l ih => by_cases h : p<e.1.getLastD 1 <;> simp only [List.filter_cons,decide_eq_true_eq,h,ite_true,ite_false,List.map_cons,List.prod_cons,ih,one_mul,Bool.false_eq_true,decide_true,decide_false]
    rw [hmprod]
    calc _ ≤ (L.map (fun p => if W p then 1 else 1-g p)).prod := by
            apply prod_map_mono; intro p hp
            by_cases hw : W p
            · by_cases hc : p<e.1.getLastD 1 <;> simp only [hw,hc,ite_true,ite_false,sub_nonneg,sub_le_self_iff,(hg₁ p hp).le,hg₀ p,zero_le_one,le_refl,and_self]
            · have hlt : p<e.1.getLastD 1 := lt_of_not_ge (fun h => hw (hup _ (hsub.subset hm) _ hp h hl))
              simp only [hw,hlt,ite_true,ite_false,sub_nonneg,(hg₁ p hp).le,le_refl,and_self]
         _ = _ := masked_euler L W g hg₁
         _ ≤ _ := mul_le_mul_of_nonneg_left hD hV.le
  have hs : rosserRemainderSlice g C b L k≤V*D*((rosserFirstFailures L b C).map U).sum := by
    rw [←List.sum_map_mul_left]
    apply list_sum_map_le
    intro e he
    by_cases h : e.1.length=k
    · have hall : ∀p∈e.1,W p := hwindow e he h
      simp only [h,U,hall,true_and,ite_true]
      rw [if_pos hall,mul_comm (V*D)]
      apply mul_le_mul_of_nonneg_left (hterm e he h)
      apply List.prod_nonneg; intro x hx; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx; exact hg₀ _
    · simp [U,h]
  have hbound := rosser_failure_rankin L C b k W g hg₀ ha
  have hmoment := (masked_moment L W g (fun p hp => ⟨hg₀ _,hg₁ _ hp⟩) ha.le).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.log_le_log hZ hD) ha.le))
  exact hs.trans ((mul_le_mul_of_nonneg_left (hbound.trans (div_le_div_of_nonneg_right hmoment (pow_pos ha _).le))
    (mul_nonneg hV.le (hZ.le.trans hD))).trans_eq (by ring))

end AnalyticNumberTheory.SieveMethods
