import AnalyticNumberTheory.SieveMethods.RosserRemainder

/-!
# Location of the first rejected prime in the beta sieve

Each pair of selected primes consumes only a fixed fraction of the
remaining logarithmic budget. Iteration bounds the last prime on every
rejected branch, even when earlier tests have nearly reached the level.
-/
noncomputable section
open Real Finset
namespace AnalyticNumberTheory.SieveMethods

private def logFactor (β : ℝ) (l : List ℕ) :=
  (l.map (fun p : ℕ => log p)).sum+β*log (l.getLastD 1)

private theorem logFactor_cons {l : List ℕ} (hl : l≠[]) (β : ℝ) (p : ℕ) :
    logFactor β (p::l)=log p+logFactor β l := by
  cases l with
  | nil => contradiction
  | cons q t => simp [logFactor]; ring

private theorem log_prod_list {l : List ℕ} (hp : ∀ p∈l, p.Prime) :
    log (l.prod:ℝ)=(l.map (fun p : ℕ => log p)).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    have hpr := hp p (by simp)
    have ht : ∀ q∈t,q.Prime := fun q hq => hp _ (by simp [hq])
    have hne := List.prod_ne_zero (fun he : 0∈t => (ht 0 he).ne_zero rfl)
    rw [List.prod_cons,Nat.cast_mul,Real.log_mul (by exact_mod_cast hpr.ne_zero) (by exact_mod_cast hne),
      List.map_cons,List.sum_cons,ih ht]

private theorem log_cut {β y : ℝ} (hy : 0<y) {l : List ℕ} (hl : l≠[]) (hp : ∀ p∈l,p.Prime) :
    rosserTruncationFactor β l<y ↔ logFactor β l<log y := by
  have hlm : l.getLastD 1∈l := by cases l with | nil => contradiction | cons p t => exact List.getLast_mem (by simp)
  have hn : (0:ℝ)<l.getLastD 1 := by exact_mod_cast (hp _ hlm).pos
  have hpr : (0:ℝ)<l.prod := by
    exact_mod_cast Nat.pos_of_ne_zero (List.prod_ne_zero (fun he : 0∈l => (hp 0 he).ne_zero rfl))
  unfold rosserTruncationFactor logFactor
  rw [←Real.log_lt_log_iff (mul_pos hpr (Real.rpow_pos_of_pos hn _)) hy,
    Real.log_mul hpr.ne' (Real.rpow_pos_of_pos hn _).ne',Real.log_rpow hn,log_prod_list hp]

private theorem upper_spacing {β : ℝ} (hb : 2≤β) (l : List ℕ) :
    ∀ {C : List ℕ → Prop} {Y : ℝ}, l≠[] → Odd l.length → l.Pairwise (·>·) → (∀ p∈l,p.Prime) →
      (∀ t : List ℕ, t≠[] → (∀ p∈t,p.Prime) → (C t ↔ logFactor β t<Y)) →
      rosserCondPlus C l.dropLast → ¬C l →
      Y*((β-1)/(β+1))^(l.length/2)≤(β+1)*log (l.getLastD 1) := by
  intro C Y hl hodd hdesc hp hC hpre hf
  have hratio : 0≤(β-1)/(β+1) := div_nonneg (by linarith) (by linarith)
  match l with
  | [] => contradiction
  | [p] =>
    have h := not_lt.mp (fun h => hf ((hC [p] hl hp).mpr h))
    simp [logFactor] at h ⊢
    linarith
  | [p,q] => norm_num [Nat.odd_iff] at hodd
  | p::q::a::t =>
    let W : ℝ := Y-log p-log q
    let D := fun l : List ℕ => C (p::q::l)
    have hsub : ∀ u, u≠[] → (∀ a∈u,a.Prime) → (D u ↔ logFactor β u<W) := by
      intro u hu hpr
      have hpu : ∀ x∈p::q::u,x.Prime := by
        intro x hx; simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact hp _ (by simp)
        · exact hp _ (by simp)
        · exact hpr _ hx
      rw [show D u=C (p::q::u) by rfl,hC _ (by simp) hpu,logFactor_cons (by simp) β p,logFactor_cons hu β q]
      dsimp [W]; constructor <;> intro h <;> linarith
    have hboth : C [p] ∧ rosserCondPlus D (a::t).dropLast := by
      simpa only [List.dropLast_cons_of_ne_nil (by simp : q::a::t≠[]),
        List.dropLast_cons_of_ne_nil (by simp : a::t≠[]),rosserCondPlus,rosserCondMinus,D] using hpre
    have hpfirst := (hC [p] (by simp) (by simpa using hp p (by simp))).mp hboth.1
    simp [logFactor] at hpfirst
    have hqp : log q≤log p := Real.log_le_log (by exact_mod_cast (hp q (by simp)).pos)
      (by exact_mod_cast (List.pairwise_cons.mp hdesc).1 q (by simp) |>.le)
    have hW : Y*((β-1)/(β+1))≤W := by
      rw [←mul_div_assoc,div_le_iff₀ (by linarith : 0<β+1)]; dsimp [W]
      nlinarith only [hpfirst.le,mul_le_mul_of_nonneg_left hqp (show 0≤β+1 by linarith)]
    have hlen : (p::q::a::t).length/2=(a::t).length/2+1 := by simp; omega
    have ih := upper_spacing hb (a::t) (C:=D) (Y:=W) (by simp) (by
      rw [Nat.odd_iff] at hodd ⊢; simp only [List.length_cons] at hodd ⊢; omega)
      (List.pairwise_cons.mp (List.pairwise_cons.mp hdesc).2).2
      (fun x hx => hp x (by simp [hx])) hsub hboth.2 hf
    rw [hlen,pow_succ,show Y*(((β-1)/(β+1))^((a::t).length/2)*((β-1)/(β+1)))=
       (Y*((β-1)/(β+1)))*((β-1)/(β+1))^((a::t).length/2) by ring]
    simpa only [List.getLastD_eq_getLast?,List.getLast?_cons_cons] using
      (mul_le_mul_of_nonneg_right hW (pow_nonneg hratio _)).trans ih
termination_by l.length



private theorem lower_spacing {β Y : ℝ} (hb : 2≤β) (hY : 0≤Y) (l : List ℕ)
    {C : List ℕ → Prop} (hl : l≠[]) (hpar : Even l.length) (hdesc : l.Pairwise (·>·))
    (hp : ∀ p∈l,p.Prime) (hsmall : ∀ p∈l,2*log p≤Y)
    (hC : ∀ t : List ℕ, t≠[] → (∀ p∈t,p.Prime) → (C t ↔ logFactor β t<Y))
    (hpre : rosserCondMinus C l.dropLast) (hf : ¬C l) :
    (Y/2)*((β-1)/(β+1))^(l.length/2)≤(β+1)*log (l.getLastD 1) := by
  match l with
  | [] => contradiction
  | [p] => norm_num [Nat.even_iff] at hpar
  | p::a::t =>
    let D := fun u : List ℕ => C (p::u)
    have hD : ∀ u, u≠[] → (∀ q∈u,q.Prime) → (D u ↔ logFactor β u<Y-log p) := by
      intro u hu hq
      have hpu : ∀ q∈p::u,q.Prime := by
        intro q h; rcases List.mem_cons.mp h with rfl | h
        · exact hp _ (by simp)
        · exact hq q h
      rw [show D u=C (p::u) by rfl,hC _ (by simp) hpu,logFactor_cons hu]
      constructor <;> intro h <;> linarith
    have hc : rosserCondPlus D (a::t).dropLast := by
      simpa only [List.dropLast_cons_of_ne_nil (by simp : a::t≠[]),rosserCondMinus,D] using hpre
    have h := upper_spacing hb (a::t) (C:=D) (Y:=Y-log p) (by simp)
      (by rw [Nat.odd_iff]; rw [Nat.even_iff] at hpar; simp only [List.length_cons] at hpar ⊢; omega)
      (List.pairwise_cons.mp hdesc).2 (fun q hq => hp q (by simp [hq])) hD hc hf
    have hr₀ : 0≤(β-1)/(β+1) := div_nonneg (by linarith) (by linarith)
    have hr₁ : (β-1)/(β+1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    have hpow : ((β-1)/(β+1))^((p::a::t).length/2)≤((β-1)/(β+1))^((a::t).length/2) :=
      pow_le_pow_of_le_one hr₀ hr₁ (by simp; omega)
    have hU : Y/2≤Y-log p := by linarith [hsmall p (by simp)]
    exact (mul_le_mul hU hpow (pow_nonneg hr₀ _) (by linarith)).trans (by simpa using h)

/-- A first rejected prefix of the beta sieve has its smallest selected
prime bounded away from one on a logarithmic scale. The condition on
the squares of the primes is the usual z≤√y range. -/
theorem betaSieve_failure_smallest_prime {L : List ℕ} {e : List ℕ × List ℕ} {b : Bool}
    {β y : ℝ} (hβ : 2≤β) (hy : 1≤y) (hdesc : L.Pairwise (·>·)) (hp : ∀ p∈L,p.Prime)
    (hlevel : ∀ p∈L,(p:ℝ)^2≤y)
    (he : e∈rosserFirstFailures L b (fun l => rosserTruncationFactor β l<y)) :
    (log y/2)*((β-1)/(β+1))^(e.1.length/2)≤(β+1)*log (e.1.getLastD 1) := by
  obtain ⟨h₁,_,hne,hf,hpre,hpar⟩ := rosserFirstFailures_spec he
  have hP : ∀ p∈e.1,p.Prime := fun p hp' => hp p (h₁.subset hp')
  have hY := Real.log_nonneg hy
  have hc := fun (l : List ℕ) (hl : l≠[]) (hpr : ∀ p∈l,p.Prime) => log_cut (β:=β) (by linarith : 0<y) hl hpr
  cases b with
  | false =>
    apply lower_spacing hβ hY _ hne hpar (hdesc.sublist h₁) hP _ hc hpre hf
    intro p hpl
    have hp₀ : (0:ℝ)<p := by exact_mod_cast (hP p hpl).pos
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (pow_pos hp₀ 2) (hlevel p (h₁.subset hpl))
  | true =>
    apply le_trans _ (upper_spacing hβ _ hne hpar (hdesc.sublist h₁) hP hc hpre hf)
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (div_nonneg (by linarith) (by linarith)) _)

end AnalyticNumberTheory.SieveMethods
