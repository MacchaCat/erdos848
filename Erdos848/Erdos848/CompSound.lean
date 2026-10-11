import Erdos848.CheckSound
import ErdosComp

/-!
# Soundness of the computational part

1. `sqfTest_sound`: `sqfTest n = true → Squarefree n`.
2. `buildMarks_sound`: unmarked `w` have `w² + 1` squarefree.
3. `runFrom_sound`: a successful guarded colouring run proves `Statement N`.
-/

namespace Erdos848

open Finset ErdosComp

/-! ### 1. The squarefreeness test -/

lemma isSq_iff (m : ℕ) : isSq m = true ↔ ∃ k, k * k = m := by
  unfold isSq
  simp only [beq_iff_eq]
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨k, rfl⟩; rw [Nat.sqrt_eq]

/-- A number all of whose prime factors are `≥ P` and which is `< P³` is squarefree unless it is
a perfect square `> 1`. -/
lemma sqf_of_big_factors {rem P : ℕ} (hrem : 0 < rem) (hlt : rem < P * P * P)
    (hP : ∀ q, q.Prime → q ∣ rem → P ≤ q) (hsq : ¬ (1 < rem ∧ ∃ k, k * k = rem)) :
    Squarefree rem := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hqP := hP q hq ⟨q * m, by rw [hm]; ring⟩
  by_cases hm1 : m = 1
  · subst hm1
    apply hsq
    refine ⟨?_, q, by rw [hm]; ring⟩
    have := hq.two_le; nlinarith
  · obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have hrP := hP r hr (Dvd.dvd.mul_left hrm _ |>.trans (by rw [hm]))
    have hrle : r ≤ m := Nat.le_of_dvd hm0 hrm
    have : P * P * P ≤ q * q * m := by
      have h1 : P * P ≤ q * q := Nat.mul_le_mul hqP hqP
      exact Nat.mul_le_mul h1 (hrP.trans hrle)
    omega

lemma plist_mem {p : ℕ} : p ∈ plist ↔ p ≤ DTr ∧ p.Prime := by
  unfold plist
  rw [List.mem_filter, List.mem_range, isPrimeB_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma plist_sorted : plist.Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem sqfGo_sound (n : ℕ) : ∀ (ps : List ℕ) (rem s L : ℕ),
    n = rem * s → Squarefree s → (∀ q, q.Prime → q ∣ s → q < L) →
    (∀ q, q.Prime → q < L → ¬ q ∣ rem) → 0 < rem →
    ps.Pairwise (· < ·) → (∀ p ∈ ps, p.Prime ∧ L ≤ p ∧ p ≤ DTr) →
    (∀ q, q.Prime → L ≤ q → q ≤ DTr → q ∈ ps) → n ≤ DTr * DTr * DTr →
    sqfGo n rem ps = true → Squarefree n := by
  intro ps
  induction ps with
  | nil =>
    intro rem s L hn hs hsL hremL hrem _ _ hcomp hD h
    simp only [sqfGo, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    have hfac : ∀ q, q.Prime → q ∣ rem → DTr + 1 ≤ q := by
      intro q hq hd
      by_contra hc; push Not at hc
      by_cases hqL : q < L
      · exact hremL q hq hqL hd
      · exact absurd (hcomp q hq (by omega) (by omega)) (by simp)
    have hremle : rem ≤ n := by rw [hn]; exact Nat.le_mul_of_pos_right _ (by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0; exact absurd hs (by simp)
      · exact h0)
    have hsq : Squarefree rem := by
      apply sqf_of_big_factors hrem (P := DTr + 1) _ hfac
      · rintro ⟨h1, k, hk⟩
        rcases h with h | h
        · omega
        · rw [← hk] at h; exact absurd ((isSq_iff _).mpr ⟨k, rfl⟩) (by simp [h])
      · have : DTr * DTr * DTr < (DTr + 1) * (DTr + 1) * (DTr + 1) := by unfold DTr; norm_num
        omega
    rw [hn, Nat.squarefree_mul_iff]
    refine ⟨?_, hsq, hs⟩
    rw [Nat.coprime_comm, Nat.Coprime]
    by_contra hg
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hg
    have h1 := hsL q hq (hqd.trans (Nat.gcd_dvd_left _ _))
    exact hremL q hq h1 (hqd.trans (Nat.gcd_dvd_right _ _))
  | cons p ps ih =>
    intro rem s L hn hs hsL hremL hrem hsort hps hcomp hD h
    have hp := (hps p (List.mem_cons_self ..)).1
    have hpL := (hps p (List.mem_cons_self ..)).2.1
    have hpD := (hps p (List.mem_cons_self ..)).2.2
    have hsort' := List.pairwise_cons.mp hsort
    -- no prime strictly between L and p
    have hgap : ∀ q, q.Prime → q < p → ¬ q ∣ rem := by
      intro q hq hqp hd
      by_cases hqL : q < L
      · exact hremL q hq hqL hd
      · have := hcomp q hq (by omega) (by omega)
        rcases List.mem_cons.mp this with rfl | hmem
        · omega
        · exact absurd (hsort'.1 q hmem) (by omega)
    have hrw : sqfGo n rem (p :: ps) = if n < p * p * p then !(1 < rem && isSq rem)
        else if rem % p == 0 then (if rem / p % p == 0 then false else sqfGo n (rem / p) ps)
        else sqfGo n rem ps := rfl
    rw [hrw] at h
    have hremle : rem ≤ n := by
      rw [hn]; exact Nat.le_mul_of_pos_right _ (by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · subst h0; exact absurd hs (by simp)
        · exact h0)
    have hcop_fin : ∀ r', Squarefree r' → (∀ q, q.Prime → q ∣ r' → ¬ q ∣ s) →
        n = r' * s → Squarefree n := by
      intro r' hr' hco hn'
      rw [hn', Nat.squarefree_mul_iff]
      refine ⟨?_, hr', hs⟩
      rw [Nat.Coprime]
      by_contra hg
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hg
      exact hco q hq (hqd.trans (Nat.gcd_dvd_left _ _)) (hqd.trans (Nat.gcd_dvd_right _ _))
    by_cases h1 : n < p * p * p
    · simp only [h1, ↓reduceIte, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at h
      have hsq : Squarefree rem := by
        apply sqf_of_big_factors hrem (P := p) (by omega)
        · intro q hq hd; by_contra hc; push Not at hc; exact hgap q hq hc hd
        · rintro ⟨h1', k, hk⟩
          rcases h with h | h
          · omega
          · rw [← hk] at h; exact absurd ((isSq_iff _).mpr ⟨k, rfl⟩) (by simp [h])
      exact hcop_fin rem hsq (fun q hq hd hds => hremL q hq (hsL q hq hds) hd) hn
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : rem % p = 0
      · have hdvd : p ∣ rem := Nat.dvd_of_mod_eq_zero h2
        by_cases h3 : rem / p % p = 0
        · simp [h2, h3] at h
        · simp only [h2, h3, beq_self_eq_true, ↓reduceIte, beq_iff_eq] at h
          have hnd : ¬ p ∣ rem / p := fun hd => h3 (Nat.mod_eq_zero_of_dvd hd)
          obtain ⟨k, hk⟩ := hdvd
          have hkdiv : rem / p = k := by rw [hk, Nat.mul_div_cancel_left _ hp.pos]
          rw [hkdiv] at h hnd
          apply ih k (s * p) (p + 1)
          · rw [hn, hk]; ring
          · rw [Nat.squarefree_mul_iff]
            refine ⟨?_, hs, hp.squarefree⟩
            rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
            intro hps'
            have := hsL p hp hps'
            omega
          · intro q hq hd
            rcases (Nat.Prime.dvd_mul hq).mp hd with hd | hd
            · have := hsL q hq hd; omega
            · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hd; omega
          · intro q hq hqp hd
            rcases Nat.lt_or_ge q p with hlt | hge
            · exact hgap q hq hlt (hd.trans ⟨p, by rw [hk]; ring⟩)
            · have : q = p := by omega
              subst this; exact hnd hd
          · rcases Nat.eq_zero_or_pos k with h0 | h0
            · subst h0; simp at hk; omega
            · exact h0
          · exact hsort'.2
          · intro x hx
            exact ⟨(hps x (List.mem_cons_of_mem _ hx)).1, hsort'.1 x hx,
              (hps x (List.mem_cons_of_mem _ hx)).2.2⟩
          · intro q hq hqL hqD
            rcases List.mem_cons.mp (hcomp q hq (by omega) hqD) with rfl | hmem
            · omega
            · exact hmem
          · exact hD
          · exact h
      · simp only [h2, beq_iff_eq, ↓reduceIte] at h
        apply ih rem s (p + 1) hn hs (fun q hq hd => by have := hsL q hq hd; omega)
        · intro q hq hqp hd
          rcases Nat.lt_or_ge q p with hlt | hge
          · exact hgap q hq hlt hd
          · have : q = p := by omega
            subst this; exact h2 (Nat.mod_eq_zero_of_dvd hd)
        · exact hrem
        · exact hsort'.2
        · intro x hx
          exact ⟨(hps x (List.mem_cons_of_mem _ hx)).1, hsort'.1 x hx,
            (hps x (List.mem_cons_of_mem _ hx)).2.2⟩
        · intro q hq hqL hqD
          rcases List.mem_cons.mp (hcomp q hq (by omega) hqD) with rfl | hmem
          · omega
          · exact hmem
        · exact hD
        · exact h

theorem sqfTest_sound {n : ℕ} (h : sqfTest n = true) : Squarefree n := by
  unfold sqfTest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpos, hD⟩, hgo⟩ := h
  exact sqfGo_sound n plist n 1 0 (by ring) squarefree_one (fun q hq hd => absurd
    (Nat.le_of_dvd one_pos hd) (by have := hq.two_le; omega)) (fun q _ h => absurd h (by omega))
    hpos plist_sorted (fun p hp => ⟨(plist_mem.mp hp).2, Nat.zero_le _, (plist_mem.mp hp).1⟩)
    (fun q hq _ hqD => plist_mem.mpr ⟨hqD, hq⟩) hD hgo

/-! ### 2. The marks -/

lemma getD_set_true (a : Array Bool) (w i : ℕ) :
    (a.set! w true).getD i true = (a.getD i true || decide (i = w)) := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : i = w
  · subst h; by_cases hs : i < a.size <;> simp [hs]
  · simp [Ne.symm h, h]

lemma markProg_mono (X m : ℕ) : ∀ f w (a : Array Bool) i, a.getD i true = true →
    (markProg X m f w a).getD i true = true := by
  intro f
  induction f with
  | zero => intro w a i h; exact h
  | succ f ih =>
    intro w a i h
    simp only [markProg]
    split_ifs
    · exact h
    · apply ih; rw [getD_set_true, h]; rfl

lemma markProg_marks (X m : ℕ) : ∀ f w (a : Array Bool) j, j < f → w + j * m ≤ X →
    (markProg X m f w a).getD (w + j * m) true = true := by
  intro f
  induction f with
  | zero => intro w a j hj; omega
  | succ f ih =>
    intro w a j hj hX
    simp only [markProg]
    split_ifs with h
    · exfalso; have : w ≤ w + j * m := Nat.le_add_right _ _; omega
    · rcases j with _ | j
      · apply markProg_mono; simp [getD_set_true]
      · have := ih (w + m) (a.set! w true) j (by omega) (by
          have : w + m + j * m = w + (j + 1) * m := by ring
          omega)
        have e : w + m + j * m = w + (j + 1) * m := by ring
        rw [e] at this; exact this

lemma sqRoots_eq {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r < p * p)
    (hdvd : p * p ∣ r * r + 1) : ∀ x ∈ sqRoots p, x = r ∨ x = p * p - r := by
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      have := Nat.le_of_dvd one_pos (by simpa using hdvd)
      have := hp.two_le; nlinarith
    · exact h
  have hr1 : r ∈ sqRoots p := by simp [sqRoots, mem_filter, hr, hdvd]
  have hr2 : p * p - r ∈ sqRoots p := by
    simp only [sqRoots, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ (p * p)).mp
    have e := (ZMod.natCast_eq_zero_iff _ (p * p)).mpr hdvd
    push_cast [Nat.cast_sub hr.le] at e ⊢
    rw [show ((p : ZMod (p * p)) * p) = ((p * p : ℕ) : ZMod (p * p)) by push_cast; ring,
      ZMod.natCast_self]
    linear_combination e
  have hne : r ≠ p * p - r := by
    intro h
    have h2 : 2 ∣ p * p := ⟨r, by omega⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3 <;>
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h3).symm
  intro x hx
  by_contra hc
  push Not at hc
  have hsub : ({x, r, p * p - r} : Finset ℕ) ⊆ sqRoots p := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hcard : ({x, r, p * p - r} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem (by simp [hc.1, hc.2]), card_insert_of_notMem (by simp [hne]),
      card_singleton]
  have := card_le_card hsub
  have := card_sqRoots_le hp hp2
  omega

lemma markLoop_step {X : ℕ} {cert : ℕ → ℕ × ℕ} {k p : ℕ} {a b : Array Bool}
    (h : markLoop X cert (k + 1) p a = some b) :
    ∃ a', markLoop X cert k (p + 4) a' = some b ∧
      (∀ i, a.getD i true = true → a'.getD i true = true) ∧
      (p.Prime → ∀ w ≤ X, p * p ∣ w * w + 1 → a'.getD w true = true) := by
  simp only [markLoop] at h
  by_cases h1 : (cert p).1 = 0
  · simp only [h1, beq_self_eq_true, ↓reduceIte] at h
    by_cases h2 : (cert p).2 < p * p ∧ ((cert p).2 * (cert p).2 + 1) % (p * p) = 0
    · have h2' : ((cert p).2 < p * p && ((cert p).2 * (cert p).2 + 1) % (p * p) == 0) = true := by
        simp [h2]
      simp only [h2', ↓reduceIte] at h
      refine ⟨_, h, fun i hi => markProg_mono _ _ _ _ _ _ (markProg_mono _ _ _ _ _ _ hi), ?_⟩
      intro hq w hw hd
      obtain ⟨hr, hroot⟩ := h2
      have hroot' : p * p ∣ (cert p).2 * (cert p).2 + 1 := Nat.dvd_of_mod_eq_zero hroot
      have hp2 : p ≠ 2 := by
        have := prime_mod_four_of_sq_dvd hq hd; omega
      have hmem : w % (p * p) ∈ sqRoots p := (mod_mem_sqRoots hq.pos w).mpr hd
      have hw' : w % (p * p) + w / (p * p) * (p * p) = w := by
        rw [Nat.mul_comm (w / (p * p))]; exact Nat.mod_add_div w (p * p)
      have hj : w / (p * p) < X / (p * p) + 2 := by
        have := Nat.div_le_div_right (c := p * p) hw; omega
      rcases sqRoots_eq hq hp2 hr hroot' _ hmem with he | he
      · apply markProg_mono
        have key : (cert p).2 + w / (p * p) * (p * p) = w := by rw [← he]; exact hw'
        have := markProg_marks X (p * p) (X / (p * p) + 2) (cert p).2 a (w / (p * p)) hj
          (by rw [key]; exact hw)
        rwa [key] at this
      · have key : p * p - (cert p).2 + w / (p * p) * (p * p) = w := by rw [← he]; exact hw'
        have := markProg_marks X (p * p) (X / (p * p) + 2) (p * p - (cert p).2)
          (markProg X (p * p) (X / (p * p) + 2) (cert p).2 a) (w / (p * p)) hj
          (by rw [key]; exact hw)
        rwa [key] at this
    · have h2' : ((cert p).2 < p * p && ((cert p).2 * (cert p).2 + 1) % (p * p) == 0) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
        tauto
      simp [h2'] at h
  · have h1' : ((cert p).1 == 0) = false := by simp [h1]
    simp only [h1', Bool.false_eq_true, ↓reduceIte] at h
    by_cases h3 : (cert p).1 = 1 ∧ 1 < (cert p).2 ∧ (cert p).2 < p ∧ p % (cert p).2 = 0
    · have h3' : ((cert p).1 == 1 && decide (1 < (cert p).2) && decide ((cert p).2 < p) &&
          p % (cert p).2 == 0) = true := by simp [h3]
      simp only [h3', ↓reduceIte] at h
      refine ⟨a, h, fun i hi => hi, fun hq => ?_⟩
      have := hq.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h3.2.2.2)
      omega
    · have h3' : ((cert p).1 == 1 && decide (1 < (cert p).2) && decide ((cert p).2 < p) &&
          p % (cert p).2 == 0) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
        tauto
      simp [h3'] at h

lemma markLoop_mono (X : ℕ) (cert : ℕ → ℕ × ℕ) : ∀ k p (a b : Array Bool),
    markLoop X cert k p a = some b → ∀ i, a.getD i true = true → b.getD i true = true := by
  intro k
  induction k with
  | zero => intro p a b h i hi; simp [markLoop] at h; subst h; exact hi
  | succ k ih =>
    intro p a b h i hi
    obtain ⟨a', h', hm, -⟩ := markLoop_step h
    exact ih _ _ _ h' i (hm i hi)

lemma markLoop_cover (X : ℕ) (cert : ℕ → ℕ × ℕ) : ∀ k p (a b : Array Bool),
    markLoop X cert k p a = some b → ∀ j < k, (p + 4 * j).Prime →
      ∀ w ≤ X, (p + 4 * j) * (p + 4 * j) ∣ w * w + 1 → b.getD w true = true := by
  intro k
  induction k with
  | zero => intro p a b _ j hj; omega
  | succ k ih =>
    intro p a b h j hj hq w hw hd
    obtain ⟨a', h', hm, hc⟩ := markLoop_step h
    rcases j with _ | j
    · simp only [mul_zero, add_zero] at hq hd
      exact markLoop_mono X cert k (p + 4) a' b h' w (hc hq w hw hd)
    · exact ih (p + 4) a' b h' j (by omega) (by rwa [show p + 4 + 4 * j = p + 4 * (j + 1) by ring])
        w hw (by rwa [show p + 4 + 4 * j = p + 4 * (j + 1) by ring])

theorem buildMarks_sound {X : ℕ} {cert : ℕ → ℕ × ℕ} {marks : Array Bool}
    (h : buildMarks X cert = some marks) {w : ℕ} (hw1 : 1 ≤ w) (hwX : w ≤ X)
    (hm : marks.getD w true = false) : Squarefree (w * w + 1) := by
  by_contra hsq
  obtain ⟨q, hq, hd⟩ := exists_prime_sq_dvd hsq
  have h4 := prime_mod_four_of_sq_dvd hq hd
  have hq5 : 5 ≤ q := by
    have := hq.two_le; omega
  have hqw : q ≤ w := by
    by_contra hc; push Not at hc
    have : (w + 1) * (w + 1) ≤ q * q := Nat.mul_le_mul hc hc
    have := Nat.le_of_dvd (by omega) hd
    nlinarith
  have hj : q = 5 + 4 * ((q - 5) / 4) := by omega
  have := markLoop_cover X cert (X / 4 + 1) 5 _ marks h ((q - 5) / 4) (by omega)
    (by rw [← hj]; exact hq) w hwX (by rw [← hj]; exact hd)
  rw [hm] at this; exact absurd this (by simp)

/-! ### 3. The guarded colouring -/

/-- Same-class members are compatible. -/
def Proper (cls : Array (Array ℕ)) : Prop :=
  ∀ c (hc : c < cls.size), ∀ u ∈ cls[c], ∀ v ∈ cls[c], u ≠ v → Squarefree (u * v + 1)

/-- `x` lies in some class. -/
def InCls (cls : Array (Array ℕ)) (x : ℕ) : Prop := ∃ c, ∃ hc : c < cls.size, x ∈ cls[c]

/-- The invariant after step `N`. -/
def ClsOk (N : ℕ) (cls : Array (Array ℕ)) : Prop :=
  Proper cls ∧ (∀ v, 1 ≤ v → v ≤ N → ¬ Squarefree (v * v + 1) → InCls cls v) ∧ cls.size ≤ c7 N

theorem statement_of_clsOk {N : ℕ} {cls : Array (Array ℕ)} (h : ClsOk N cls) : Statement N := by
  classical
  obtain ⟨hP, hC, hS⟩ := h
  intro A hsub hA
  have hin : ∀ a ∈ A, InCls cls a := fun a ha => by
    have := Finset.mem_Icc.mp (hsub ha)
    exact hC a this.1 this.2 (hA a ha a ha)
  let f : ℕ → ℕ := fun a => if h : InCls cls a then Classical.choose h else 0
  have hf : ∀ a ∈ A, ∃ hc : f a < cls.size, a ∈ cls[f a] := by
    intro a ha
    have h := hin a ha
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  calc A.card ≤ cls.size := by
        apply card_le_of_coloring f hA (fun a ha => (hf a ha).1)
        intro a ha b hb hne hfab
        obtain ⟨hca, hma⟩ := hf a ha
        obtain ⟨hcb, hmb⟩ := hf b hb
        have hmb' : b ∈ cls[f a] := by simp only [hfab]; exact hmb
        exact hP (f a) hca a hma b hmb' hne
    _ ≤ c7 N := hS

lemma compatB_sound {v : ℕ} {arr : Array ℕ} (h : compatB v arr = true) :
    ∀ u ∈ arr, u ≠ v → Squarefree (u * v + 1) := by
  intro u hu hne
  unfold compatB at h
  have := (Array.all_eq_true_iff_forall_mem.mp h) u hu
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h1
  · exact absurd h1 hne
  · exact sqfTest_sound h1

lemma c7C_eq (N : ℕ) : c7C N = c7 N := rfl

theorem applyOp_ok {N : ℕ} {cls cls' : Array (Array ℕ)} {op : Op}
    (h : applyOp N cls op = some cls') (hP : Proper cls) :
    Proper cls' ∧ (∀ x, InCls cls x → InCls cls' x) ∧ (cls.size ≤ c7 N → cls'.size ≤ c7 N) := by
  cases op with
  | opn v =>
    simp only [applyOp] at h
    split_ifs at h with hs
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_, fun _ => by rw [Array.size_push]; rw [c7C_eq] at hs; exact hs⟩
    · intro c hc u hu w hw hne
      rw [Array.getElem_push] at hu hw
      split_ifs at hu hw with hlt
      · exact hP c hlt u hu w hw hne
      · rw [Array.mem_singleton] at hu hw; exact absurd (hu.trans hw.symm) hne
    · rintro x ⟨c, hc, hx⟩
      exact ⟨c, by rw [Array.size_push]; omega, by rw [Array.getElem_push, dif_pos hc]; exact hx⟩
  | place v c =>
    simp only [applyOp] at h
    split_ifs at h with hc hcomp
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_, fun hs => by rw [Array.size_modify]; exact hs⟩
    · intro c' hc' u hu w hw hne
      rw [Array.getElem_modify] at hu hw
      rw [Array.size_modify] at hc'
      split_ifs at hu hw with hcc
      · subst hcc
        rw [Array.mem_push] at hu hw
        have hcs := compatB_sound hcomp
        rcases hu with hu | rfl <;> rcases hw with hw | rfl
        · exact hP c hc' u hu w hw hne
        · exact hcs u hu hne
        · rw [mul_comm]; exact hcs w hw (Ne.symm hne)
        · exact absurd rfl hne
      · exact hP c' hc' u hu w hw hne
    · rintro x ⟨c', hc', hx⟩
      refine ⟨c', by rw [Array.size_modify]; exact hc', ?_⟩
      rw [Array.getElem_modify]
      split_ifs with hcc
      · subst hcc; exact Array.mem_push_of_mem _ hx
      · exact hx
  | move u c₁ c₂ =>
    simp only [applyOp] at h
    split_ifs at h with h₁ h₂ hcond
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
    obtain ⟨⟨hne12, hcont⟩, hcomp⟩ := hcond
    have hcs := compatB_sound hcomp
    have hu1 : u ∈ cls[c₁] := Array.contains_iff_mem.mp hcont
    -- membership in the new classes
    have hmem : ∀ c (hc : c < cls.size) x,
        x ∈ ((cls.modify c₁ (·.erase u)).modify c₂ (·.push u))[c]'(by simpa using hc) ↔
          (c = c₂ ∧ (x ∈ cls[c] ∨ x = u)) ∨ (c = c₁ ∧ x ∈ cls[c].erase u) ∨
          (c ≠ c₁ ∧ c ≠ c₂ ∧ x ∈ cls[c]) := by
      intro c hc x
      by_cases h2c : c₂ = c
      · subst h2c
        simp [Array.getElem_modify, Ne.symm hne12, hne12]
      · by_cases h1c : c₁ = c
        · subst h1c
          simp [Array.getElem_modify, h2c, Ne.symm h2c]
        · simp [Array.getElem_modify, h2c, h1c, Ne.symm h2c, Ne.symm h1c]
    refine ⟨?_, ?_, fun hs => by simp only [Array.size_modify]; exact hs⟩
    · intro c hc x hx y hy hne
      have hc' : c < cls.size := by simpa using hc
      rw [hmem c hc'] at hx hy
      rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨h1, h2, hx⟩
      · rcases hy with ⟨-, hy⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩
        · rcases hx with hx | rfl <;> rcases hy with hy | rfl
          · exact hP c hc' x hx y hy hne
          · exact hcs x hx hne
          · rw [mul_comm]; exact hcs y hy (Ne.symm hne)
          · exact absurd rfl hne
        · exact absurd h1.symm hne12
        · exact absurd rfl h2
      · rcases hy with ⟨h1, -⟩ | ⟨-, hy⟩ | ⟨h1, -, -⟩
        · exact absurd h1 hne12
        · exact hP c hc' x (Array.mem_of_mem_erase hx) y (Array.mem_of_mem_erase hy) hne
        · exact absurd rfl h1
      · rcases hy with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, -, hy⟩
        · exact absurd h3 h2
        · exact absurd h3 h1
        · exact hP c hc' x hx y hy hne
    · rintro x ⟨c, hc, hx⟩
      by_cases hxu : x = u
      · subst hxu
        exact ⟨c₂, by simpa using h₂, (hmem c₂ h₂ x).mpr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩
      · refine ⟨c, by simpa using hc, (hmem c hc x).mpr ?_⟩
        by_cases h2c : c = c₂
        · exact Or.inl ⟨h2c, Or.inl hx⟩
        · by_cases h1c : c = c₁
          · exact Or.inr (Or.inl ⟨h1c, (Array.mem_erase_of_ne hxu).mpr (h1c ▸ hx)⟩)
          · exact Or.inr (Or.inr ⟨h1c, h2c, hx⟩)

theorem applyOps_ok {N : ℕ} : ∀ (ops : List Op) {cls cls' : Array (Array ℕ)},
    applyOps N cls ops = some cls' → Proper cls →
    Proper cls' ∧ (∀ x, InCls cls x → InCls cls' x) ∧ (cls.size ≤ c7 N → cls'.size ≤ c7 N) := by
  intro ops
  induction ops with
  | nil => intro cls cls' h hP; simp [applyOps] at h; subst h; exact ⟨hP, fun x h => h, id⟩
  | cons op ops ih =>
    intro cls cls' h hP
    simp only [applyOps] at h
    split at h
    · rename_i cls₁ h₁
      obtain ⟨hP1, hI1, hS1⟩ := applyOp_ok h₁ hP
      obtain ⟨hP2, hI2, hS2⟩ := ih h hP1
      exact ⟨hP2, fun x hx => hI2 x (hI1 x hx), fun hs => hS2 (hS1 hs)⟩
    · simp at h

lemma c7_mono {a b : ℕ} (h : a ≤ b) : c7 a ≤ c7 b := Nat.div_le_div_right (by omega)

theorem runFrom_sound {Aux : Type} (prop : Aux → Array (Array ℕ) → ℕ → List Op × ℕ × Aux)
    (marks : Array Bool) (B : ℕ)
    (hmarks : ∀ w, 1 ≤ w → w ≤ B → marks.getD w true = false → Squarefree (w * w + 1)) :
    ∀ k v aux cls, runFrom prop marks k v aux cls = true → 1 ≤ v → v - 1 + k ≤ B →
      ClsOk (v - 1) cls → ∀ N, v - 1 ≤ N → N ≤ v - 1 + k → Statement N := by
  intro k
  induction k with
  | zero =>
    intro v aux cls _ _ _ hok N h1 h2
    have : N = v - 1 := by omega
    subst this; exact statement_of_clsOk hok
  | succ k ih =>
    intro v aux cls hrun hv hB hok N h1 h2
    rcases Nat.eq_or_lt_of_le h1 with heq | hlt
    · subst heq; exact statement_of_clsOk hok
    simp only [runFrom] at hrun
    split at hrun
    · simp at hrun
    · rename_i cls' hops
      simp only [Bool.and_eq_true] at hrun
      obtain ⟨hchk, hrest⟩ := hrun
      obtain ⟨hP', hI', hS'⟩ := applyOps_ok _ hops hok.1
      have hok' : ClsOk v cls' := by
        refine ⟨hP', ?_, hS' (hok.2.2.trans (c7_mono (by omega)))⟩
        intro w hw1 hwv hw
        rcases Nat.lt_or_ge w v with hwlt | hwge
        · exact hI' w (hok.2.1 w hw1 (by omega) hw)
        · have hwv' : w = v := by omega
          subst hwv'
          by_cases hm : marks.getD w true = true
          · simp only [hm, ite_true] at hchk
            split at hchk
            · rename_i hlt'
              exact ⟨_, hlt', Array.contains_iff_mem.mp hchk⟩
            · simp at hchk
          · exact absurd (hmarks w hw1 (by omega) (by simpa using hm)) hw
      exact ih (v + 1) _ cls' hrest (by omega) (by omega) (by simpa using hok') N (by omega)
        (by omega)

/-- **The computational part, reduced to one Boolean.** -/
theorem compCheck_sound {X : ℕ} (h : compCheck X = true) : ∀ N ≤ X, Statement N := by
  intro N hN
  unfold compCheck at h
  split at h
  · simp at h
  · rename_i marks hm
    have hmarks := fun w hw1 hwX hw => buildMarks_sound hm (w := w) hw1 hwX hw
    have hok0 : ClsOk 0 #[] := ⟨fun c hc => by simp at hc, fun v h1 h2 => by omega, by simp⟩
    exact runFrom_sound _ marks X hmarks X 1 _ _ h le_rfl (by omega) hok0 N (by omega) (by omega)

end Erdos848
