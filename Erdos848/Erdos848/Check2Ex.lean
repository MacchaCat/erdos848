import Erdos848.Check2Core
import Erdos848.RootLocal

/-!
# Soundness of the §10 checker, part 4: `Ex(b)` through witness structures

`ex_le`: if the structure lists are sorted, valid and complete, and the bucket check `exOK`
passes, then every witness `b ≤ xb` (with the constraint of the list) has
`|Ex(b)| ≤ En / (Y · KE)` for every `N ≤ Nhi`.

* `discOK_sound`: a verified table entry gives the hypothesis `G(R) ≤ αR + β` of Lemma E2.
* `bigProd_le_prod`: `u` distinct primes `> 23` have product at least `29 · 31 ⋯` (`u` factors).
-/

namespace Erdos848

open Finset ErdosComp

/-! ### Root counts and the table entries -/

lemma rootCnt_eq (b m : ℕ) : rootCnt b m = (rootSet b m).card := by
  unfold rootCnt rootSet
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  congr 1
  ext s
  simp

lemma rootSet_add_period {b P : ℕ} (h : b ∣ P) (m : ℕ) : rootSet b (m + P) = rootSet b m := by
  unfold rootSet
  apply filter_congr
  intro s _
  obtain ⟨k, rfl⟩ := h
  rw [show s * s * (m + b * k) = s * s * m + b * (s * s * k) by ring, Nat.add_mul_mod_self_left]

lemma gLocL_eq (e : ℕ) {qs : List ℕ} (hqs : qs.Nodup) (m : ℕ) :
    gLocL e qs m = gLoc e qs.toFinset m := by
  unfold gLocL gLoc
  rw [List.prod_toFinset _ hqs]
  simp only [rootCnt_eq]

lemma gLocL_period (e : ℕ) (qs : List ℕ) (m : ℕ) :
    gLocL e qs (m + 2 ^ e * qs.prod) = gLocL e qs m := by
  unfold gLocL
  rw [rootCnt_eq, rootCnt_eq, rootSet_add_period (dvd_mul_right _ _)]
  congr 1
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [rootCnt_eq, rootCnt_eq, rootSet_add_period]
  exact dvd_mul_of_dvd_right (List.dvd_prod hq) _

/-- `G(r) = ∑_{1 ≤ k ≤ r} g(k)`. -/
def Gsum (g : ℕ → ℕ) (r : ℕ) : ℕ := ∑ k ∈ Icc 1 r, g k

lemma Gsum_succ (g : ℕ → ℕ) (r : ℕ) : Gsum g (r + 1) = Gsum g r + g (r + 1) := by
  unfold Gsum
  rw [show Icc 1 (r + 1) = insert (r + 1) (Icc 1 r) by ext x; simp only [mem_Icc, mem_insert]; omega,
    sum_insert (by simp)]
  ring

lemma discGo_spec (e : ℕ) (qs : List ℕ) (P S bn : ℕ) : ∀ f m G0,
    discGo e qs P S bn f m G0 = true → G0 = Gsum (gLocL e qs) (m - 1) → 1 ≤ m → m + f = P + 1 →
    (∀ r, m ≤ r → r < P → P * Gsum (gLocL e qs) r ≤ S * r + bn) ∧ Gsum (gLocL e qs) P = S
  | 0, m, G0, h, hG, hm, hf => by
    simp only [discGo, Nat.beq_eq] at h
    refine ⟨fun r h1 h2 => by omega, ?_⟩
    rw [← h, hG, show m - 1 = P by omega]
  | f + 1, m, G0, h, hG, hm, hf => by
    simp only [discGo, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hGm : G0 + gLocL e qs m = Gsum (gLocL e qs) m := by
      rw [hG]; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Gsum_succ]; simp
    rw [hGm] at h1 h2
    have ih := discGo_spec e qs P S bn f (m + 1) _ h2 (by simp) (by omega) (by omega)
    refine ⟨fun r hr1 hr2 => ?_, ih.2⟩
    rcases Nat.eq_or_lt_of_le hr1 with rfl | hr
    · rcases h1 with h1 | h1
      · omega
      · exact h1
    · exact ih.1 r hr hr2

/-- **A verified table entry gives the hypothesis of Lemma E2.** -/
theorem discOK_sound (d : DiscE) (h : discOK d = true) :
    d.e ≤ 3 ∧ d.qs.Nodup ∧ ∀ R, ∑ m ∈ Icc 1 R, (gLoc d.e d.qs.toFinset m : ℝ) ≤
      ((d.Ssum : ℝ) / d.P) * R + (d.bn : ℝ) / d.P := by
  unfold discOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨he, hinc⟩, hPpos⟩, hP⟩, hgo⟩ := h
  have hnd : d.qs.Nodup := by
    have : ∀ l : List ℕ, incr l = true → l.Pairwise (· < ·) := by
      intro l
      induction l with
      | nil => intro _; exact List.Pairwise.nil
      | cons a l ih =>
        intro hl
        rcases l with _ | ⟨b, l⟩
        · simp
        · simp only [incr, Bool.and_eq_true, Nat.blt_eq] at hl
          have ih' := ih hl.2
          refine List.Pairwise.cons (fun x hx => ?_) ih'
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hl.1
          · exact lt_trans hl.1 (List.rel_of_pairwise_cons ih' hx)
    exact (this _ hinc).imp (fun h => ne_of_lt h)
  refine ⟨he, hnd, ?_⟩
  have hspec := discGo_spec d.e d.qs d.P d.Ssum d.bn d.P 1 0 hgo (by simp [Gsum]) le_rfl (by omega)
  set g := gLocL d.e d.qs with hg
  have hper : ∀ m, g (m + d.P) = g m := fun m => by rw [hP, hg, gLocL_period]
  have hshift : ∀ n, Gsum g (n + d.P) = Gsum g n + d.Ssum := by
    intro n
    induction n with
    | zero => rw [zero_add, hspec.2]; simp [Gsum]
    | succ n ih =>
      rw [show n + 1 + d.P = n + d.P + 1 by omega, Gsum_succ, ih, Gsum_succ,
        show n + d.P + 1 = (n + 1) + d.P by omega, hper]
      ring
  have hnat : ∀ R, d.P * Gsum g R ≤ d.Ssum * R + d.bn := by
    intro R
    induction R using Nat.strong_induction_on with
    | _ R ih =>
      by_cases hR : R < d.P
      · rcases Nat.eq_zero_or_pos R with rfl | hR0
        · simp [Gsum]
        · exact hspec.1 R hR0 hR
      · have := ih (R - d.P) (by omega)
        rw [show R = (R - d.P) + d.P by omega, hshift]
        nlinarith
  intro R
  have hsum : ∑ m ∈ Icc 1 R, (gLoc d.e d.qs.toFinset m : ℝ) = (Gsum g R : ℝ) := by
    unfold Gsum; push_cast
    apply sum_congr rfl; intro m _; rw [hg, gLocL_eq d.e hnd]
  rw [hsum]
  have hPR : (0 : ℝ) < d.P := by exact_mod_cast hPpos
  have := hnat R
  have hR : (d.P : ℝ) * (Gsum g R : ℝ) ≤ d.Ssum * R + d.bn := by exact_mod_cast this
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hPR]
  linarith

/-! ### Products of large primes -/

def BP : List ℕ := [29, 31, 37, 41, 43, 47]

lemma BP_complete : ∀ p < 48, p.Prime → 23 < p → p ∈ BP := by decide

lemma BP_count : ∀ a < 48, ∀ k < 6, a < BP[k]! → (BP.filter (· ≤ a)).length ≤ k := by decide

lemma bigProd_succ {k : ℕ} (hk : k < 6) : bigProd (k + 1) = bigProd k * BP[k]! := by
  interval_cases k <;> rfl

lemma bigProd_six : ∀ k, 6 ≤ k → bigProd k = bigProd 6
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h => by omega
  | _ + 6, _ => rfl

/-- `k` distinct primes `> 23` have product at least `bigProd k` (`k ≤ 6`). -/
theorem bigProd_le_prod : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ 23 < p) →
    bigProd (min T.card 6) ≤ ∏ p ∈ T, p := by
  intro T
  induction T using Finset.induction_on_max with
  | empty => intro _; simp [bigProd]
  | insert a s hlt ih =>
    intro hS
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, prod_insert has]
    have ih' := ih (fun p hp => hS p (mem_insert_of_mem hp))
    have ha1 : 1 ≤ a := (hS a (mem_insert_self a s)).1.one_lt.le
    by_cases hk : 6 ≤ s.card
    · rw [show min (s.card + 1) 6 = 6 by omega]
      rw [show min s.card 6 = 6 by omega] at ih'
      calc bigProd 6 ≤ ∏ p ∈ s, p := ih'
        _ ≤ a * ∏ p ∈ s, p := Nat.le_mul_of_pos_left _ ha1
    · push Not at hk
      rw [show min (s.card + 1) 6 = s.card + 1 by omega, bigProd_succ hk]
      rw [show min s.card 6 = s.card by omega] at ih'
      have hBa : BP[s.card]! ≤ a := by
        by_contra hcon
        push Not at hcon
        have ha48 : a < 48 := lt_of_lt_of_le hcon (by interval_cases h : s.card <;> decide)
        have hsub : insert a s ⊆ (BP.filter (· ≤ a)).toFinset := by
          intro x hx
          have hxp := hS x hx
          have hxa : x ≤ a := by
            rcases mem_insert.mp hx with rfl | hx'
            · exact le_refl _
            · exact (hlt x hx').le
          rw [List.mem_toFinset, List.mem_filter]
          exact ⟨BP_complete x (by omega) hxp.1 hxp.2, by simpa using hxa⟩
        have h1 := card_le_card hsub
        rw [card_insert_of_notMem has] at h1
        have h2 := List.toFinset_card_le (BP.filter (· ≤ a))
        have h3 := BP_count a ha48 s.card hk hcon
        omega
      calc bigProd s.card * BP[s.card]! ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul ih' hBa
        _ = a * ∏ p ∈ s, p := mul_comm _ _

/-! ### The structure of a witness -/

lemma smallW_spec : ∀ p, p ∈ smallW ↔ p ≤ 23 ∧ p.Prime ∧ p ≠ 2 := by
  intro p
  constructor
  · intro h; simp only [smallW, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rintro ⟨h1, h2, h3⟩
    interval_cases p <;> simp_all (config := { decide := true }) [smallW]

lemma smallW_nodup : smallW.Nodup := by decide

/-- The small odd primes dividing `b`. -/
def qsOf (b : ℕ) : List ℕ := smallW.filter (fun p => p ∣ b)

/-- The number of odd prime factors `> 23`. -/
def uOf (b : ℕ) : ℕ := ((oddPF b).filter (fun p => ¬ p ≤ 23)).card

lemma qsOf_toFinset {b : ℕ} (hb : b ≠ 0) : (qsOf b).toFinset = (oddPF b).filter (· ≤ 23) := by
  ext p
  simp only [qsOf, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_filter, oddPF,
    Nat.mem_primeFactors, smallW_spec]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨⟨h2, h4, hb⟩, h3⟩, h1⟩
  · rintro ⟨⟨⟨h2, h4, _⟩, h3⟩, h1⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩

lemma qsOf_nodup (b : ℕ) : (qsOf b).Nodup := smallW_nodup.filter _

lemma card_oddPF_eq {b : ℕ} (hb : b ≠ 0) : (oddPF b).card = (qsOf b).length + uOf b := by
  rw [← List.toFinset_card_of_nodup (qsOf_nodup b), qsOf_toFinset hb, uOf,
    card_filter_add_card_filter_not]

lemma prod_oddPF_eq {b : ℕ} (hb : b ≠ 0) :
    ∏ p ∈ oddPF b, p = (qsOf b).prod * ∏ p ∈ (oddPF b).filter (fun p => ¬ p ≤ 23), p := by
  have h := List.prod_toFinset (fun p => p) (qsOf_nodup b)
  simp only [List.map_id'] at h
  rw [← h, qsOf_toFinset hb, prod_filter_mul_prod_filter_not]

/-- `2^e ∏ S · bigProd u ≤ b` for the structure of `b`. -/
lemma strBm_le {b : ℕ} (hb : 1 ≤ b) :
    strBm (min (b.factorization 2) 3) (qsOf b) (min (uOf b) 6) ≤ b := by
  have hb0 : b ≠ 0 := by omega
  unfold strBm
  set e := min (b.factorization 2) 3
  have h2e : 2 ^ e ∣ b := (pow_dvd_pow 2 (min_le_left _ _)).trans (Nat.ordProj_dvd b 2)
  have hdvd : 2 ^ e * ∏ p ∈ oddPF b, p ∣ b :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_prod_oddPF b e) h2e (prod_oddPF_dvd b)
  have hle := Nat.le_of_dvd (by omega) hdvd
  rw [prod_oddPF_eq hb0] at hle
  have hbig := bigProd_le_prod ((oddPF b).filter (fun p => ¬ p ≤ 23)) (by
    intro p hp
    rw [mem_filter] at hp
    exact ⟨(oddPF_prime hp.1).1, by omega⟩)
  calc 2 ^ e * (qsOf b).prod * bigProd (min (uOf b) 6)
      ≤ 2 ^ e * (qsOf b).prod * ∏ p ∈ (oddPF b).filter (fun p => ¬ p ≤ 23), p :=
        Nat.mul_le_mul_left _ hbig
    _ = 2 ^ e * ((qsOf b).prod * ∏ p ∈ (oddPF b).filter (fun p => ¬ p ≤ 23), p) := by ring
    _ ≤ b := hle

lemma uOf_le {b : ℕ} (hb : 1 ≤ b) (hb' : b ≤ 160000000) : uOf b ≤ 5 := by
  by_contra h
  have := strBm_le hb
  unfold strBm at this
  rw [show min (uOf b) 6 = 6 by omega] at this
  have h1 : 1 ≤ 2 ^ min (b.factorization 2) 3 * (qsOf b).prod := Nat.one_le_iff_ne_zero.mpr (by
    apply mul_ne_zero (by positivity)
    apply Nat.pos_iff_ne_zero.mp
    apply List.prod_pos
    intro q hq
    have := (List.mem_filter.mp hq).1
    simp only [smallW, List.mem_cons, List.not_mem_nil, or_false] at this
    omega)
  have : bigProd 6 ≤ b := le_trans (Nat.le_mul_of_pos_left _ h1) this
  simp [bigProd] at this
  omega

lemma twoFactor_eq {b : ℕ} (hb : b ≠ 0) : twoFactor b = twoC (min (b.factorization 2) 3) := by
  have h8 : 8 ∣ b ↔ 3 ≤ b.factorization 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hb
  have h4 : 4 ∣ b ↔ 2 ≤ b.factorization 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hb
  unfold twoFactor twoC
  by_cases c3 : 3 ≤ b.factorization 2
  · rw [if_pos (h8.mpr c3), if_pos (by omega)]
  · by_cases c2 : 2 ≤ b.factorization 2
    · rw [if_neg (fun h => c3 (h8.mp h)), if_pos (h4.mpr c2), if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (fun h => c3 (h8.mp h)), if_neg (fun h => c2 (h4.mp h)), if_neg (by omega),
        if_neg (by omega)]

/-! ### The checks on the structure lists -/

lemma filter_mem_subl (p : ℕ → Bool) : ∀ l : List ℕ, l.filter p ∈ subl l
  | [] => by simp [subl]
  | x :: xs => by
    simp only [subl, List.filter_cons, List.mem_append, List.mem_map]
    split_ifs
    · exact Or.inr ⟨_, filter_mem_subl p xs, rfl⟩
    · exact Or.inl (filter_mem_subl p xs)

lemma sortedBm_head : ∀ (a : StrE) (l : List StrE), sortedBm (a :: l) = true → ∀ t ∈ l, a.bm ≤ t.bm
  | _, [], _, t, ht => by simp at ht
  | a, b :: l, h, t, ht => by
    simp only [sortedBm, Bool.and_eq_true, Nat.ble_eq] at h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h.1
    · exact h.1.trans (sortedBm_head b l h.2 t ht)

lemma sortedBm_tail : ∀ (a : StrE) (l : List StrE), sortedBm (a :: l) = true → sortedBm l = true
  | _, [], _ => rfl
  | a, b :: l, h => by simp only [sortedBm, Bool.and_eq_true] at h; exact h.2

lemma exOK_spec (f : StrE → ℕ) (aN Y xb En : ℕ) : ∀ S : List StrE, sortedBm S = true →
    exOK S (S.map f) aN Y xb En = true → ∀ s ∈ S, s.bm ≤ xb → strOK aN (f s) Y En s = true
  | [], _, _, s, hs, _ => by simp at hs
  | a :: l, hS, h, s, hs, hsx => by
    have hab : a.bm ≤ s.bm := by
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact le_rfl
      · exact sortedBm_head a l hS s hs'
    have hle : Nat.ble a.bm xb = true := Nat.ble_eq.mpr (le_trans hab hsx)
    simp only [List.map_cons, exOK, hle, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact h.1
    · exact exOK_spec f aN Y xb En l (sortedBm_tail a l hS) h.2 s hs' hsx

lemma discBEq_eq {a b : DiscE} (h : discBEq a b = true) : a = b := by
  unfold discBEq at h
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases a; cases b; simp_all

/-! ### Square roots -/

lemma sqrt_ineq {N Nhi b bm : ℕ} (hN : N ≤ Nhi) (hb : bm ≤ b) :
    Nat.sqrt (N * b + 1) * bm ≤ (Nat.sqrt (Nhi * bm + 1) + 1) * b := by
  set s := Nat.sqrt (N * b + 1)
  set t := Nat.sqrt (Nhi * bm + 1)
  have hs : s * s ≤ N * b + 1 := Nat.sqrt_le _
  have ht : Nhi * bm + 1 < (t + 1) * (t + 1) := Nat.lt_succ_sqrt _
  have h1 : N * b * (bm * bm) ≤ Nhi * bm * (b * b) := by
    calc N * b * (bm * bm) = N * (b * bm) * bm := by ring
      _ ≤ Nhi * (b * bm) * b := by gcongr
      _ = Nhi * bm * (b * b) := by ring
  have h2 : bm * bm ≤ b * b := Nat.mul_le_mul hb hb
  have key : (s * bm) * (s * bm) < ((t + 1) * b) * ((t + 1) * b) ∨ b = 0 := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · exact Or.inr hb0
    left
    calc (s * bm) * (s * bm) = (s * s) * (bm * bm) := by ring
      _ ≤ (N * b + 1) * (bm * bm) := Nat.mul_le_mul_right _ hs
      _ = N * b * (bm * bm) + bm * bm := by ring
      _ ≤ Nhi * bm * (b * b) + b * b := Nat.add_le_add h1 h2
      _ = (Nhi * bm + 1) * (b * b) := by ring
      _ < (t + 1) * (t + 1) * (b * b) := Nat.mul_lt_mul_of_pos_right ht (by positivity)
      _ = ((t + 1) * b) * ((t + 1) * b) := by ring
  rcases key with key | rfl
  · exact (Nat.mul_self_lt_mul_self_iff.mp key).le
  · have : bm = 0 := by omega
    simp [this]

/-! ### `Ex(b)` -/

/-- The witness constraint of structure list `ci`. -/
def ConsP (ci b : ℕ) : Prop := (ci = 0 → ¬ 5 ∣ b) ∧ (ci = 1 → b % 2 = 1) ∧ (ci = 2 → b % 2 = 0)

lemma KE_pos : (0 : ℝ) < KE := by unfold KE; positivity

/-- **`|Ex(b)| ≤ En/(Y·KE)` for every witness of a checked bucket.** -/
theorem ex_le {D : List DiscE} {S : List StrE} {ci : ℕ} (hci : ci ≤ 2) (hS : sortedBm S = true)
    (hval : S.all (strValid D) = true) (hcomp : ∀ e ≤ 3, completeE ci e S = true)
    (hdisc : D.all discOK = true)
    {N Nhi xb Y En : ℕ} (hN : N ≤ Nhi) (hxb : xb ≤ 160000000) (hY : 1 ≤ Y)
    (hok : exOK S (bNsOf Nhi S) (exAN Nhi xb Y) Y xb En = true)
    {b : ℕ} (hb1 : 1 ≤ b) (hbx : b ≤ xb) (hc : ConsP ci b) :
    ((exSet N b Y).card : ℝ) ≤ (En : ℝ) / ((Y : ℝ) * KE) := by
  have hb0 : b ≠ 0 := by omega
  have hu5 := uOf_le hb1 (by omega)
  have hbm := strBm_le hb1
  rw [show min (uOf b) 6 = uOf b by omega] at hbm
  set e := min (b.factorization 2) 3 with he
  -- the structure of `b` is in the list
  have hcons : consOK ci e (qsOf b) = true := by
    obtain ⟨c0, c1, c2⟩ := hc
    unfold consOK
    split_ifs with h0 h1
    · have h5 : 5 ∉ qsOf b := by
        intro h; exact c0 h0 (List.mem_filter.mp h |>.2 |> of_decide_eq_true)
      simpa using h5
    · have hodd := c1 h1
      have : b.factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by omega)
      simp [he, this]
    · have heven := c2 (by omega)
      have : 1 ≤ b.factorization 2 := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hb0]; simpa using
          Nat.dvd_of_mod_eq_zero heven
      simp only [decide_eq_true_eq]; omega
  have hkey : (qsOf b, uOf b) ∈ keysOf ci e := by
    unfold keysOf
    rw [List.mem_flatMap]
    refine ⟨qsOf b, filter_mem_subl _ smallW, ?_⟩
    rw [List.mem_map]
    refine ⟨uOf b, ?_, rfl⟩
    rw [List.mem_filter, List.mem_range]
    refine ⟨by omega, ?_⟩
    simp only [hcons, Bool.true_and, Nat.ble_eq]
    omega
  have hcomp' := hcomp e (min_le_right _ _)
  unfold completeE at hcomp'
  rw [List.all_eq_true] at hcomp'
  obtain ⟨s, hsS, hs⟩ := List.any_eq_true.mp (hcomp' _ hkey)
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨hse, hsq⟩, hsu⟩ := hs
  have hsv := List.all_eq_true.mp hval s hsS
  unfold strValid at hsv
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, List.all_eq_true] at hsv
  obtain ⟨⟨_, hsbm⟩, hch⟩ := hsv
  have hsbm' : s.bm ≤ b := by rw [hsbm, hse, hsq, hsu]; exact hbm
  have hbm1 : 1 ≤ s.bm := by
    rw [hsbm]; unfold strBm
    apply Nat.one_le_iff_ne_zero.mpr
    apply mul_ne_zero (mul_ne_zero (by positivity) ?_) (by unfold bigProd; split <;> norm_num)
    apply Nat.pos_iff_ne_zero.mp; apply List.prod_pos; intro q hq
    rw [hsq] at hq
    have := (List.mem_filter.mp hq).1
    simp only [smallW, List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  have hstr := exOK_spec (fun s => Nat.sqrt (Nhi * s.bm + 1) + 1 + s.bm) _ Y xb En S hS hok s hsS
    (by omega)
  -- the common bounds
  set aN := exAN Nhi xb Y
  set bN := Nat.sqrt (Nhi * s.bm + 1) + 1 + s.bm
  set w := s.qs.length + s.u
  have hw : (oddPF b).card = w := by rw [card_oddPF_eq hb0]; simp only [w, hsq, hsu]
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hA : ((N : ℝ) + 1) / Y + exM N b Y ≤ (aN : ℝ) / Y := by
    have hM : exM N b Y ≤ exM Nhi xb Y := Nat.div_le_div_right (by gcongr)
    have : (aN : ℝ) = Nhi + 1 + (exM Nhi xb Y : ℝ) * Y := by simp [aN, exAN, exM]
    have h0 : (aN : ℝ) / Y = ((Nhi : ℝ) + 1) / Y + exM Nhi xb Y := by
      rw [this]; field_simp
    rw [h0]
    have h1 : ((N : ℝ) + 1) / Y ≤ ((Nhi : ℝ) + 1) / Y := by gcongr
    have h2 : (exM N b Y : ℝ) ≤ exM Nhi xb Y := by exact_mod_cast hM
    linarith
  have hA0 : (0 : ℝ) ≤ ((N : ℝ) + 1) / Y + exM N b Y := by positivity
  unfold strOK at hstr
  simp only [Bool.or_eq_true, Nat.ble_eq, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq,
    List.all_eq_true, List.contains_iff_mem] at hstr
  rcases hstr with htriv | ⟨d, hdch, ⟨hde, hdq⟩, hdin⟩
  · -- the trivial choice (Lemma E1)
    have hE1 := card_exSet_le_E1 N b Y hb1 hY
    have hrho : (rhoBound b : ℝ) = (twoC s.e : ℝ) * 2 ^ w := by
      unfold rhoBound; rw [twoFactor_eq hb0, oddOmega_eq, hw, hse]; push_cast; ring
    rw [hrho] at hE1
    have hnat : ((twoC s.e * 2 ^ w * aN * KE : ℕ) : ℝ) ≤ En := by exact_mod_cast htriv
    push_cast at hnat
    rw [le_div_iff₀ (by have := KE_pos; positivity)]
    have h2 : (0 : ℝ) ≤ (twoC s.e : ℝ) * 2 ^ w := by positivity
    calc ((exSet N b Y).card : ℝ) * (Y * KE)
        ≤ (twoC s.e : ℝ) * 2 ^ w * (((N : ℝ) + 1) / Y + exM N b Y) * (Y * KE) := by
          gcongr
      _ ≤ (twoC s.e : ℝ) * 2 ^ w * ((aN : ℝ) / Y) * (Y * KE) := by gcongr
      _ = (twoC s.e : ℝ) * 2 ^ w * aN * KE := by field_simp
      _ ≤ En := hnat
  · -- a table entry (Lemma E2)
    obtain ⟨d', hd'D, hdd'⟩ := List.any_eq_true.mp (hch d hdch)
    have hdeq := discBEq_eq hdd'
    subst hdeq
    obtain ⟨_, hdnd, hG⟩ := discOK_sound d (List.all_eq_true.mp hdisc d hd'D)
    have hQ : d.qs.toFinset ⊆ oddPF b := by
      intro q hq
      rw [List.mem_toFinset] at hq
      have hq' := hdq q hq
      rw [hsq] at hq'
      have h1 := List.mem_filter.mp hq'
      have h2 := (smallW_spec q).mp h1.1
      unfold oddPF
      rw [mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨h2.2.1, of_decide_eq_true h1.2, hb0⟩, h2.2.2⟩
    have hP0 : (0 : ℝ) < d.P := by
      have := List.all_eq_true.mp hdisc d hd'D
      unfold discOK at this
      simp only [Bool.and_eq_true, Nat.blt_eq] at this
      exact_mod_cast this.1.1.2
    have hE2 := card_exSet_le_E2 N b Y hb1 hY d.qs.toFinset hQ ((d.Ssum : ℝ) / d.P) ((d.bn : ℝ) / d.P)
      (by positivity) (by rw [← he, ← hse, ← hde]; exact hG)
    rw [hw, List.toFinset_card_of_nodup hdnd] at hE2
    -- the square-root term
    have hB : ((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1 ≤ (bN : ℝ) / s.bm := by
      have hsq' := sqrt_ineq (N := N) (Nhi := Nhi) hN hsbm'
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb1
      have hbmR : (0 : ℝ) < s.bm := by exact_mod_cast hbm1
      have : ((Nat.sqrt (N * b + 1) : ℕ) : ℝ) * s.bm ≤ ((Nat.sqrt (Nhi * s.bm + 1) : ℕ) + 1) * b := by
        exact_mod_cast hsq'
      simp only [bN]; push_cast
      rw [div_add_one hbR.ne', div_le_div_iff₀ hbR hbmR]
      nlinarith
    have hnat : ((2 ^ (w - d.qs.length) * (d.Ssum * aN * s.bm + d.bn * bN * Y) * KE : ℕ) : ℝ) ≤
        ((En * d.P * s.bm : ℕ) : ℝ) := by exact_mod_cast hdin
    push_cast at hnat
    have hbmR : (0 : ℝ) < s.bm := by exact_mod_cast hbm1
    have hc0 : (0 : ℝ) ≤ 2 ^ (w - d.qs.length) := by positivity
    have hB0 : (0 : ℝ) ≤ ((Nat.sqrt (N * b + 1) : ℕ) : ℝ) / b + 1 := by positivity
    calc ((exSet N b Y).card : ℝ)
        ≤ 2 ^ (w - d.qs.length) * ((d.Ssum : ℝ) / d.P * (((N : ℝ) + 1) / Y + exM N b Y) +
            (d.bn : ℝ) / d.P * ((Nat.sqrt (N * b + 1) : ℕ) / b + 1)) := hE2
      _ ≤ 2 ^ (w - d.qs.length) * ((d.Ssum : ℝ) / d.P * ((aN : ℝ) / Y) +
            (d.bn : ℝ) / d.P * ((bN : ℝ) / s.bm)) := by gcongr
      _ = 2 ^ (w - d.qs.length) * (d.Ssum * aN * s.bm + d.bn * bN * Y) * KE /
            (d.P * s.bm * (Y * KE)) := by
          have := KE_pos; field_simp
      _ ≤ (En * d.P * s.bm) / (d.P * s.bm * (Y * KE)) := by
          gcongr
      _ = (En : ℝ) / (Y * KE) := by
          have := KE_pos; field_simp

end Erdos848
