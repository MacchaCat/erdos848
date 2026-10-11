import Erdos848.CheckSound
import ErdosComp.KTable

/-!
# Soundness of the kernel-friendly prime table

* `fastP_eq`: for `n < 4473²`, `fastP n = isPrimeB n`.
* `stAt_add_segB`: `stAt (lo + len) = addSt (stAt lo) (segB 64 lo len)` for `lo + len < 4473²`.
* `chainOK_sound`: a table accepted by `chainOK 0 zeroSt` has `e.2 = stAt e.1` for every entry.
* `lookDT_eq`: lookups in a tree of valid entries agree with `stAt`.
-/

namespace Erdos848

open ErdosComp Finset

theorem smallPrimes_filter : (List.range 4473).filter isPrimeB = smallPrimesL := by decide +kernel

theorem PSH_eq : PSH = smallPrimesL.prod := by decide +kernel

lemma mem_smallPrimes {p : ℕ} : p ∈ smallPrimesL ↔ p < 4473 ∧ p.Prime := by
  rw [← smallPrimes_filter, List.mem_filter, List.mem_range, isPrimeB_iff]

theorem fastP_eq {n : ℕ} (hn : n < 20007729) : fastP n = isPrimeB n := by
  unfold fastP
  by_cases hs : n < 4473
  · rw [show Nat.blt n 4473 = true from Nat.blt_eq.mpr hs, cond_true]
  · have hb : Nat.blt n 4473 = false := by
      cases h : Nat.blt n 4473
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hs
    rw [hb, cond_false]
    -- gcd(n, PSH) = 1 ↔ n prime
    have key : Nat.gcd n PSH = 1 ↔ n.Prime := by
      rw [PSH_eq]
      constructor
      · intro h
        by_contra hnp
        have hn0 : 0 < n := by omega
        have hsq := Nat.minFac_sq_le_self hn0 hnp
        have hmf : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
        have hlt : Nat.minFac n < 4473 := by
          by_contra hge; push Not at hge
          have : 4473 * 4473 ≤ Nat.minFac n ^ 2 := by nlinarith
          omega
        have hmem : Nat.minFac n ∈ smallPrimesL := mem_smallPrimes.mpr ⟨hlt, hmf⟩
        have hd1 : Nat.minFac n ∣ Nat.gcd n smallPrimesL.prod :=
          Nat.dvd_gcd (Nat.minFac_dvd n) (List.dvd_prod hmem)
        rw [h] at hd1
        exact hmf.one_lt.ne' (Nat.dvd_one.mp hd1)
      · intro hp
        have : Nat.Coprime n smallPrimesL.prod := by
          rw [Nat.coprime_list_prod_right_iff]
          intro q hq
          have hq' := mem_smallPrimes.mp hq
          rw [Nat.coprime_primes hp hq'.2]
          omega
        exact this
    have e1 : (Nat.beq (Nat.gcd n PSH) 1 = true) ↔ (isPrimeB n = true) := by
      rw [Nat.beq_eq, key, isPrimeB_iff]
    cases h1 : Nat.beq (Nat.gcd n PSH) 1 <;> cases h2 : isPrimeB n <;> simp_all

/-! ### Sums of contributions -/

lemma addSt_zero (a : PSt) : addSt a zeroSt = a := by cases a; simp [addSt, zeroSt]
lemma zero_addSt (a : PSt) : addSt zeroSt a = a := by cases a; simp [addSt, zeroSt]
lemma addSt_assoc (a b c : PSt) : addSt (addSt a b) c = addSt a (addSt b c) := by
  cases a; cases b; cases c; simp [addSt]; omega

lemma stepSt_eq_add {n : ℕ} (hn : n < 20007729) (s : PSt) : stepSt n s = addSt s (contribF n) := by
  have hf := fastP_eq hn
  unfold stepSt contribF isU1B
  rw [hf]
  cases hp : isPrimeB n
  · simp [addSt_zero]
  · cases hu : (n % 4 == 1 && decide (13 ≤ n))
    · simp [hu, addSt]
    · simp [hu, addSt]

/-- The sequential sum of contributions over `(lo, lo + k]`. -/
def segSeq (lo : ℕ) : ℕ → PSt
  | 0 => zeroSt
  | k + 1 => addSt (segSeq lo k) (contribF (lo + k + 1))

lemma segSeq_add (lo a : ℕ) : ∀ b, segSeq lo (a + b) = addSt (segSeq lo a) (segSeq (lo + a) b) := by
  intro b
  induction b with
  | zero => simp [segSeq, addSt_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, segSeq, ih, segSeq, addSt_assoc]
    congr 3; omega

lemma segB_eq : ∀ f lo len, len ≤ 2 ^ f → segB (f + 1) lo len = segSeq lo len := by
  intro f
  induction f with
  | zero =>
    intro lo len hlen
    simp only [pow_zero] at hlen
    interval_cases len
    · rfl
    · show contribF (lo + 1) = addSt zeroSt (contribF (lo + 0 + 1))
      rw [zero_addSt]
  | succ f ih =>
    intro lo len hlen
    show (cond (Nat.beq len 0) zeroSt (cond (Nat.beq len 1) (contribF (lo + 1))
      (addSt (segB (f + 1) lo (len / 2)) (segB (f + 1) (lo + len / 2) (len - len / 2))))) =
      segSeq lo len
    rcases Nat.lt_or_ge len 2 with h | h
    · interval_cases len
      · rfl
      · show contribF (lo + 1) = addSt zeroSt (contribF (lo + 0 + 1))
        rw [zero_addSt]
    · have h0 : Nat.beq len 0 = false := by
        cases hh : Nat.beq len 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
      have h1 : Nat.beq len 1 = false := by
        cases hh : Nat.beq len 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hh) (by omega)
      rw [h0, h1, cond_false, cond_false, ih lo (len / 2) (by rw [pow_succ] at hlen; omega),
        ih (lo + len / 2) (len - len / 2) (by rw [pow_succ] at hlen; omega), ← segSeq_add]
      congr 1; omega

lemma stAt_add_segSeq (lo : ℕ) : ∀ k, lo + k < 20007729 → stAt (lo + k) = addSt (stAt lo) (segSeq lo k) := by
  intro k
  induction k with
  | zero => intro _; simp [segSeq, addSt_zero]
  | succ k ih =>
    intro hk
    rw [← Nat.add_assoc, stAt, ih (by omega), stepSt_eq_add (by omega), segSeq, addSt_assoc]

theorem stAt_add_segB {lo len : ℕ} (h : lo + len < 20007729) :
    stAt (lo + len) = addSt (stAt lo) (segB 64 lo len) := by
  have h63 : (20007729 : ℕ) ≤ 2 ^ 63 := by norm_num
  rw [segB_eq 63 lo len (by omega), stAt_add_segSeq lo len h]

lemma eqSt_true {a b : PSt} (h : eqSt a b = true) : a = b := by
  unfold eqSt at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  cases a; cases b; simp_all

theorem chainOK_sound : ∀ (tab : List (ℕ × PSt)) (x : ℕ) (v : PSt), v = stAt x →
    chainOK x v tab = true → ∀ e ∈ tab, e.2 = stAt e.1 := by
  intro tab
  induction tab with
  | nil => intro _ _ _ _ e he; simp at he
  | cons hd rest ih =>
    obtain ⟨y, w⟩ := hd
    intro x v hv hc e he
    unfold chainOK at hc
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    obtain ⟨⟨⟨hxy, hy⟩, heq⟩, hrest⟩ := hc
    have hw : w = stAt y := by
      rw [eqSt_true heq, hv, show y = x + (y - x) by omega, ← stAt_add_segB (by omega)]
      congr 1; omega
    rcases List.mem_cons.mp he with rfl | he
    · exact hw
    · exact ih y w hw hrest e he

/-! ### Trees -/

def _root_.ErdosComp.PTree.entries : PTree → List (ℕ × PSt)
  | .leaf => []
  | .node l k v r => l.entries ++ (k, v) :: r.entries

lemma _root_.ErdosComp.PTree.look_mem : ∀ (t : PTree) (x : ℕ) (v : PSt), t.look x = some v → (x, v) ∈ t.entries := by
  intro t
  induction t with
  | leaf => intro x v h; simp [PTree.look] at h
  | node l k w r ihl ihr =>
    intro x v h
    unfold PTree.look at h
    simp only [PTree.entries, List.mem_append, List.mem_cons]
    cases hb : Nat.beq x k
    · rw [hb, cond_false] at h
      cases hl : Nat.blt x k
      · rw [hl, cond_false] at h; exact Or.inr (Or.inr (ihr x v h))
      · rw [hl, cond_true] at h; exact Or.inl (ihl x v h)
    · rw [hb, cond_true] at h
      have := Nat.beq_eq.mp hb; subst this
      simp only [Option.some.injEq] at h; subst h
      exact Or.inr (Or.inl rfl)

theorem lookDT_eq (t : PTree) (ht : ∀ e ∈ t.entries, e.2 = stAt e.1) (x : ℕ) : lookDT t x = stAt x := by
  unfold lookDT
  split
  · rename_i v hv
    exact ht (x, v) (PTree.look_mem t x v hv)
  · rfl

lemma _root_.ErdosComp.PTree.matchT_entries (t : PTree) :
    ∀ (l r : List (ℕ × PSt)), matchT t l = some r → t.entries ++ r = l := by
  induction t with
  | leaf =>
    intro l r h
    simp only [matchT, Option.some.injEq] at h
    simp [PTree.entries, h]
  | node a k v b iha ihb =>
    intro l r h
    simp only [matchT] at h
    split at h
    · rename_i k₁ v₁ rest ha
      cases hc : (Nat.beq k k₁ && eqSt v v₁)
      · rw [hc] at h; simp at h
      · rw [hc, cond_true] at h
        simp only [Bool.and_eq_true, Nat.beq_eq] at hc
        obtain ⟨rfl, hv⟩ := hc
        obtain rfl := eqSt_true hv
        have h1 := iha l _ ha
        have h2 := ihb rest r h
        simp only [PTree.entries, List.append_assoc, List.cons_append, h2]
        exact h1
    · simp at h

lemma _root_.ErdosComp.PTree.ofList_entries : ∀ (f : ℕ) (l : List (ℕ × PSt)), ∀ e ∈ (PTree.ofList f l).entries, e ∈ l := by
  intro f
  induction f with
  | zero => intro l e he; simp [PTree.ofList, PTree.entries] at he
  | succ f ih =>
    intro l e he
    match l, he with
    | [], he => simp [PTree.ofList, PTree.entries] at he
    | a :: l', he =>
      unfold PTree.ofList at he
      split at he
      · simp [PTree.entries] at he
      · rename_i k v rest hdrop
        simp only [PTree.entries, List.mem_append, List.mem_cons] at he
        rcases he with h | h | h
        · exact List.mem_of_mem_take (ih _ e h)
        · subst h
          have : (k, v) ∈ (a :: l').drop ((a :: l').length / 2) := by rw [hdrop]; exact List.mem_cons_self
          exact List.mem_of_mem_drop this
        · have h' := ih rest e h
          have : e ∈ (a :: l').drop ((a :: l').length / 2) := by rw [hdrop]; exact List.mem_cons_of_mem _ h'
          exact List.mem_of_mem_drop this

end Erdos848
