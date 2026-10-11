import Erdos848.Skeleton

/-!
# Phase 2: elementary counting lemmas

* `card_mod_eq_le`: a residue class mod `Q` has at most `N / Q + 1` elements in `[1,N]`.
* `exists_prime_sq_dvd`: a positive non-squarefree number has a prime square divisor.
* `prime_sq_dvd_mul_add_one_iff` (fact F5): for a prime `p ∤ b`, `p² ∣ ab+1` iff `a` lies in one
  fixed residue class mod `p²`.
* `badCount_le_sum`: `badCount` is bounded by a sum over primes of single-class counts.
-/

namespace Erdos848

open Finset

/-- A residue class mod `Q` meets `[1,N]` in at most `N / Q + 1` points. -/
lemma card_mod_eq_le (N Q r : ℕ) :
    ((Icc 1 N).filter (fun a => a % Q = r)).card ≤ N / Q + 1 := by
  -- the map a ↦ a / Q is injective on the class and lands in [0, N / Q]
  calc ((Icc 1 N).filter (fun a => a % Q = r)).card
      ≤ (range (N / Q + 1)).card := by
        apply card_le_card_of_injOn (fun a => a / Q)
        · intro a ha
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right ha.1.2)
        · intro a ha a' ha' h
          simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ha'
          simp only at h
          rw [← Nat.div_add_mod a Q, ← Nat.div_add_mod a' Q, h, ha.2, ha'.2]
    _ = N / Q + 1 := card_range _

/-- A positive integer that is not squarefree has a prime square divisor. -/
lemma exists_prime_sq_dvd {n : ℕ} (h : ¬ Squarefree n) : ∃ p, p.Prime ∧ p * p ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, hd⟩ := h
  exact ⟨p, hp, hd⟩

/-- If a prime divides `b`, its square cannot divide `ab + 1`. -/
lemma not_sq_dvd_of_dvd {p a b : ℕ} (hp : p.Prime) (hpb : p ∣ b) : ¬ p * p ∣ a * b + 1 := by
  intro h
  have h1 : p ∣ a * b + 1 := dvd_trans (Dvd.intro p rfl) h
  have h2 : p ∣ a * b := dvd_mul_of_dvd_right hpb a
  have : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- (F5) For a prime `p ∤ b` there is a residue `c < p²` with
`p² ∣ ab+1 ↔ a ≡ c (mod p²)`. -/
lemma prime_sq_dvd_mul_add_one_iff {p b : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    ∃ c < p * p, ∀ a, p * p ∣ a * b + 1 ↔ a % (p * p) = c := by
  have hpp : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  have hcop : Nat.Coprime b (p * p) :=
    Nat.Coprime.mul_right ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)))
  -- let u be the inverse of b mod p²; c = (p² - 1) * u mod p²  (i.e. -b⁻¹)
  set u := ((ZMod.unitOfCoprime b hcop)⁻¹ : (ZMod (p * p))ˣ)
  set c := ((-(u : ZMod (p * p))).val) with hc
  have : NeZero (p * p) := ⟨hpp.ne'⟩
  refine ⟨c, ZMod.val_lt _, fun a => ?_⟩
  have hb : ((b : ZMod (p * p)) * (u : ZMod (p * p))) = 1 := by
    have := Units.mul_inv (ZMod.unitOfCoprime b hcop)
    simp [u, ZMod.coe_unitOfCoprime] at this ⊢
  rw [← ZMod.natCast_eq_zero_iff]   -- p² ∣ ab+1 ↔ (ab+1 : ZMod p²) = 0
  constructor
  · intro h
    have h' : ((a : ZMod (p * p)) * b + 1) = 0 := by exact_mod_cast h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      have := congrArg (· * (u : ZMod (p * p))) h'
      simp only [add_mul, zero_mul, one_mul, mul_assoc, hb, mul_one] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [hc, ← this, ZMod.val_natCast]
  · intro h
    have : (a : ZMod (p * p)) = -(u : ZMod (p * p)) := by
      rw [← ZMod.natCast_mod a (p * p), h, hc, ZMod.natCast_zmod_val]
    push_cast
    rw [this, neg_mul, mul_comm (u : ZMod (p * p)) (b : ZMod (p * p)), hb, neg_add_cancel]

/-- Union bound: if every `a` counted by `badCount` (with `a ≤ N`) has a prime square divisor of
`ab+1` with `p ∈ S`, then `badCount` is at most the sum over `S` of the per-prime counts. -/
lemma badCount_le_sum (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] (S : Finset ℕ)
    (hS : ∀ p, p.Prime → ¬ p ∣ b → p * p ≤ N * b + 1 → p ∈ S) :
    badCount N P b ≤ ∑ p ∈ S, ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card := by
  unfold badCount
  calc ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a * b + 1))).card
      ≤ (S.biUnion (fun p => (Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1))).card := by
        apply card_le_card
        intro a ha
        simp only [mem_filter, mem_Icc] at ha
        obtain ⟨p, hp, hd⟩ := exists_prime_sq_dvd ha.2.2
        have hpb : ¬ p ∣ b := fun h => not_sq_dvd_of_dvd hp h hd
        have hle : p * p ≤ N * b + 1 := by
          have := Nat.le_of_dvd (Nat.succ_pos _) hd
          have : a * b ≤ N * b := Nat.mul_le_mul_right b ha.1.2
          omega
        simp only [mem_biUnion, mem_filter, mem_Icc]
        exact ⟨p, hS p hp hpb hle, ⟨ha.1, ha.2.1, hd⟩⟩
    _ ≤ _ := card_biUnion_le

/-- Each per-prime term is a single residue class (for `p ∤ b`), hence `≤ N / p² + 1`. -/
lemma card_sq_dvd_le (N b : ℕ) (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card ≤ N / (p * p) + 1 := by
  obtain ⟨c, -, hc⟩ := prime_sq_dvd_mul_add_one_iff hp hpb
  calc ((Icc 1 N).filter (fun a => P a ∧ p * p ∣ a * b + 1)).card
      ≤ ((Icc 1 N).filter (fun a => a % (p * p) = c)).card := by
        apply card_le_card; intro a ha
        simp only [mem_filter] at ha ⊢
        exact ⟨ha.1, (hc a).mp ha.2.2⟩
    _ ≤ N / (p * p) + 1 := card_mod_eq_le N (p * p) c

end Erdos848
