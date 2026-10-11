import Erdos848.PrimeTable
import Erdos848.Cases
import Erdos848.OmegaBound

/-!
# Phase 7 (part 2): soundness of the interval checker

Bridges between the executable definitions of `ErdosComp/Check.lean` and the mathematical
quantities of `Cases.lean`.
-/

namespace Erdos848

open Finset ErdosComp

/-! ### The primality test is exact -/

lemma minFacAux_spec {n : ℕ} (hodd : n % 2 = 1) : ∀ f k, k % 2 = 1 → 3 ≤ k →
    n < (k + 2 * f) * (k + 2 * f) → ErdosComp.minFacAux n k f = n →
    ∀ d, k ≤ d → d * d ≤ n → ¬ d ∣ n := by
  intro f
  induction f with
  | zero =>
    intro k _hk _hk3 hlt _hres d hd hdd _hdvd
    have : k * k ≤ d * d := Nat.mul_le_mul hd hd
    simp only [mul_zero, add_zero] at hlt; omega
  | succ f ih =>
    intro k hk hk3 hlt hres d hd hdd hdvd
    simp only [ErdosComp.minFacAux] at hres
    split_ifs at hres with h1 h2
    · have : k * k ≤ d * d := Nat.mul_le_mul hd hd
      omega
    · -- returned k = n, impossible since k * k ≤ n
      push Not at h1
      have : k * k ≤ k := hres ▸ h1
      nlinarith
    · rcases Nat.lt_or_ge d (k + 2) with hlt2 | hge
      · rcases (show d = k ∨ d = k + 1 by omega) with rfl | rfl
        · exact h2 (by simpa using Nat.mod_eq_zero_of_dvd hdvd)
        · have h2k : 2 ∣ k + 1 := by omega
          have := Nat.dvd_trans h2k hdvd
          omega
      · exact ih (k + 2) (by omega) (by omega) (by nlinarith) hres d hge hdd hdvd

lemma prime_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  unfold isPrimeB at h
  by_cases h1 : n < 2
  · simp [h1] at h
  by_cases h2 : n % 2 = 0
  · simp only [h1, h2, ↓reduceIte, beq_self_eq_true, beq_iff_eq] at h
    subst h; exact Nat.prime_two
  simp only [h1, ↓reduceIte, beq_iff_eq, h2] at h
  have hodd : n % 2 = 1 := by omega
  rw [Nat.prime_def_le_sqrt]
  refine ⟨by omega, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · omega
  · exact minFacAux_spec hodd n 3 rfl le_rfl (by nlinarith) h m h3 hmm hdvd

lemma isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime :=
  ⟨prime_of_isPrimeB, isPrimeB_of_prime⟩

lemma isU1B_iff (n : ℕ) : isU1B n = true ↔ IsU1 n := by
  unfold isU1B IsU1
  simp only [Bool.and_eq_true, isPrimeB_iff, beq_iff_eq, decide_eq_true_eq]
  tauto

/-! ### Finite products and sums -/

lemma prodF_eq (cond : ℕ → Bool) (f : ℕ → ℚ) (n : ℕ) :
    prodF cond f n = ∏ p ∈ (range n).filter (fun p => cond p = true), f p := by
  induction n with
  | zero => simp [prodF]
  | succ n ih =>
    rw [prodF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [prod_insert (by simp), mul_comm]
    · rw [mul_one]

lemma sumF_eq (cond : ℕ → Bool) (f : ℕ → ℚ) (n : ℕ) :
    sumF cond f n = ∑ p ∈ (range n).filter (fun p => cond p = true), f p := by
  induction n with
  | zero => simp [sumF]
  | succ n ih =>
    rw [sumF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [sum_insert (by simp), add_comm]
    · rw [add_zero]

lemma cntF_eq (cond : ℕ → Bool) (n : ℕ) :
    cntF cond n = ((range n).filter (fun p => cond p = true)).card := by
  induction n with
  | zero => simp [cntF]
  | succ n ih =>
    rw [cntF, ih, range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]
    · rw [add_zero]

/-! ### The small prime sets -/

lemma smallP_excl5 : smallP 31 (· ∉ ({5} : Finset ℕ)) =
    (range 32).filter (fun p => condP [5] p = true) := by
  ext p; simp [smallP, condP, isPrimeB_iff]

lemma smallP_excl25 : smallP 31 (· ∉ ({2, 5} : Finset ℕ)) =
    (range 32).filter (fun p => condP [2, 5] p = true) := by
  ext p; simp [smallP, condP, isPrimeB_iff]

lemma smallP_U : smallP 41 IsU1 = (range 42).filter (fun p => isU1B p = true) := by
  ext p; simp only [smallP, mem_filter, isU1B_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2⟩⟩

lemma smallP_U_erase (p : ℕ) :
    (smallP 41 IsU1).erase p = (range 42).filter (fun q => condE p q = true) := by
  rw [smallP_U]; ext q
  simp only [mem_erase, mem_filter, condE, Bool.and_eq_true, bne_iff_ne]
  tauto

lemma smallP_odd : smallP 1000 (fun p => p ≠ 2 ∧ p ≠ 5) =
    (range 1001).filter (fun p => condOdd p = true) := by
  ext p
  simp only [smallP, mem_filter, condOdd, Bool.and_eq_true, bne_iff_ne, isPrimeB_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-! ### `ρ` -/

lemma OPc_eq : OPc = OP := by decide

lemma primeProdC_eq (k : ℕ) : primeProdC k = primeProd k := by
  unfold primeProdC primeProd; rw [OPc_eq]

lemma primeProd_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 45) : primeProd j ≤ primeProd k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]
    · rw [primeProd_succ (by omega)]
      have h1 : 1 ≤ OP[k]! := by
        have : ∀ k < 45, 1 ≤ OP[k]! := by decide
        exact this k (by omega)
      calc primeProd j ≤ primeProd k := ih (by omega) (by omega)
        _ ≤ primeProd k * OP[k]! := Nat.le_mul_of_pos_right _ h1

lemma countP_range_ge (P : ℕ → Bool) : ∀ n k, k ≤ n → (∀ j < k, P j = true) →
    k ≤ (List.range n).countP P := by
  intro n
  induction n with
  | zero => intro k hk _; omega
  | succ n ih =>
    intro k hk hP
    rw [List.range_succ, List.countP_append]
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · have := ih k (by omega) hP; omega
    · have hk' : k = n + 1 := by omega
      have := ih n le_rfl (fun j hj => hP j (by omega))
      have hn : P n = true := hP n (by omega)
      simp [hn]; omega

lemma le_Wc {k L : ℕ} (hk : k ≤ 45) (h : primeProd k ≤ L) : k ≤ Wc L := by
  unfold Wc
  rw [← List.countP_eq_length_filter]
  apply countP_range_ge _ 45 k hk
  intro j hj
  simp only [decide_eq_true_eq, primeProdC_eq]
  exact (primeProd_mono (by omega) hk).trans h

lemma W_le_Wc (L : ℕ) : W L ≤ Wc L := by
  rcases Nat.eq_zero_or_pos (W L) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hP : primeProd (W L) ≤ L :=
      Nat.findGreatest_of_ne_zero (P := fun k => primeProd k ≤ L) (n := 45) rfl
        (Nat.pos_iff_ne_zero.mp hpos)
    exact le_Wc (Nat.findGreatest_le 45) hP

lemma rhoMax_le_rhoMaxC (N : ℕ) : rhoMax N ≤ rhoMaxC N := by
  unfold rhoMax rhoMaxC
  have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc N)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc (N / 4))
  have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (W_le_Wc (N / 8))
  omega

/-- `ρ`-bound for a witness `b ≤ N_hi`. -/
lemma rhoBound_le_C {b Nhi : ℕ} (hb : 1 ≤ b) (hbN : b ≤ Nhi) (hN : Nhi < primeProdC 45) :
    rhoBound b ≤ rhoMaxC Nhi :=
  (rhoBound_le_rhoMax hb hbN (by rw [← primeProdC_eq]; exact hN)).trans (rhoMax_le_rhoMaxC Nhi)

/-! ### `log₃` -/

lemma log3Go_ge (n : ℕ) : ∀ f k, k ≤ log3Go n f k := by
  intro f
  induction f with
  | zero => intro k; simp [log3Go]
  | succ f ih =>
    intro k; simp only [log3Go]; split_ifs
    · exact (Nat.le_succ k).trans (ih (k + 1))
    · exact le_rfl

lemma log3Go_reach (n m : ℕ) (hm : 3 ^ m ≤ n) : ∀ f k, k ≤ m → m ≤ k + f → m ≤ log3Go n f k := by
  intro f
  induction f with
  | zero => intro k hk hkf; simp only [log3Go]; omega
  | succ f ih =>
    intro k hk hkf
    simp only [log3Go]
    rcases Nat.lt_or_ge k m with hlt | hge
    · have : 3 ^ (k + 1) ≤ n := (Nat.pow_le_pow_right (by norm_num) hlt).trans hm
      simp only [this, ↓reduceIte]; exact ih (k + 1) hlt (by omega)
    · split_ifs
      · exact (show m ≤ k + 1 by omega).trans (log3Go_ge n f (k + 1))
      · omega

lemma log_le_log3C {N Nhi : ℕ} (h : N ≤ Nhi) : Nat.log 3 N ≤ log3C Nhi := by
  have hmono : Nat.log 3 N ≤ Nat.log 3 Nhi := Nat.log_mono_right h
  refine hmono.trans ?_
  rcases Nat.eq_zero_or_pos Nhi with h0 | hpos
  · subst h0; simp
  have hm : 3 ^ Nat.log 3 Nhi ≤ Nhi := Nat.pow_log_le_self 3 (by omega)
  have hmn : Nat.log 3 Nhi ≤ Nhi := (Nat.lt_pow_self (by norm_num)).le.trans hm
  exact log3Go_reach Nhi _ hm Nhi 0 (Nat.zero_le _) (by omega)

/-- The Pell factor is monotone in `N`. -/
lemma pell_le_pellC {N Nhi : ℕ} (h : N ≤ Nhi) (Y : ℕ) :
    (N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) ≤ pellC Nhi Y := by
  unfold pellC
  apply Nat.mul_le_mul
  · rw [sq, sq]; apply Nat.div_le_div_right; exact Nat.add_le_add_right (Nat.mul_le_mul h h) 1
  · exact Nat.add_le_add_right (log_le_log3C h) 1

/-! ### The first 30 U1 primes -/

lemma UL_spec : ∀ j < 30, isU1B (UL.getD j 0) = true ∧ cntF isU1B (UL.getD j 0) = j := by
  decide +kernel

lemma count_U1_eq (n : ℕ) : Nat.count IsU1 n = cntF isU1B n := by
  rw [Nat.count_eq_card_filter_range, cntF_eq]
  congr 1; apply filter_congr; intro p _; rw [isU1B_iff]

lemma u1_eq_UL {j : ℕ} (hj : j < 30) : u1 j = UL.getD j 0 := by
  obtain ⟨h1, h2⟩ := UL_spec j hj
  have hU : IsU1 (UL.getD j 0) := (isU1B_iff _).mp h1
  unfold u1
  conv_lhs => rw [← h2, ← count_U1_eq]
  exact Nat.nth_count hU

/-! ### Casting the constants -/

lemma prod1_cast (excl : List ℕ) :
    ((prod1 excl : ℚ) : ℝ) = ∏ p ∈ (range 32).filter (fun p => condP excl p = true),
      (1 - 1 / ((p : ℝ) * p)) := by
  unfold prod1; rw [prodF_eq]; push_cast; rfl

lemma k1_eq (excl : List ℕ) : k1 excl = ((range 32).filter (fun p => condP excl p = true)).card := by
  unfold k1; rw [cntF_eq]

lemma prodU_cast : ((prodU : ℚ) : ℝ) = PU 41 := by
  unfold prodU PU; rw [prodF_eq, smallP_U]; push_cast; rfl

lemma kU_eq : kU = (smallP 41 IsU1).card := by unfold kU; rw [cntF_eq, smallP_U]

lemma prErase_cast (p : ℕ) : ((prErase p : ℚ) : ℝ) =
    ∏ q ∈ (smallP 41 IsU1).erase p, (1 - 2 / ((q : ℝ) * q)) := by
  unfold prErase; rw [prodF_eq, smallP_U_erase]; push_cast; rfl

lemma kErase_eq (p : ℕ) : kErase p = ((smallP 41 IsU1).erase p).card := by
  unfold kErase; rw [cntF_eq, smallP_U_erase]

lemma prErase_nonneg (p : ℕ) : (0 : ℝ) ≤ ((prErase p : ℚ) : ℝ) := by
  rw [prErase_cast]
  apply prod_nonneg; intro q hq
  exact (factor_pos (mem_filter.mp (mem_of_mem_erase hq)).2.1).le

lemma gC_eq (N p : ℕ) : gC N 41 p = ((gA p : ℚ) : ℝ) * N + ((gE p : ℚ) : ℝ) := by
  unfold gC wholeB nonB gA gE
  push_cast
  rw [prErase_cast, kErase_eq]
  ring

lemma sumNon_eq (N : ℕ) : ∑ p ∈ smallP 1000 (fun p => p ≠ 2 ∧ p ≠ 5), nonB N p 41 =
    ((cNon : ℚ) : ℝ) * N + ((eNon : ℚ) : ℝ) := by
  unfold cNon eNon
  rw [sumF_eq, sumF_eq, smallP_odd]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl; intro p _
  unfold nonB
  rw [← prErase_cast, ← kErase_eq]
  ring

/-! ### Prime-range sums -/

lemma midsum_le (P S : Finset ℕ) (hPS : P ⊆ S) (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) ≤ a * S2 S + S.card := by
  have h1 : ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) = a * S2 P + P.card := by
    unfold S2; rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one]
    congr 1; apply sum_congr rfl; intro p _; ring
  have h2 : S2 P ≤ S2 S := S2_mono hPS
  have h3 : (P.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hPS
  rw [h1]; nlinarith

lemma midP_sub_primesIn (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    midP z w Q ⊆ primesIn z w := fun p hp => by
  simp only [midP, primesIn, mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩

lemma midP_sub_u1In (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p) :
    midP z w Q ⊆ u1In z w := fun p hp => by
  simp only [midP, u1In, mem_filter] at hp ⊢; exact ⟨hp.1, hQ p hp.2.2⟩

lemma sum_two (P : Finset ℕ) (a : ℝ) :
    ∑ p ∈ P, (2 * (a / ((p : ℝ) * p)) + 2) = 2 * ∑ p ∈ P, (a / ((p : ℝ) * p) + 1) := by
  rw [mul_sum]; apply sum_congr rfl; intro p _; ring

lemma gmax_le (a e : ℝ) (ha : 0 ≤ a) {N Nlo : ℝ} (h : Nlo ≤ N) :
    max (a * N + e) 0 ≤ a * N + max e (-a * Nlo) := by
  rcases le_total 0 (a * N + e) with h0 | h0
  · rw [max_eq_left h0]; linarith [le_max_left e (-a * Nlo)]
  · rw [max_eq_right h0]
    have := le_max_right e (-a * Nlo)
    nlinarith

lemma gA_nonneg (p : ℕ) : (0 : ℝ) ≤ ((gA p : ℚ) : ℝ) := by
  unfold gA; push_cast
  have := prErase_nonneg p
  positivity

lemma gsum_sound (N Nlo L : ℕ) (hL : L ≤ 30) (hN : Nlo ≤ N) :
    ∑ j ∈ range L, max (gC N 41 (u1 j)) 0 ≤
      ((gSumC L : ℚ) : ℝ) * N + ((gSumE Nlo L : ℚ) : ℝ) := by
  unfold gSumC gSumE
  rw [sumF_eq, sumF_eq]
  have hf : (range L).filter (fun _ => true = true) = range L := filter_true_of_mem (fun _ _ => rfl)
  rw [hf]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_le_sum; intro j hj
  have hj30 : j < 30 := by have := mem_range.mp hj; omega
  rw [u1_eq_UL hj30, gC_eq]
  have := gmax_le ((gA (UL.getD j 0) : ℚ) : ℝ) ((gE (UL.getD j 0) : ℚ) : ℝ) (gA_nonneg _)
    (show (Nlo : ℝ) ≤ N by exact_mod_cast hN)
  push_cast at this
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

lemma primeSum_le (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((s2P tab z w : ℚ) : ℝ) + ((cP tab z w : ℚ) : ℝ) := by
  have := midsum_le _ _ (midP_sub_primesIn z w Q) a ha
  have h1 := S2_primesIn_le htab z w
  have h2 := card_primesIn_le htab z w
  nlinarith

lemma u1Sum_le (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p)
    (a : ℝ) (ha : 0 ≤ a) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + 1) ≤
      a * ((s2U tab z w : ℚ) : ℝ) + ((cU tab z w : ℚ) : ℝ) := by
  have := midsum_le _ _ (midP_sub_u1In z w Q hQ) a ha
  have h1 := S2_u1In_le htab z w
  have h2 := card_u1In_le htab z w
  nlinarith

/-! ### The components -/

lemma res_sound (N q T pc : ℕ) (excl : Finset ℕ) (exclL : List ℕ)
    (hS : smallP 31 (· ∉ excl) = (range 32).filter (fun p => condP exclL p = true)) :
    resB N q T 31 pc excl ≤
      ((resCE tab q T exclL pc).1 : ℝ) * N + ((resCE tab q T exclL pc).2 : ℝ) := by
  unfold resB resCE
  have hm := primeSum_le htab 31 pc (· ∉ excl) ((N : ℝ) / q) (by positivity)
  have hT : (0 : ℝ) ≤ T := by positivity
  have := mul_le_mul_of_nonneg_left hm hT
  dsimp only
  push_cast
  rw [prod1_cast, k1_eq, ← hS]
  linear_combination this

lemma sh_sound (N Nhi b pc Y : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N) (hN : N ≤ Nhi)
    (hNhi : Nhi < primeProdC 45) (hY : 1 ≤ Y) :
    shB N b pc Y ≤ ((shCE tab Nhi pc Y).1 : ℝ) * N + ((shCE tab Nhi pc Y).2 : ℝ) := by
  unfold shB shCE
  have hm := primeSum_le htab pc Y (fun p => pc < p) (N : ℝ) (by positivity)
  have hρ : (rhoBound b : ℝ) ≤ rhoMaxC Nhi := by exact_mod_cast rhoBound_le_C hb (hbN.trans hN) hNhi
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hNR : (N : ℝ) ≤ Nhi := by exact_mod_cast hN
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hNb : (N : ℝ) * b ≤ (Nhi : ℝ) * Nhi := by
    have : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have hG : 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 ≤
      2 * ((Nhi : ℝ) + 1) / Y + ((Nhi : ℝ) * Nhi + 1) / ((Y : ℝ) * Y) := by
    rw [sq]
    have hY0 : (0 : ℝ) < Y := by linarith
    gcongr
  have hG0 : 0 ≤ 2 * ((N : ℝ) + 1) / Y + ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2 := by positivity
  have hρ0 : (0 : ℝ) ≤ rhoBound b := by positivity
  have := mul_le_mul hρ hG hG0 (by positivity)
  dsimp only
  push_cast
  linarith

lemma lemB_sound (N Nhi q T pB YB : ℕ) (hN : N ≤ Nhi) :
    lemBB N q T 41 pB YB ≤
      ((lemBCE tab Nhi q T pB YB).1 : ℝ) * N + ((lemBCE tab Nhi q T pB YB).2 : ℝ) := by
  unfold lemBB lemBCE
  have h1 := u1Sum_le htab 41 pB IsU1 (fun _ h => h) ((N : ℝ) / q) (by positivity)
  have h2 := u1Sum_le htab pB YB (fun p => IsU1 p ∧ pB < p) (fun _ h => h.1) (N : ℝ)
    (by positivity)
  have hp : (((N ^ 2 + 1) / (YB + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ (pellC Nhi YB : ℝ) := by
    exact_mod_cast pell_le_pellC hN YB
  rw [sum_two, sum_two]
  have hT : (0 : ℝ) ≤ T := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hT
  dsimp only
  push_cast
  rw [prodU_cast, kU_eq]
  unfold PU
  push_cast at hp
  linear_combination 2 * h1' + 2 * h2 + hp

lemma lemC_sound (N Nlo Nhi pB YB pc L : ℕ) (hL : L ≤ 30) (h1 : Nlo ≤ N) (h2 : N ≤ Nhi) :
    lemCB N 41 1000 pB YB pc (∑ j ∈ range L, max (gC N 41 (u1 j)) 0) ≤
      ((lemCCE tab Nlo Nhi pB YB pc L).1 : ℝ) * N + ((lemCCE tab Nlo Nhi pB YB pc L).2 : ℝ) := by
  unfold lemCB lemCCE
  have e1 := u1Sum_le htab 41 pB (fun p => IsU1 p ∧ 41 < p) (fun _ h => h.1) ((N : ℝ) / 25)
    (by positivity)
  have e2 := u1Sum_le htab pB YB (fun p => IsU1 p ∧ pB < p) (fun _ h => h.1) (N : ℝ)
    (by positivity)
  have e3 : (((N ^ 2 + 1) / (YB + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ (pellC Nhi YB : ℝ) := by
    exact_mod_cast pell_le_pellC h2 YB
  have e4 := sumNon_eq N
  have e5 := gsum_sound N Nlo L hL h1
  have e6 := primeSum_le htab 1000 pc (fun p => 1000 < p) (N : ℝ) (Nat.cast_nonneg N)
  rw [sum_two, sum_two]
  dsimp only
  push_cast
  rw [prodU_cast, kU_eq]
  push_cast at e3 e5
  linear_combination 46 * e1 + 2 * e2 + e3 + e4 + e5 + e6

end

/-! ### Lemma D and one interval -/

lemma addCE_le {a b : CE} {N : ℕ} {X Y : ℝ} (hX : X ≤ (a.1 : ℝ) * N + a.2)
    (hY : Y ≤ (b.1 : ℝ) * N + b.2) :
    X + Y ≤ ((addCE a b).1 : ℝ) * N + (addCE a b).2 := by
  simp only [addCE]; push_cast; linarith

lemma const_le (a e : ℚ) (N : ℕ) : (a : ℝ) * N + e ≤ (((a, e) : CE).1 : ℝ) * N + ((a, e) : CE).2 :=
  le_rfl

/-- **Lemma D.** -/
lemma lemmaD {c : CE} {Nlo N X : ℕ} (hok : okCE Nlo c = true) (hN : Nlo ≤ N)
    (hX : (X : ℝ) ≤ (c.1 : ℝ) * N + c.2) : X ≤ c7 N := by
  unfold okCE at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  have h1R : (c.1 : ℝ) < 1 / 25 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2R : (c.1 : ℝ) * Nlo + c.2 < ((Nlo : ℝ) - 6) / 25 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h2; push_cast at this; exact this
  have hNR : (Nlo : ℝ) ≤ N := by exact_mod_cast hN
  have hc7 : ((N : ℝ) - 6) / 25 ≤ c7 N := by
    unfold c7
    have := Nat.div_add_mod (N + 18) 25
    have := Nat.mod_lt (N + 18) (show 0 < 25 by norm_num)
    have h : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast h
    linarith
  have : (X : ℝ) < c7 N := by nlinarith
  exact_mod_cast this.le

lemma ulProd_eq (n : ℕ) : ulProd n = ∏ j ∈ range n, UL.getD j 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ulProd, ih, prod_range_succ]

lemma ulProd_u1 {n : ℕ} (hn : n ≤ 30) : ulProd n = ∏ j ∈ range n, u1 j := by
  rw [ulProd_eq]; apply prod_congr rfl; intro j hj
  rw [u1_eq_UL (by have := mem_range.mp hj; omega)]

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

theorem countBounds_of_row (r : Row) (hr : checkRow tab r = true) (N : ℕ)
    (hlo : r.Nlo ≤ N) (hhi : N ≤ r.Nhi) : CountBounds N := by
  unfold checkRow at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hY, h7⟩, hlh⟩, hprod⟩, hL30⟩, hLc⟩, okIb⟩, okII⟩, okIII1⟩, okIIIa⟩, okIIIb⟩ := hr
  have hS5 := smallP_excl5
  have hS25 := smallP_excl25
  have sh : ∀ b, Witness N b → shB N b r.pc r.Y ≤
      ((shCE tab r.Nhi r.pc r.Y).1 : ℝ) * N + (shCE tab r.Nhi r.pc r.Y).2 :=
    fun b hw => sh_sound htab N r.Nhi b r.pc r.Y hw.1 hw.2.1 hhi hprod hY
  constructor
  · -- I.b
    intro b b' hw h7b hw' h18
    have := caseIb_real N b b' 31 r.pc r.Y hY hw h7b hw' h18
    have e := addCE_le (addCE_le (res_sound htab N 25 1 r.pc {5} [5] hS5) (sh b hw))
      (addCE_le (res_sound htab N 25 1 r.pc {5} [5] hS5) (sh b' hw'))
    exact lemmaD okIb hlo (by push_cast; exact this.trans e)
  · -- II
    intro b hw hs he
    have hL : N * N + 1 < (∏ j ∈ range (Lval r.Nhi + 1), u1 j) *
        (∏ j ∈ range (Lval r.Nhi + 1), u1 j) := by
      rw [← ulProd_u1 (n := Lval r.Nhi + 1) (by omega)]
      have : N * N ≤ r.Nhi * r.Nhi := Nat.mul_le_mul hhi hhi
      omega
    have := caseII_real N b 31 r.pc r.Y 41 1000 r.pB25 r.Y25 _ hY hw hs he
      (by norm_num) (gBound_prefix N 41 1000 (Lval r.Nhi) hL)
    have e := addCE_le (addCE_le (res_sound htab N 25 2 r.pc {2, 5} [2, 5] hS25)
      (lemC_sound htab N r.Nlo r.Nhi r.pB25 r.Y25 r.pc (Lval r.Nhi) (by omega) hlo hhi))
      (sh b hw)
    exact lemmaD okII hlo (by push_cast; exact this.trans e)
  · -- III.1
    intro b₁ b₃ hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
    have := caseIII1_real N b₁ b₃ 31 r.pc r.Y 41 r.pB50 r.Y50 hY hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
    have e := addCE_le (addCE_le
      (addCE_le (res_sound htab N 100 6 r.pc {2, 5} [2, 5] hS25) (sh b₁ hw₁))
      (addCE_le (res_sound htab N 100 2 r.pc {2, 5} [2, 5] hS25) (sh b₃ hw₃)))
      (lemB_sound htab N r.Nhi 50 23 r.pB50 r.Y50 hhi)
    exact lemmaD okIII1 hlo (by push_cast; exact this.trans e)
  · -- III.2.a
    intro b rr hw hs hbr hrr
    have := caseIII2a_real N b rr 31 r.pc r.Y 41 r.pB100 r.Y100 hY hw hs hbr hrr
    have hc : 2 * ((N : ℝ) / 100) + 2 ≤ (((2 / 100 : ℚ), (2 : ℚ)) : CE).1 * N +
        (((2 / 100 : ℚ), (2 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le hc
      (addCE_le (res_sound htab N 100 2 r.pc {2, 5} [2, 5] hS25) (sh b hw)))
      (lemB_sound htab N r.Nhi 100 23 r.pB100 r.Y100 hhi)
    exact lemmaD okIIIa hlo (by push_cast; exact this.trans e)
  · -- III.2.b, even witness in A₇
    intro b b' rr hw hs hbr hrr hw' h7' he
    have := caseIII2b7_real N b b' rr 31 r.pc r.Y 41 r.pB100 r.Y100 hY hw hs hbr hrr hw' h7' he
    have hc : (N : ℝ) / 100 + 1 ≤ (((1 / 100 : ℚ), (1 : ℚ)) : CE).1 * N +
        (((1 / 100 : ℚ), (1 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le (addCE_le hc
      (addCE_le (res_sound htab N 100 3 r.pc {2, 5} [2, 5] hS25) (sh b hw)))
      (addCE_le (res_sound htab N 25 1 r.pc {2, 5} [2, 5] hS25) (sh b' hw')))
      (lemB_sound htab N r.Nhi 100 23 r.pB100 r.Y100 hhi)
    exact lemmaD okIIIb hlo (by push_cast; exact this.trans e)
  · -- III.2.b, even witness in A₁₈
    intro b b' rr hw hs hbr hrr hw' h18' he
    have := caseIII2b18_real N b b' rr 31 r.pc r.Y 41 r.pB100 r.Y100 hY hw hs hbr hrr hw' h18' he
    have hc : (N : ℝ) / 100 + 1 ≤ (((1 / 100 : ℚ), (1 : ℚ)) : CE).1 * N +
        (((1 / 100 : ℚ), (1 : ℚ)) : CE).2 := by push_cast; linarith
    have e := addCE_le (addCE_le (addCE_le hc
      (addCE_le (res_sound htab N 100 3 r.pc {2, 5} [2, 5] hS25) (sh b hw)))
      (addCE_le (res_sound htab N 25 1 r.pc {2, 5} [2, 5] hS25) (sh b' hw')))
      (lemB_sound htab N r.Nhi 100 23 r.pB100 r.Y100 hhi)
    exact lemmaD okIIIb hlo (by push_cast; exact this.trans e)

end

/-! ### Covering an interval of `N` -/

lemma chain_cover (b N : ℕ) : ∀ (rows : List Row) (a : ℕ), chain a b rows = true →
    (∀ r ∈ rows, r.Nlo ≤ r.Nhi) → rows ≠ [] → a ≤ N → N ≤ b →
    ∃ r ∈ rows, r.Nlo ≤ N ∧ N ≤ r.Nhi := by
  intro rows
  induction rows with
  | nil => intro a _ _ h; exact absurd rfl h
  | cons r rs ih =>
    intro a hc hle _ haN hNb
    simp only [chain, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hra, hc⟩ := hc
    by_cases hN : N ≤ r.Nhi
    · exact ⟨r, List.mem_cons_self .., hra ▸ haN, hN⟩
    · cases rs with
      | nil => simp [chain] at hc; omega
      | cons r' rs' =>
        obtain ⟨r'', hmem, h⟩ := ih r.Nhi hc (fun x hx => hle x (List.mem_cons_of_mem _ hx))
          (by simp) (by omega) hNb
        exact ⟨r'', List.mem_cons_of_mem _ hmem, h⟩

/-- **Soundness of the checker.** -/
theorem countBounds_of_checkAll {a b : ℕ} {rows : List Row} (hc : checkAll a b rows = true)
    (hne : rows ≠ []) (N : ℕ) (haN : a ≤ N) (hNb : N ≤ b) : CountBounds N := by
  unfold checkAll at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hch, hall⟩ := hc
  have htab := evalPts_sound (needPts rows) 0
  have hle : ∀ r ∈ rows, r.Nlo ≤ r.Nhi := by
    intro r hr
    have := hall r hr
    unfold checkRow at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1.1.2
  obtain ⟨r, hr, h1, h2⟩ := chain_cover b N rows a hch hle hne haN hNb
  exact countBounds_of_row htab r (hall r hr) N h1 h2

end Erdos848
