import Erdos848.Check2Alg

/-!
# Soundness of the §10 checker, part 2: the linear pieces, `Mid` and the tails

Each real-valued bound of `Erdos848/Cases2.lean` is bounded by the checker's rational value
(`resR_le`, `lemBR_le`, `midB_le`, `tailB_le`), and is monotone in `N` (`midB_mono`,
`tailB_mono`).
-/

namespace Erdos848

open Finset ErdosComp

/-- A sum over primes in a subset of `S` with nonnegative weights. -/
lemma midsum_le_gen (P S : Finset ℕ) (hPS : P ⊆ S) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ∑ p ∈ P, (a / ((p : ℝ) * p) + c) ≤ a * S2 S + c * S.card := by
  have h1 : ∑ p ∈ P, (a / ((p : ℝ) * p) + c) = a * S2 P + c * P.card := by
    unfold S2; rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul]
    rw [mul_comm c]
    congr 1; apply sum_congr rfl; intro p _; ring
  have h2 : S2 P ≤ S2 S := S2_mono hPS
  have h3 : (P.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hPS
  rw [h1]; nlinarith

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

lemma primeSumK' (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + c) ≤
      a * ((S2Pk lk z w : ℚ) : ℝ) + c * ((CPk lk z w : ℚ) : ℝ) := by
  have := midsum_le_gen _ _ (midP_sub_primesIn z w Q) a c ha hc
  have h1 := S2PK_le hlk z w
  have h2 := CPK_le hlk z w
  nlinarith

lemma u1SumK' (z w : ℕ) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ p, Q p → IsU1 p)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ∑ p ∈ midP z w Q, (a / ((p : ℝ) * p) + c) ≤
      a * ((S2Uk lk z w : ℚ) : ℝ) + c * ((CUk lk z w : ℚ) : ℝ) := by
  have := midsum_le_gen _ _ (midP_sub_u1In z w Q hQ) a c ha hc
  have h1 := S2UK_le hlk z w
  have h2 := CUK_le hlk z w
  nlinarith

omit hlk in
lemma resLin_eq (q z pc dA : ℕ) (exclL : List ℕ) :
    resLin lk q z pc dA exclL =
      ((1 - altL (invSq 1) (primesEx z exclL) dA) / q + S2Pk lk z pc / q,
        terrL (primesEx z exclL).length 1 dA + CPk lk z pc) := rfl

/-- **Lemma A′(iii) with Bonferroni**, as computed by the checker. -/
theorem resR_le (L : ℝ) (hL : 0 ≤ L) (q z pc dA : ℕ) (hq : 0 < q) (excl : Finset ℕ)
    (exclL : List ℕ) (hex : ∀ p, p ∈ excl ↔ p ∈ exclL) :
    resR L q z pc dA excl ≤
      (((resLin lk q z pc dA exclL).1 : ℚ) : ℝ) * L + (((resLin lk q z pc dA exclL).2 : ℚ) : ℝ) := by
  have hP := primesEx_toFinset z excl exclL hex
  have hnd := primesEx_nodup z exclL
  have hA : altE (smallP z (· ∉ excl)) (fun p => ((1 : ℕ) : ℝ) / (p * p)) dA =
      ((altL (invSq 1) (primesEx z exclL) dA : ℚ) : ℝ) := by
    rw [← hP, ← altE_toFinset _ _ hnd]
    apply altE_congr; intro p _; simp [invSq]
  have hT : truncErr (smallP z (· ∉ excl)) (fun _ => ((1 : ℕ) : ℝ)) dA =
      ((terrL (primesEx z exclL).length 1 dA : ℚ) : ℝ) := by
    rw [← hP, ← List.toFinset_card_of_nodup hnd, ← truncErr_const]; simp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hM := primeSumK' hlk z pc (· ∉ excl) (L / q) 1 (by positivity) zero_le_one
  have hsum : ∑ p ∈ midP z pc (· ∉ excl), (((1 : ℕ) : ℝ) * (L / q / (p * p)) + 1 * ((1 : ℕ) : ℝ)) =
      ∑ p ∈ midP z pc (· ∉ excl), (L / q / ((p : ℝ) * p) + 1) := by
    apply sum_congr rfl; intro p _; push_cast; ring
  unfold resR
  rw [hA, hT, hsum, resLin_eq]
  push_cast
  have e1 : L / q * ((S2Pk lk z pc : ℚ) : ℝ) = ((S2Pk lk z pc : ℚ) : ℝ) / q * L := by ring
  have e2 : L / q * (1 - ((altL (invSq 1) (primesEx z exclL) dA : ℚ) : ℝ)) =
      (1 - ((altL (invSq 1) (primesEx z exclL) dA : ℚ) : ℝ)) / q * L := by ring
  nlinarith

omit hlk in
lemma lemBLin_eq (zB pT dB : ℕ) :
    lemBLin lk zB pT dB =
      ((1 - altL (invSq 2) (u1UpTo zB) dB) / 100 + 2 * S2Uk lk zB pT / 100,
        terrL (u1UpTo zB).length 2 dB + 2 * CUk lk zB pT) := rfl

/-- **Lemma B per class with Bonferroni**, as computed by the checker. -/
theorem lemBR_le (L : ℝ) (hL : 0 ≤ L) (zB pT dB : ℕ) :
    lemBR L zB pT dB ≤
      (((lemBLin lk zB pT dB).1 : ℚ) : ℝ) * L + (((lemBLin lk zB pT dB).2 : ℚ) : ℝ) := by
  have hP := u1UpTo_toFinset zB
  have hnd := u1UpTo_nodup zB
  have hA : altE (smallP zB IsU1) (fun p => ((2 : ℕ) : ℝ) / (p * p)) dB =
      ((altL (invSq 2) (u1UpTo zB) dB : ℚ) : ℝ) := by
    rw [← hP, ← altE_toFinset _ _ hnd]
    apply altE_congr; intro p _; simp [invSq]
  have hT : truncErr (smallP zB IsU1) (fun _ => ((2 : ℕ) : ℝ)) dB =
      ((terrL (u1UpTo zB).length 2 dB : ℚ) : ℝ) := by
    rw [← hP, ← List.toFinset_card_of_nodup hnd, ← truncErr_const]; simp
  have hM := u1SumK' hlk zB pT IsU1 (fun _ h => h) (L / 100) 1 (by positivity) zero_le_one
  have hsum : ∑ p ∈ midP zB pT IsU1, (((2 : ℕ) : ℝ) * (L / 100 / (p * p)) + 1 * ((2 : ℕ) : ℝ)) =
      2 * ∑ p ∈ midP zB pT IsU1, (L / 100 / ((p : ℝ) * p) + 1) := by
    rw [mul_sum]; apply sum_congr rfl; intro p _; push_cast; ring
  unfold lemBR
  rw [hA, hT, hsum, lemBLin_eq]
  push_cast
  nlinarith

/-! ### `Mid` -/

omit hlk in
lemma div_sq_eq_zero {N p : ℕ} (h : Nat.sqrt N < p) : N / (p * p) = 0 := by
  apply Nat.div_eq_of_lt
  have := Nat.lt_succ_sqrt N
  have h2 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ p * p := Nat.mul_le_mul h h
  nlinarith

/-- **`Mid` as computed by the checker.** -/
theorem midB_le (N pc Y : ℕ) : midB N pc Y ≤ ((midQ lk N pc Y : ℚ) : ℝ) := by
  set h := max pc (min Y (Nat.sqrt N)) with hh
  unfold midB midQ
  rw [← hh]
  push_cast
  rw [sum_add_distrib]
  simp only [Nat.cast_sum, Nat.cast_one, sum_const, nsmul_eq_mul, mul_one]
  -- the floor terms vanish above `h`
  have h1 : ∑ p ∈ midP pc Y (fun p => pc < p), ((N / (p * p) : ℕ) : ℝ) ≤
      ∑ p ∈ primesIn pc h, (N : ℝ) / ((p : ℝ) * p) := by
    have hsplit : ∑ p ∈ midP pc Y (fun p => pc < p), ((N / (p * p) : ℕ) : ℝ) =
        ∑ p ∈ (midP pc Y (fun p => pc < p)).filter (· ≤ h), ((N / (p * p) : ℕ) : ℝ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      split_ifs with hph
      · rfl
      · simp only [midP, mem_filter, mem_Ioc] at hp
        have : Nat.sqrt N < p := by
          have := le_max_right pc (min Y (Nat.sqrt N)); rw [← hh] at this
          have hm : min Y (Nat.sqrt N) < p := by omega
          rcases min_choice Y (Nat.sqrt N) with e | e <;> rw [e] at hm <;> omega
        rw [div_sq_eq_zero this]; simp
    rw [hsplit]
    refine (sum_le_sum (fun p _ => (show ((N / (p * p) : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) * p) by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := p * p); push_cast at this; exact this))).trans ?_
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [midP, primesIn, mem_filter, mem_Ioc] at hp ⊢
      exact ⟨⟨hp.1.1.1, hp.2⟩, hp.1.2.1⟩
    · intro p _ _; push_cast; positivity
  have h2 : ∑ p ∈ primesIn pc h, (N : ℝ) / ((p : ℝ) * p) = N * S2 (primesIn pc h) := by
    unfold S2; rw [mul_sum]; apply sum_congr rfl; intro p _; ring
  have h3 := S2PK_le hlk pc h
  have h4 : ((midP pc Y (fun p => pc < p)).card : ℝ) ≤ ((CPk lk pc Y : ℚ) : ℝ) :=
    le_trans (by exact_mod_cast card_le_card (midP_sub_primesIn pc Y _)) (CPK_le hlk pc Y)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast at h1
  nlinarith

end

lemma midB_mono {N N' : ℕ} (h : N ≤ N') (pc Y : ℕ) : midB N pc Y ≤ midB N' pc Y := by
  unfold midB
  exact_mod_cast sum_le_sum (fun p _ => Nat.add_le_add_right (Nat.div_le_div_right h) 1)

/-! ### The U1 tail -/

lemma hcnt_mono {N N' : ℕ} (h : N ≤ N') (p : ℕ) : hcnt N p ≤ hcnt N' p := by
  have hR : (N : ℝ) ≤ N' := by exact_mod_cast h
  have hp : (0 : ℝ) ≤ (p : ℝ) * p := by positivity
  unfold hcnt
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> try omega
  all_goals first
    | (gcongr)
    | (have : (0 : ℝ) ≤ (N' : ℝ) / (p * p) := by positivity
       linarith)
    | norm_num

lemma hcnt_le_main (N p : ℕ) : hcnt N p ≤ 2 * ((N : ℝ) / ((p : ℝ) * p) + 1) := by
  have : (0 : ℝ) ≤ (N : ℝ) / ((p : ℝ) * p) := by positivity
  unfold hcnt; split_ifs <;> linarith

lemma hcnt_le_two {N p : ℕ} (h : Nat.sqrt N < p) : hcnt N p ≤ 2 := by
  have : ¬ p * p ≤ N := by
    have := Nat.lt_succ_sqrt N
    simp only [Nat.succ_eq_add_one] at this
    have h2 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ p * p := Nat.mul_le_mul h h
    omega
  unfold hcnt; rw [if_neg this]; split_ifs <;> norm_num

lemma hcnt_le_one {N p : ℕ} (h : Nat.sqrt (2 * N) < p) : hcnt N p ≤ 1 := by
  have h2 : ¬ p * p ≤ 2 * N := by
    have := Nat.lt_succ_sqrt (2 * N)
    simp only [Nat.succ_eq_add_one] at this
    have h2 : (Nat.sqrt (2 * N) + 1) * (Nat.sqrt (2 * N) + 1) ≤ p * p := Nat.mul_le_mul h h
    omega
  have h1 : ¬ p * p ≤ N := fun h' => h2 (by omega)
  unfold hcnt; rw [if_neg h1, if_neg h2]

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- **The U1 tail (Lemma H)** as computed by the checker. -/
theorem u1Tail_sum_le (N pT Y : ℕ) :
    ∑ p ∈ midP pT Y (fun p => IsU1 p ∧ pT < p), hcnt N p ≤ ((u1TailQ lk N pT Y : ℚ) : ℝ) := by
  set a := max pT (min Y (Nat.sqrt N)) with ha
  set b := max a (min Y (Nat.sqrt (2 * N))) with hb
  set P := midP pT Y (fun p => IsU1 p ∧ pT < p)
  have hsplit : ∑ p ∈ P, hcnt N p = ∑ p ∈ P.filter (· ≤ a), hcnt N p +
      (∑ p ∈ (P.filter (fun p => ¬ p ≤ a)).filter (· ≤ b), hcnt N p +
        ∑ p ∈ (P.filter (fun p => ¬ p ≤ a)).filter (fun p => ¬ p ≤ b), hcnt N p) := by
    rw [sum_filter_add_sum_filter_not, sum_filter_add_sum_filter_not]
  have hA : ∑ p ∈ P.filter (· ≤ a), hcnt N p ≤
      2 * ((N : ℝ) * ((S2Uk lk pT a : ℚ) : ℝ) + ((CUk lk pT a : ℚ) : ℝ)) := by
    refine (sum_le_sum (fun p _ => hcnt_le_main N p)).trans ?_
    rw [← mul_sum]
    gcongr
    have hsub : P.filter (· ≤ a) ⊆ u1In pT a := by
      intro p hp
      simp only [P, midP, u1In, mem_filter, mem_Ioc] at hp ⊢
      exact ⟨⟨hp.1.1.1, hp.2⟩, hp.1.2.2.1⟩
    have := midsum_le_gen _ _ hsub (N : ℝ) 1 (Nat.cast_nonneg N) zero_le_one
    have h1 := S2UK_le hlk pT a
    have h2 := CUK_le hlk pT a
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hB : ∑ p ∈ (P.filter (fun p => ¬ p ≤ a)).filter (· ≤ b), hcnt N p ≤
      2 * ((CUk lk a b : ℚ) : ℝ) := by
    have hsub : (P.filter (fun p => ¬ p ≤ a)).filter (· ≤ b) ⊆ u1In a b := by
      intro p hp
      simp only [P, midP, u1In, mem_filter, mem_Ioc] at hp ⊢
      exact ⟨⟨by omega, hp.2⟩, hp.1.1.2.2.1⟩
    have hle : ∀ p ∈ (P.filter (fun p => ¬ p ≤ a)).filter (· ≤ b), hcnt N p ≤ 2 := by
      intro p hp
      simp only [P, midP, mem_filter, mem_Ioc] at hp
      apply hcnt_le_two
      have : min Y (Nat.sqrt N) < p := by omega
      rcases min_choice Y (Nat.sqrt N) with e | e <;> rw [e] at this <;> omega
    refine (sum_le_sum hle).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have := le_trans (show (((P.filter (fun p => ¬ p ≤ a)).filter (· ≤ b)).card : ℝ) ≤ (u1In a b).card by
      exact_mod_cast card_le_card hsub) (CUK_le hlk a b)
    linarith
  have hC : ∑ p ∈ (P.filter (fun p => ¬ p ≤ a)).filter (fun p => ¬ p ≤ b), hcnt N p ≤
      ((CUk lk b Y : ℚ) : ℝ) := by
    have hsub : (P.filter (fun p => ¬ p ≤ a)).filter (fun p => ¬ p ≤ b) ⊆ u1In b Y := by
      intro p hp
      simp only [P, midP, u1In, mem_filter, mem_Ioc] at hp ⊢
      exact ⟨⟨by omega, hp.1.1.1.2⟩, hp.1.1.2.2.1⟩
    have hle : ∀ p ∈ (P.filter (fun p => ¬ p ≤ a)).filter (fun p => ¬ p ≤ b), hcnt N p ≤ 1 := by
      intro p hp
      simp only [P, midP, mem_filter, mem_Ioc] at hp
      apply hcnt_le_one
      have : min Y (Nat.sqrt (2 * N)) < p := by omega
      rcases min_choice Y (Nat.sqrt (2 * N)) with e | e <;> rw [e] at this <;> omega
    refine (sum_le_sum hle).trans ?_
    rw [sum_const, nsmul_eq_mul, mul_one]
    exact le_trans (by exact_mod_cast card_le_card hsub) (CUK_le hlk b Y)
  rw [hsplit]
  have hq : u1TailQ lk N pT Y = 2 * ((N : ℚ) * S2Uk lk pT a + CUk lk pT a) + 2 * CUk lk a b +
      CUk lk b Y := rfl
  rw [hq]
  push_cast
  linarith

end

/-! ### The Pell tail -/

lemma chainK_eq (G X : ℕ) : ∀ f T, chainK G X f T = chainCnt G X f T
  | 0, _ => rfl
  | f + 1, T => by simp only [chainK, chainCnt, chainK_eq G X f]

lemma pellTermK_eq (N Y m : ℕ) : pellTermK N Y m = pellTerm N Y m := by
  unfold pellTermK pellTerm admBk admB; simp only [chainK_eq]

lemma chainCnt_mono (G X : ℕ) : ∀ f f' T T', f ≤ f' → T ≤ T' → chainCnt G X f T ≤ chainCnt G X f' T'
  | 0, _, _, _, _, _ => by simp [chainCnt]
  | f + 1, f' + 1, T, T', hf, hT => by
    simp only [chainCnt]
    split_ifs with h1 h2 <;> try omega
    have := chainCnt_mono G X f f' (T / G) (T' / G) (by omega) (Nat.div_le_div_right hT)
    omega
  | _ + 1, 0, _, _, hf, _ => by omega

lemma pellTerm_mono {N N' : ℕ} (h : N ≤ N') (Y m : ℕ) : pellTerm N Y m ≤ pellTerm N' Y m := by
  unfold pellTerm
  split_ifs
  · exact chainCnt_mono _ _ _ _ _ _ (by gcongr) (by gcongr)
  · exact le_refl 0

lemma chainCnt_le_one (G X f T : ℕ) (h : T / G < X) : chainCnt G X f T ≤ 1 := by
  rcases f with _ | f
  · simp [chainCnt]
  · simp only [chainCnt]
    split_ifs
    · omega
    · rcases f with _ | f
      · simp [chainCnt]
      · simp only [chainCnt]; rw [if_pos h]

lemma admCnt_add (lo : ℕ) : ∀ a b, admCnt lo (a + b) = admCnt lo a + admCnt (lo + a) b
  | a, 0 => by simp [admCnt]
  | a, b + 1 => by
    rw [← Nat.add_assoc, admCnt, admCnt, admCnt_add lo a b]
    have : lo + (a + b) + 1 = lo + a + b + 1 := by omega
    rw [this]; omega

lemma admCnt_eq_card (lo : ℕ) : ∀ k, admCnt lo k = ((Ioc lo (lo + k)).filter (fun m => admBk m = true)).card
  | 0 => by simp [admCnt]
  | k + 1 => by
    rw [admCnt, admCnt_eq_card lo k]
    have hI : Ioc lo (lo + (k + 1)) = insert (lo + k + 1) (Ioc lo (lo + k)) := by
      ext x; simp only [mem_Ioc, mem_insert]; omega
    rw [hI, filter_insert]
    have hn : lo + k + 1 ∉ Ioc lo (lo + k) := by simp
    cases h : admBk (lo + k + 1)
    · simp
    · rw [if_pos rfl, card_insert_of_notMem (fun hm => hn (mem_filter.mp hm).1)]; simp

lemma admPreOK_spec : ∀ (pre : List ℕ) (i acc : ℕ), admPreOK pre i acc = true →
    acc = admCnt 0 (i * admBlock) → ∀ j < pre.length, pre.getD j 0 = admCnt 0 ((i + j) * admBlock)
  | [], _, _, _, _, j, hj => by simp at hj
  | c :: cs, i, acc, h, hacc, j, hj => by
    simp only [admPreOK, Bool.and_eq_true, Nat.beq_eq] at h
    rcases j with _ | j
    · simp [h.1, hacc]
    · have := admPreOK_spec cs (i + 1) _ h.2 (by
        rw [hacc, show (i + 1) * admBlock = i * admBlock + admBlock by ring, admCnt_add]; simp)
        j (by simpa using hj)
      simp only [List.getD_cons_succ]
      rw [this]; congr 2; ring

lemma admUpTo_eq {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) {M : ℕ}
    (hM : M / admBlock < pre.length) : admUpTo pre M = admCnt 0 M := by
  unfold admUpTo
  rw [admPreOK_spec pre 0 0 hpre (by simp [admCnt]) _ hM]
  simp only [zero_add]
  have := admCnt_add 0 (M / admBlock * admBlock) (M % admBlock)
  rw [zero_add] at this
  rw [← this, show M / admBlock * admBlock + M % admBlock = M by
    rw [mul_comm]; exact Nat.div_add_mod M admBlock]

lemma pellSum_eq (N Y : ℕ) : ∀ K, (pellSum N Y K : ℝ) = ∑ m ∈ Icc 1 K, (pellTerm N Y m : ℝ)
  | 0 => by simp [pellSum]
  | K + 1 => by
    rw [pellSum, Nat.cast_add, pellSum_eq N Y K, pellTermK_eq]
    rw [show Icc 1 (K + 1) = insert (K + 1) (Icc 1 K) by ext x; simp only [mem_Icc, mem_insert]; omega,
      sum_insert (by simp)]
    ring

/-- **The Pell tail** as computed by the checker. -/
theorem pell_le {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) (N Y K s : ℕ)
    (h : pellQ pre N Y K = some s) :
    ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N Y m : ℝ) ≤ s := by
  unfold pellQ at h
  set M := (N ^ 2 + 1) / (Y + 1) ^ 2 with hM
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hKM, hlen, hcond⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  have hKlen : K / admBlock < pre.length := lt_of_le_of_lt (Nat.div_le_div_right hKM) hlen
  rw [admUpTo_eq hpre hlen, admUpTo_eq hpre hKlen]
  have hsplit : Icc 1 M = Icc 1 K ∪ Ioc K M := by
    ext x; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  rw [hsplit, sum_union (by rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  push_cast
  rw [← pellSum_eq]
  have hrest : ∑ m ∈ Ioc K M, (pellTerm N Y m : ℝ) ≤ ((admCnt 0 M - admCnt 0 K : ℕ) : ℝ) := by
    have hcnt : admCnt 0 M - admCnt 0 K = ((Ioc K M).filter (fun m => admBk m = true)).card := by
      have := admCnt_add 0 K (M - K)
      rw [show 0 + K = K by simp, show K + (M - K) = M by omega] at this
      rw [this, Nat.add_sub_cancel_left, admCnt_eq_card, show K + (M - K) = M by omega]
    rw [hcnt, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_le_sum
    intro m hm
    simp only [mem_Ioc] at hm
    rw [← pellTermK_eq]
    unfold pellTermK
    split_ifs with ha
    · rcases hcond with hKM' | hcond
      · omega
      · have hle : N ^ 2 / max 9 (4 * m) < m * (Y + 1) ^ 2 - 1 := by
          have e1 : N ^ 2 / max 9 (4 * m) ≤ N ^ 2 / max 9 (4 * (K + 1)) :=
            Nat.div_le_div_left (max_le_max le_rfl (by omega)) (by positivity)
          have e2 : (K + 1) * (Y + 1) ^ 2 ≤ m * (Y + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
          omega
        have := chainCnt_le_one (max 9 (4 * m)) (m * (Y + 1) ^ 2 - 1) (N ^ 2 + 1) (N ^ 2) hle
        rw [chainK_eq]; exact_mod_cast this
    · simp
  linarith

lemma tailB_mono {N N' : ℕ} (h : N ≤ N') (pT Y : ℕ) : tailB N pT Y ≤ tailB N' pT Y := by
  unfold tailB
  apply add_le_add
  · exact sum_le_sum (fun p _ => hcnt_mono h p)
  · calc ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N Y m : ℝ)
        ≤ ∑ m ∈ Icc 1 ((N ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N' Y m : ℝ) :=
          sum_le_sum (fun m _ => by exact_mod_cast pellTerm_mono h Y m)
      _ ≤ ∑ m ∈ Icc 1 ((N' ^ 2 + 1) / (Y + 1) ^ 2), (pellTerm N' Y m : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.div_le_div_right (by gcongr)))
            (fun _ _ _ => by positivity)

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- **The tail** as computed by the checker. -/
theorem tailB_le {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) (N pT Y K : ℕ) (t : ℚ)
    (h : tailQ lk pre N pT Y K = some t) : tailB N pT Y ≤ (t : ℝ) := by
  cases hp : pellQ pre N Y K with
  | none => simp [tailQ, hp] at h
  | some s =>
    simp [tailQ, hp] at h
    subst h
    unfold tailB
    have h1 := u1Tail_sum_le hlk N pT Y
    have h2 := pell_le hpre N Y K s hp
    push_cast
    linarith

end

end Erdos848
