import Erdos848.Counting

/-!
# Phase 3: inclusion–exclusion for small primes

Step 1: a residue class mod `Q` has between `N/Q - 1` and `N/Q + 1` elements in `[1,N]`;
a union of `K` residue classes has between `K·N/Q - K` and `K·N/Q + K` elements.
-/

namespace Erdos848

open Finset

/-- A residue class mod `Q` (with `r < Q`) has at least `⌊N/Q⌋` elements in `[1,N]`. -/
lemma card_mod_eq_ge (N Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    N / Q ≤ ((Icc 1 N).filter (fun a => a % Q = r)).card := by
  -- block i ↦ the element of (iQ, iQ+Q] congruent to r
  let f : ℕ → ℕ := fun i => if r = 0 then (i + 1) * Q else i * Q + r
  calc N / Q = (range (N / Q)).card := (card_range _).symm
    _ ≤ ((Icc 1 N).filter (fun a => a % Q = r)).card := by
      apply card_le_card_of_injOn f
      · intro i hi
        simp only [coe_range, Set.mem_Iio] at hi
        have hiQ : (i + 1) * Q ≤ N := by
          have := (Nat.lt_div_iff_mul_lt hQ).mp hi
          calc (i + 1) * Q ≤ N / Q * Q := Nat.mul_le_mul_right Q hi
            _ ≤ N := Nat.div_mul_le_self N Q
        simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc, f]
        split_ifs with h0
        · refine ⟨⟨by nlinarith, hiQ⟩, ?_⟩
          rw [h0]; exact Nat.mul_mod_left _ _
        · refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      · intro i _ j _ hij
        simp only [f] at hij
        split_ifs at hij with h0
        · exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right hQ hij)
        · have : i * Q = j * Q := by omega
          exact Nat.eq_of_mul_eq_mul_right hQ this

/-- Real-valued two-sided bound for a residue class. -/
lemma card_mod_eq_real (N Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    |(((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q| ≤ 1 := by
  have h1 := card_mod_eq_le N Q r
  have h2 := card_mod_eq_ge N Q r hQ hr
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have e1 : ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) / Q := Nat.cast_div_le
  have e2 : (N : ℝ) / Q < ((N / Q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hQ']
    have := Nat.lt_div_mul_add hQ (a := N)
    exact_mod_cast (by nlinarith [Nat.div_add_mod N Q, Nat.mod_lt N hQ] : N < (N / Q + 1) * Q)
  rw [abs_le]
  constructor
  · have : ((N / Q : ℕ) : ℝ) ≤ (((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) := by exact_mod_cast h2
    linarith
  · have : (((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) ≤ ((N / Q : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith

/-- A union of residue classes `D ⊆ [0,Q)` meets `[1,N]` in `|D|·N/Q ± |D|` points. -/
lemma card_mod_mem_real (N Q : ℕ) (hQ : 0 < Q) (D : Finset ℕ) (hD : ∀ r ∈ D, r < Q) :
    |(((Icc 1 N).filter (fun a => a % Q ∈ D)).card : ℝ) - D.card * ((N : ℝ) / Q)| ≤ D.card := by
  have hsplit : ((Icc 1 N).filter (fun a => a % Q ∈ D)).card =
      ∑ r ∈ D, ((Icc 1 N).filter (fun a => a % Q = r)).card := by
    rw [← card_biUnion]
    · congr 1; ext a; simp only [mem_filter, mem_biUnion]
      constructor
      · rintro ⟨ha, hD'⟩; exact ⟨a % Q, hD', ha, rfl⟩
      · rintro ⟨r, hr, ha, rfl⟩; exact ⟨ha, hr⟩
    · intro r _ s _ hrs
      rw [Function.onFun, disjoint_left]
      intro a ha hb
      simp only [mem_filter] at ha hb
      exact hrs (ha.2.symm.trans hb.2)
  rw [hsplit]
  push_cast
  calc |∑ r ∈ D, ((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ)) - D.card * ((N : ℝ) / Q)|
      = |∑ r ∈ D, ((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q)| := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ D, |((((Icc 1 N).filter (fun a => a % Q = r)).card : ℝ) - (N : ℝ) / Q)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ D, (1 : ℝ) := sum_le_sum (fun r hr => card_mod_eq_real N Q r hQ (hD r hr))
    _ = D.card := by simp

/-! ### Step 2: counting residues by CRT -/

section CRT
variable (q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ)

/-- The combined modulus `q · ∏_{p ∈ T} m p`. -/
def bigMod (T : Finset ℕ) : ℕ := q * ∏ p ∈ T, m p

/-- Residues mod `bigMod T` satisfying all the conditions. -/
def resSet (T : Finset ℕ) : Finset ℕ :=
  (range (bigMod q m T)).filter (fun r => r % q = t ∧ ∀ p ∈ T, r % m p ∈ Rs p)

variable {q t m Rs}

lemma mod_bigMod_mod_q (T : Finset ℕ) (a : ℕ) : a % bigMod q m T % q = a % q :=
  Nat.mod_mod_of_dvd a (dvd_mul_right q _)

lemma mod_bigMod_mod_m {T : Finset ℕ} {p : ℕ} (hp : p ∈ T) (a : ℕ) :
    a % bigMod q m T % m p = a % m p :=
  Nat.mod_mod_of_dvd a (dvd_mul_of_dvd_right (dvd_prod_of_mem m hp) q)

/-- The conditions only depend on `a mod bigMod T`. -/
lemma cond_iff_resSet (T : Finset ℕ) (hq : 0 < q) (hm : ∀ p ∈ T, 0 < m p) (a : ℕ) :
    (a % q = t ∧ ∀ p ∈ T, a % m p ∈ Rs p) ↔ a % bigMod q m T ∈ resSet q t m Rs T := by
  have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p hp))
  simp only [resSet, mem_filter, mem_range, Nat.mod_lt _ hpos, true_and, mod_bigMod_mod_q]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp => by rw [mod_bigMod_mod_m hp]; exact h2 p hp⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp => by have := h2 p hp; rwa [mod_bigMod_mod_m hp] at this⟩

/-- **CRT count.** If the moduli `m p` (`p ∈ T`) are pairwise coprime and coprime to `q`, `t < q`
and `Rs p ⊆ [0, m p)`, then there are exactly `∏ |Rs p|` admissible residues. -/
theorem card_resSet (T : Finset ℕ) (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ T, 0 < m p) (hR : ∀ p ∈ T, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ T, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (resSet q t m Rs T).card = ∏ p ∈ T, (Rs p).card := by
  induction T using Finset.induction_on with
  | empty =>
    have : resSet q t m Rs ∅ = {t} := by
      ext r
      simp only [resSet, bigMod, prod_empty, mul_one, mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hr, h, -⟩; rwa [Nat.mod_eq_of_lt hr] at h
      · rintro rfl; exact ⟨ht, Nat.mod_eq_of_lt ht, fun p hp => absurd hp (Finset.notMem_empty p)⟩
    rw [this]; simp
  | insert p T hpT ih =>
    have ih' := ih (fun p' hp' => hm p' (mem_insert_of_mem hp'))
      (fun p' hp' => hR p' (mem_insert_of_mem hp')) (fun p' hp' => hcopq p' (mem_insert_of_mem hp'))
      (fun a ha b hb hab => hcop a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
    rw [prod_insert hpT, ← ih']
    set Q' := bigMod q m T
    have hQ'pos : 0 < Q' := Nat.mul_pos hq (prod_pos (fun p' hp' => hm p' (mem_insert_of_mem hp')))
    have hmp : 0 < m p := hm p (mem_insert_self p T)
    have hcopQ : Nat.Coprime Q' (m p) := by
      apply Nat.coprime_mul_iff_left.mpr
      refine ⟨hcopq p (mem_insert_self p T), ?_⟩
      rw [Nat.coprime_prod_left_iff]
      intro p' hp'
      exact hcop p' (mem_insert_of_mem hp') p (mem_insert_self p T) (fun h => hpT (h ▸ hp'))
    have hbig : bigMod q m (insert p T) = Q' * m p := by
      simp only [bigMod, Q', prod_insert hpT]; ring
    -- bijection r ↦ (r % Q', r % m p)
    rw [mul_comm, ← card_product]
    apply card_bij (fun r _ => (r % Q', r % m p))
    · intro r hr
      simp only [resSet, mem_filter, mem_range, hbig] at hr
      simp only [mem_product, resSet, mem_filter, mem_range]
      refine ⟨⟨Nat.mod_lt _ hQ'pos, ?_, ?_⟩, ?_⟩
      · rw [mod_bigMod_mod_q]; exact hr.2.1
      · intro p' hp'; rw [mod_bigMod_mod_m hp']; exact hr.2.2 p' (mem_insert_of_mem hp')
      · exact hr.2.2 p (mem_insert_self p T)
    · intro r hr r' hr' h
      simp only [Prod.mk.injEq] at h
      simp only [resSet, mem_filter, mem_range, hbig] at hr hr'
      have := (Nat.modEq_and_modEq_iff_modEq_mul hcopQ).mp ⟨h.1, h.2⟩
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt hr'.1] at this
    · intro ⟨u, v⟩ huv
      simp only [mem_product, resSet, mem_filter, mem_range] at huv
      obtain ⟨⟨hu, hut, huT⟩, hv⟩ := huv
      have hvm : v < m p := hR p (mem_insert_self p T) v hv
      let k := Nat.chineseRemainder hcopQ u v
      refine ⟨k.1 % (Q' * m p), ?_, ?_⟩
      · simp only [resSet, mem_filter, mem_range, hbig]
        have hk1 : k.1 % (Q' * m p) % Q' = u := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right Q' (m p))]
          have := k.2.1; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hu]
        have hk2 : k.1 % (Q' * m p) % m p = v := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (m p) Q')]
          have := k.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hvm]
        refine ⟨Nat.mod_lt _ (Nat.mul_pos hQ'pos hmp), ?_, ?_⟩
        · rw [← mod_bigMod_mod_q (m := m) T, hk1]; exact hut
        · intro p' hp'
          rcases mem_insert.mp hp' with rfl | hp''
          · rw [hk2]; exact hv
          · rw [← mod_bigMod_mod_m (q := q) hp'', hk1]; exact huT p' hp''
      · simp only [Prod.mk.injEq]
        constructor
        · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right Q' (m p))]
          have := k.2.1; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hu]
        · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (m p) Q')]
          have := k.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hvm]

end CRT

/-! ### Step 3: the inclusion–exclusion bound -/

/-- Algebraic identity: `∑_{∅ ≠ T ⊆ P} (-1)^{|T|+1} ∏_{T} x = 1 - ∏_{P} (1 - x)`. -/
lemma sum_powerset_alt (P : Finset ℕ) (x : ℕ → ℝ) :
    ∑ T ∈ P.powerset.filter (·.Nonempty), (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, x p =
      1 - ∏ p ∈ P, (1 - x p) := by
  have h := Finset.prod_add (fun p => -x p) (fun _ => (1 : ℝ)) P
  simp only [prod_const_one, mul_one] at h
  have h' : ∏ p ∈ P, (1 - x p) = ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
    rw [show (fun p => 1 - x p) = (fun p => -x p + 1) by ext; ring, h]
    apply sum_congr rfl; intro T _
    rw [prod_neg]
  rw [h', ← sum_filter_add_sum_filter_not P.powerset (·.Nonempty)]
  have hempty : ∑ T ∈ P.powerset.filter (fun T => ¬ T.Nonempty), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p = 1 := by
    rw [show P.powerset.filter (fun T => ¬ T.Nonempty) = {∅} by
      ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨empty_subset _, rfl⟩]
    simp
  rw [hempty]
  have : ∀ T ∈ P.powerset.filter (·.Nonempty),
      (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, x p = -((-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
    intro T _; ring
  rw [sum_congr rfl this, sum_neg_distrib]; ring

/-- `∑_{∅ ≠ T ⊆ P} ∏_{T} y = ∏_{P} (1 + y) - 1`. -/
lemma sum_powerset_prod (P : Finset ℕ) (y : ℕ → ℝ) :
    ∑ T ∈ P.powerset.filter (·.Nonempty), ∏ p ∈ T, y p = ∏ p ∈ P, (1 + y p) - 1 := by
  have h := Finset.prod_add y (fun _ => (1 : ℝ)) P
  simp only [prod_const_one, mul_one] at h
  rw [show (fun p => 1 + y p) = (fun p => y p + 1) by ext; ring, h,
    ← sum_filter_add_sum_filter_not P.powerset (·.Nonempty)]
  rw [show P.powerset.filter (fun T => ¬ T.Nonempty) = {∅} by
      ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨empty_subset _, rfl⟩]
  simp

/-- **Inclusion–exclusion, two-sided.** Under the CRT hypotheses,
`#{a ∈ [1,N] : a ≡ t (q), ∃ p ∈ P, a mod m p ∈ Rs p}` differs from
`(N/q)(1 - ∏_P (1 - |Rs p|/m p))` by at most `∏_P (1 + |Rs p|) - 1`. -/
theorem card_union_abs (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    |(((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) -
      (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p))| ≤
        ∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1 := by
  classical
  let S : ℕ → Finset ℕ := fun p => (Icc 1 N).filter (fun a => a % q = t ∧ a % m p ∈ Rs p)
  have hunion : (Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p) = P.biUnion S := by
    ext a; simp only [mem_filter, mem_biUnion, S]
    constructor
    · rintro ⟨ha, h1, p, hp, h2⟩; exact ⟨p, hp, ha, h1, h2⟩
    · rintro ⟨p, hp, ha, h1, h2⟩; exact ⟨ha, h1, p, hp, h2⟩
  -- intersections are periodic sets mod bigMod T
  have hinter : ∀ T (hT : T.Nonempty), T ⊆ P →
      T.inf' hT S = (Icc 1 N).filter (fun a => a % bigMod q m T ∈ resSet q t m Rs T) := by
    intro T hT hTP
    ext a
    rw [mem_inf']
    simp only [S, mem_filter]
    rw [← cond_iff_resSet T hq (fun p hp => hm p (hTP hp))]
    constructor
    · intro h
      obtain ⟨p0, hp0⟩ := hT
      exact ⟨(h p0 hp0).1, (h p0 hp0).2.1, fun p hp => (h p hp).2.2⟩
    · rintro ⟨ha, h1, h2⟩ p hp; exact ⟨ha, h1, h2 p hp⟩
  -- per-T estimate
  have hT : ∀ T ∈ P.powerset.filter (·.Nonempty),
      |(-1 : ℝ) ^ (T.card + 1) * (((Icc 1 N).filter
          (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ) -
        (-1 : ℝ) ^ (T.card + 1) * ((N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p)| ≤
          ∏ p ∈ T, ((Rs p).card : ℝ) := by
    intro T hTm
    simp only [mem_filter, mem_powerset] at hTm
    have hTP := hTm.1
    have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p (hTP hp)))
    have hD : ∀ r ∈ resSet q t m Rs T, r < bigMod q m T := by
      intro r hr; simp only [resSet, mem_filter, mem_range] at hr; exact hr.1
    have hc := card_mod_mem_real N (bigMod q m T) hpos (resSet q t m Rs T) hD
    have hcard := card_resSet T hq ht (fun p hp => hm p (hTP hp)) (fun p hp => hR p (hTP hp))
      (fun p hp => hcopq p (hTP hp)) (fun p hp p' hp' => hcop p (hTP hp) p' (hTP hp'))
    rw [hcard] at hc
    have hbigR : ((bigMod q m T : ℕ) : ℝ) = (q : ℝ) * ∏ p ∈ T, (m p : ℝ) := by
      simp only [bigMod, Nat.cast_mul, Nat.cast_prod]
    have hmain : ((∏ p ∈ T, (Rs p).card : ℕ) : ℝ) * ((N : ℝ) / ((bigMod q m T : ℕ) : ℝ)) =
        (N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p := by
      rw [hbigR, Nat.cast_prod, prod_div_distrib]; ring
    rw [hmain, Nat.cast_prod] at hc
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hc
  rw [hunion]
  have hIE := inclusion_exclusion_card_biUnion P S
  have hIE' : ((P.biUnion S).card : ℝ) = ∑ T ∈ P.powerset.filter (·.Nonempty),
      (-1 : ℝ) ^ (T.card + 1) * (((Icc 1 N).filter
          (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIE
    simp only [Int.cast_natCast] at this
    rw [this]; push_cast
    rw [← sum_coe_sort (P.powerset.filter (·.Nonempty))]
    apply sum_congr rfl
    intro T _
    have hTP : T.1 ⊆ P := (mem_powerset.mp (mem_filter.mp T.2).1)
    rw [hinter T.1 (mem_filter.mp T.2).2 hTP]
  have hmainE : (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) =
      ∑ T ∈ P.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (T.card + 1) * ((N : ℝ) / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p) := by
    rw [← sum_powerset_alt, mul_sum]; apply sum_congr rfl; intro T _; ring
  rw [hIE', hmainE, ← sum_sub_distrib, ← sum_powerset_prod]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hT)

/-- **Inclusion–exclusion bound** (upper half of `card_union_abs`). -/
theorem card_union_le (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) ≤
      (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) +
        (∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1) := by
  have := card_union_abs N q t m Rs P hq ht hm hR hcopq hcop
  rw [abs_le] at this; linarith [this.2]

/-- Lower half of `card_union_abs`. -/
theorem card_union_ge (N q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p')) :
    (N : ℝ) / q * (1 - ∏ p ∈ P, (1 - ((Rs p).card : ℝ) / m p)) -
        (∏ p ∈ P, (1 + ((Rs p).card : ℝ)) - 1) ≤
      (((Icc 1 N).filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) := by
  have := card_union_abs N q t m Rs P hq ht hm hR hcopq hcop
  rw [abs_le] at this; linarith [this.1]

end Erdos848
