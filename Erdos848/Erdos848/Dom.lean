import Erdos848.InclExcl
import Erdos848.Bonf
import Erdos848.LemmaC

/-!
# Phase 9.1: counting on general domains

A finite set `D` is a *good domain* with length `L` and error `μ` for the moduli `Qok` if every
residue class mod such a `Q` has between `L/Q - μ` and `L/Q + μ` elements of `D`.  Intervals
`[m, N]` are good domains for all moduli (`goodDom_Icc`).  On a good domain we sieve one residue
class by a set of primes with Bonferroni truncation at odd depth (`dom_bonf_le`).
-/

namespace Erdos848

open Finset

/-- Every class mod `Q` (with `Qok Q`) has `L/Q ± μ` elements of `D`. -/
def GoodDom (D : Finset ℕ) (L μ : ℝ) (Qok : ℕ → Prop) : Prop :=
  ∀ Q r, 0 < Q → Qok Q → r < Q → |((D.filter (fun a => a % Q = r)).card : ℝ) - L / Q| ≤ μ

/-- A union of classes `E ⊆ [0, Q)` has `|E|·L/Q ± |E| μ` elements of a good domain. -/
lemma GoodDom.mem_real {D : Finset ℕ} {L μ : ℝ} {Qok : ℕ → Prop} (hD : GoodDom D L μ Qok)
    {Q : ℕ} (hQ : 0 < Q) (hok : Qok Q) (E : Finset ℕ) (hE : ∀ r ∈ E, r < Q) :
    |((D.filter (fun a => a % Q ∈ E)).card : ℝ) - E.card * (L / Q)| ≤ E.card * μ := by
  have hsplit : (D.filter (fun a => a % Q ∈ E)).card =
      ∑ r ∈ E, (D.filter (fun a => a % Q = r)).card := by
    rw [← card_biUnion]
    · congr 1; ext a; simp only [mem_filter, mem_biUnion]
      constructor
      · rintro ⟨ha, hE'⟩; exact ⟨a % Q, hE', ha, rfl⟩
      · rintro ⟨r, hr, ha, rfl⟩; exact ⟨ha, hr⟩
    · intro r _ s _ hrs
      rw [Function.onFun, disjoint_left]
      intro a ha hb
      simp only [mem_filter] at ha hb
      exact hrs (ha.2.symm.trans hb.2)
  rw [hsplit]
  push_cast
  calc |∑ r ∈ E, (((D.filter (fun a => a % Q = r)).card : ℝ)) - E.card * (L / Q)|
      = |∑ r ∈ E, (((D.filter (fun a => a % Q = r)).card : ℝ) - L / Q)| := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ E, |(((D.filter (fun a => a % Q = r)).card : ℝ) - L / Q)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ E, μ := sum_le_sum (fun r hr => hD Q r hQ hok (hE r hr))
    _ = E.card * μ := by simp

/-! ### Intervals -/

/-- Shifting a residue condition. -/
lemma add_mod_eq_iff {b c Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) :
    (b + c) % Q = r ↔ b % Q = (r + Q - c % Q) % Q := by
  have hu := Nat.mod_lt b hQ
  have hw := Nat.mod_lt c hQ
  rw [Nat.add_mod]
  set u := b % Q
  set w := c % Q
  have e1 : (u + w) % Q = if u + w < Q then u + w else u + w - Q := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have e2 : (r + Q - w) % Q = if r + Q - w < Q then r + Q - w else r - w := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  rw [e1, e2]
  split_ifs <;> omega

/-- An interval `[m, N]` (`1 ≤ m ≤ N + 1`) is a good domain of length `N + 1 - m`, error `1`. -/
theorem goodDom_Icc (m N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N + 1) :
    GoodDom (Icc m N) ((N + 1 - m : ℕ) : ℝ) 1 (fun _ => True) := by
  intro Q r hQ _ hr
  set L := N + 1 - m
  set c := m - 1
  set r' := (r + Q - c % Q) % Q
  have hr' : r' < Q := Nat.mod_lt _ hQ
  -- `a ↦ a - c` maps the class `r` of `[m, N]` onto the class `r'` of `[1, L]`
  have hcard : ((Icc m N).filter (fun a => a % Q = r)).card =
      ((Icc 1 L).filter (fun b => b % Q = r')).card := by
    apply card_nbij' (fun a => a - c) (fun b => b + c)
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have : a - c + c = a := by omega
      rw [← (add_mod_eq_iff hQ hr), this]; exact ha.2
    · intro b hb
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at hb ⊢
      exact ⟨⟨by omega, by omega⟩, (add_mod_eq_iff hQ hr).mpr hb.2⟩
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc] at ha
      simp only; omega
    · intro b _; simp only; omega
  rw [hcard]
  exact card_mod_eq_real L Q r' hQ hr'

/-! ### Sieving one class of a good domain (Bonferroni) -/

/-- The truncated error count `∑_{∅ ≠ T ⊆ P, |T| ≤ d} ∏_{p ∈ T} x p`. -/
noncomputable def truncErr (P : Finset ℕ) (x : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d), ∏ p ∈ T, x p

/-- The truncated main term, written through `altE`. -/
lemma trunc_main_eq (P : Finset ℕ) (v : ℕ → ℝ) (d : ℕ) :
    ∑ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d), (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, v p =
      1 - altE P v d := by
  unfold altE
  have hsplit := sum_filter_add_sum_filter_not (P.powerset.filter (fun T => T.card ≤ d))
    (fun T => T.Nonempty) (fun T => (-1 : ℝ) ^ T.card * ∏ p ∈ T, v p)
  have hempty : (P.powerset.filter (fun T => T.card ≤ d)).filter (fun T => ¬ T.Nonempty) = {∅} := by
    ext T; simp only [mem_filter, mem_powerset, not_nonempty_iff_eq_empty, mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨⟨empty_subset _, by simp⟩, rfl⟩
  rw [hempty, sum_singleton, card_empty, pow_zero, prod_empty, mul_one, filter_filter] at hsplit
  have hset : (P.powerset.filter (fun T => T.card ≤ d ∧ T.Nonempty)) =
      P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d) := by
    apply filter_congr; intro T _; exact and_comm
  rw [hset] at hsplit
  rw [← hsplit]
  have : ∀ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      (-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, v p = -((-1 : ℝ) ^ T.card * ∏ p ∈ T, v p) := by
    intro T _; ring
  rw [sum_congr rfl this, sum_neg_distrib]; ring

/-- **Bonferroni sieve on a good domain.**  For odd `d`, the elements of the class `t` mod `q`
of `D` lying in some `R_p` mod `m p` (`p ∈ P`) number at most
`(L/q)(1 - E_d) + μ · ∑_{∅≠T, |T|≤d} ∏ |R_p|`. -/
theorem dom_bonf_le {D : Finset ℕ} {L μ : ℝ} {Qok : ℕ → Prop} (hD : GoodDom D L μ Qok)
    (q t : ℕ) (m : ℕ → ℕ) (Rs : ℕ → Finset ℕ) (P : Finset ℕ) (d : ℕ) (hd : Odd d)
    (hq : 0 < q) (ht : t < q)
    (hm : ∀ p ∈ P, 0 < m p) (hR : ∀ p ∈ P, ∀ r ∈ Rs p, r < m p)
    (hcopq : ∀ p ∈ P, Nat.Coprime q (m p))
    (hcop : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Nat.Coprime (m p) (m p'))
    (hok : ∀ T ⊆ P, Qok (bigMod q m T)) :
    ((D.filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)).card : ℝ) ≤
      L / q * (1 - altE P (fun p => ((Rs p).card : ℝ) / m p) d) +
        μ * truncErr P (fun p => ((Rs p).card : ℝ)) d := by
  classical
  let S : ℕ → Finset ℕ := fun p => D.filter (fun a => a % q = t ∧ a % m p ∈ Rs p)
  have hunion : D.filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p) = P.biUnion S := by
    ext a; simp only [mem_filter, mem_biUnion, S]
    constructor
    · rintro ⟨ha, h1, p, hp, h2⟩; exact ⟨p, hp, ha, h1, h2⟩
    · rintro ⟨p, hp, ha, h1, h2⟩; exact ⟨ha, h1, p, hp, h2⟩
  have hB := bonferroni_odd P S d hd
  rw [← hunion] at hB
  set U := D.filter (fun a => a % q = t ∧ ∃ p ∈ P, a % m p ∈ Rs p)
  -- the intersections are periodic sets mod `bigMod T`
  have hinter : ∀ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      U.filter (fun x => ∀ i ∈ T, x ∈ S i) =
        D.filter (fun a => a % bigMod q m T ∈ resSet q t m Rs T) := by
    intro T hT
    simp only [mem_filter, mem_powerset] at hT
    obtain ⟨hTP, ⟨p0, hp0⟩, -⟩ := hT
    ext a
    simp only [U, S, mem_filter]
    rw [← cond_iff_resSet T hq (fun p hp => hm p (hTP hp))]
    constructor
    · rintro ⟨⟨ha, h1, -⟩, h⟩; exact ⟨ha, h1, fun p hp => (h p hp).2.2⟩
    · rintro ⟨ha, h1, h2⟩
      exact ⟨⟨ha, h1, p0, hTP hp0, h2 p0 hp0⟩, fun p hp => ⟨ha, h1, h2 p hp⟩⟩
  -- per-term estimate
  have hterm : ∀ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      (-1 : ℝ) ^ (T.card + 1) * ((U.filter (fun x => ∀ i ∈ T, x ∈ S i)).card : ℝ) ≤
        (-1 : ℝ) ^ (T.card + 1) * (L / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p) +
          μ * ∏ p ∈ T, ((Rs p).card : ℝ) := by
    intro T hT
    have hTP := (mem_powerset.mp (mem_filter.mp hT).1)
    rw [hinter T hT]
    have hpos : 0 < bigMod q m T := Nat.mul_pos hq (prod_pos (fun p hp => hm p (hTP hp)))
    have hE : ∀ r ∈ resSet q t m Rs T, r < bigMod q m T := by
      intro r hr; simp only [resSet, mem_filter, mem_range] at hr; exact hr.1
    have hc := hD.mem_real hpos (hok T hTP) (resSet q t m Rs T) hE
    have hcard := card_resSet T hq ht (fun p hp => hm p (hTP hp)) (fun p hp => hR p (hTP hp))
      (fun p hp => hcopq p (hTP hp)) (fun p hp p' hp' => hcop p (hTP hp) p' (hTP hp'))
    rw [hcard] at hc
    have hbigR : ((bigMod q m T : ℕ) : ℝ) = (q : ℝ) * ∏ p ∈ T, (m p : ℝ) := by
      simp only [bigMod, Nat.cast_mul, Nat.cast_prod]
    have hmain : ((∏ p ∈ T, (Rs p).card : ℕ) : ℝ) * (L / ((bigMod q m T : ℕ) : ℝ)) =
        L / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p := by
      rw [hbigR, prod_div_distrib]; push_cast; ring
    rw [hmain] at hc
    push_cast at hc
    set X := ((D.filter (fun a => a % bigMod q m T ∈ resSet q t m Rs T)).card : ℝ)
    set M := L / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p
    set E := ∏ p ∈ T, ((Rs p).card : ℝ)
    have hsign : (-1 : ℝ) ^ (T.card + 1) * (X - M) ≤ |X - M| := by
      rcases neg_one_pow_eq_or ℝ (T.card + 1) with h | h <;> rw [h]
      · rw [one_mul]; exact le_abs_self _
      · rw [neg_one_mul]; exact neg_le_abs _
    have : (-1 : ℝ) ^ (T.card + 1) * X = (-1 : ℝ) ^ (T.card + 1) * M + (-1 : ℝ) ^ (T.card + 1) * (X - M) := by
      ring
    rw [this]
    have hE' : E * μ = μ * E := mul_comm _ _
    linarith
  -- assemble
  have hBR : (U.card : ℝ) ≤ ∑ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      (-1 : ℝ) ^ (T.card + 1) * ((U.filter (fun x => ∀ i ∈ T, x ∈ S i)).card : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (rfl : ((U.card : ℤ)) = U.card)
    exact_mod_cast hB
  refine hBR.trans ((sum_le_sum hterm).trans (le_of_eq ?_))
  rw [sum_add_distrib, ← mul_sum, truncErr]
  congr 1
  have h1 : ∀ T ∈ P.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ d),
      (-1 : ℝ) ^ (T.card + 1) * (L / q * ∏ p ∈ T, ((Rs p).card : ℝ) / m p) =
        L / q * ((-1 : ℝ) ^ (T.card + 1) * ∏ p ∈ T, ((Rs p).card : ℝ) / m p) := by
    intro T _; ring
  rw [sum_congr rfl h1, ← mul_sum, trunc_main_eq]

/-! ### The full single-class sieve on a good domain -/

lemma truncErr_mono (P : Finset ℕ) {x y : ℕ → ℝ} (h0 : ∀ p ∈ P, 0 ≤ x p) (hxy : ∀ p ∈ P, x p ≤ y p)
    (d : ℕ) : truncErr P x d ≤ truncErr P y d := by
  unfold truncErr
  apply sum_le_sum
  intro T hT
  have hTP := mem_powerset.mp (mem_filter.mp hT).1
  exact prod_le_prod₀ (fun p hp => h0 p (hTP hp)) (fun p hp => hxy p (hTP hp))

lemma truncErr_nonneg (P : Finset ℕ) {x : ℕ → ℝ} (h0 : ∀ p ∈ P, 0 ≤ x p) (d : ℕ) :
    0 ≤ truncErr P x d := by
  unfold truncErr
  apply sum_nonneg
  intro T hT
  have hTP := mem_powerset.mp (mem_filter.mp hT).1
  exact prod_nonneg (fun p hp => h0 p (hTP hp))

/-- One prime, as the case `P = {p}`, `d = 1` of `dom_bonf_le`. -/
lemma dom_single_le {D : Finset ℕ} {L μ : ℝ} {Qok : ℕ → Prop} (hD : GoodDom D L μ Qok)
    (q t p : ℕ) (R : Finset ℕ) (hq : 0 < q) (ht : t < q) (hp : 0 < p) (hR : R ⊆ range (p * p))
    (hcop : Nat.Coprime q p) (hok : Qok q) (hok' : Qok (q * (p * p))) :
    ((D.filter (fun a => a % q = t ∧ a % (p * p) ∈ R)).card : ℝ) ≤
      R.card * (L / q / (p * p)) + μ * R.card := by
  have h := dom_bonf_le hD q t (fun p => p * p) (fun _ => R) {p} 1 odd_one hq ht
    (by simp [hp.ne']) (fun p' hp' r hr => by
      rw [mem_singleton] at hp'; subst hp'; exact mem_range.mp (hR hr))
    (fun p' hp' => by rw [mem_singleton] at hp'; subst hp'; exact Nat.Coprime.mul_right hcop hcop)
    (fun p₁ h₁ p₂ h₂ hne => by rw [mem_singleton] at h₁ h₂; exact absurd (h₁.trans h₂.symm) hne)
    (fun T hT => by
      rcases subset_singleton_iff.mp hT with rfl | rfl
      · simpa [bigMod] using hok
      · simpa [bigMod] using hok')
  have hset : D.filter (fun a => a % q = t ∧ ∃ p' ∈ ({p} : Finset ℕ), a % (p' * p') ∈ R) =
      D.filter (fun a => a % q = t ∧ a % (p * p) ∈ R) := by
    apply filter_congr; intro a _; simp
  rw [hset] at h
  have hA : altE {p} (fun p' => (R.card : ℝ) / ((p' * p' : ℕ) : ℝ)) 1 =
      1 - (R.card : ℝ) / ((p * p : ℕ) : ℝ) := by
    rw [show ({p} : Finset ℕ) = insert p ∅ from rfl, altE_insert (notMem_empty p), altE_empty,
      altE_empty]; simp
  have hE : truncErr {p} (fun _ => (R.card : ℝ)) 1 = R.card := by
    unfold truncErr
    have hset : ({p} : Finset ℕ).powerset.filter (fun T => T.Nonempty ∧ T.card ≤ 1) = {{p}} := by
      ext T; simp only [mem_filter, mem_powerset, mem_singleton]
      constructor
      · rintro ⟨hT, hne, -⟩; exact (subset_singleton_iff.mp hT).resolve_left hne.ne_empty
      · rintro rfl; simp
    rw [hset]; simp
  rw [hA, hE] at h
  push_cast at h
  have : L / q * (1 - (1 - (R.card : ℝ) / (p * p))) = R.card * (L / q / (p * p)) := by ring
  linarith

/-- **Single-class sieve on a good domain.** Small primes (`p ≤ z`) with Bonferroni truncation at
odd depth `d`, medium primes (`z < p ≤ w`) by a union bound; `c` bounds the bad residues mod `p²`. -/
theorem domSieve_le {D : Finset ℕ} {L μ : ℝ} {Qok : ℕ → Prop} (hD : GoodDom D L μ Qok)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    (q t z w c d : ℕ) (hd : Odd d) (Rs : ℕ → Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hq : 0 < q) (ht : t < q) (hc : c ≤ 4)
    (hRs : ∀ p, Rs p ⊆ range (p * p)) (hRc : ∀ p, p.Prime → Q p → (Rs p).card ≤ c)
    (hcop : ∀ p, p.Prime → Q p → Nat.Coprime q p)
    (hok : ∀ T ⊆ smallP z Q, Qok (bigMod q (fun p => p * p) T))
    (hokq : Qok q) (hokm : ∀ p ∈ midP z w Q, Qok (q * (p * p))) :
    ((D.filter (fun a => a % q = t ∧ ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      L / q * (1 - altE (smallP z Q) (fun p => (c : ℝ) / (p * p)) d) +
        μ * truncErr (smallP z Q) (fun _ => (c : ℝ)) d +
        ∑ p ∈ midP z w Q, ((c : ℝ) * (L / q / (p * p)) + μ * c) := by
  classical
  set A := D.filter (fun a => a % q = t ∧ ∃ p ∈ smallP z Q, a % (p * p) ∈ Rs p)
  set B : ℕ → Finset ℕ := fun p => D.filter (fun a => a % q = t ∧ a % (p * p) ∈ Rs p)
  have hsub : D.filter (fun a => a % q = t ∧ ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p) ⊆
      A ∪ (midP z w Q).biUnion B := by
    intro a ha
    simp only [mem_filter] at ha
    obtain ⟨ha1, hat, p, hpw, hp, hQ, hR⟩ := ha
    by_cases hpz : p ≤ z
    · apply mem_union_left
      simp only [A, mem_filter, smallP, mem_range]
      exact ⟨ha1, hat, p, ⟨by omega, hp, hQ⟩, hR⟩
    · apply mem_union_right
      simp only [mem_biUnion, B, mem_filter, midP, mem_Ioc]
      exact ⟨p, ⟨⟨by omega, hpw⟩, hp, hQ⟩, ha1, hat, hR⟩
  have hcard : ((D.filter (fun a => a % q = t ∧
      ∃ p ≤ w, p.Prime ∧ Q p ∧ a % (p * p) ∈ Rs p)).card : ℝ) ≤
      (A.card : ℝ) + ∑ p ∈ midP z w Q, ((B p).card : ℝ) := by
    have h1 := (card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := card_biUnion_le (s := midP z w Q) (t := B)
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  have hsmallP : ∀ p ∈ smallP z Q, p.Prime ∧ Q p := fun p hp => (mem_filter.mp hp).2
  -- small primes
  have hA := dom_bonf_le hD q t (fun p => p * p) Rs (smallP z Q) d hd hq ht
    (fun p hp => Nat.mul_pos (hsmallP p hp).1.pos (hsmallP p hp).1.pos)
    (fun p _ r hr => mem_range.mp (hRs p hr))
    (fun p hp => Nat.Coprime.mul_right (hcop p (hsmallP p hp).1 (hsmallP p hp).2)
      (hcop p (hsmallP p hp).1 (hsmallP p hp).2))
    (fun p hp p' hp' hne => coprime_sq_of_primes (hsmallP p hp).1 (hsmallP p' hp').1 hne) hok
  have hv : ∀ p ∈ smallP z Q, (0 : ℝ) ≤ ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ) ∧
      ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ) ≤ (c : ℝ) / (p * p) := by
    intro p hp
    have hpp : (0 : ℝ) < p * p := by have := (hsmallP p hp).1.pos; positivity
    have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2
    push_cast
    exact ⟨by positivity, div_le_div_of_nonneg_right hRp hpp.le⟩
  have hw1 : ∀ p ∈ smallP z Q, (0 : ℝ) ≤ (c : ℝ) / (p * p) ∧ (c : ℝ) / (p * p) ≤ 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hsmallP p hp).1.two_le
    have : (c : ℝ) ≤ 4 := by exact_mod_cast hc
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]; nlinarith
  have hanti := altE_odd_anti (P := smallP z Q) (v := fun p => ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ))
    (w := fun p => (c : ℝ) / (p * p)) (fun p hp => (hv p hp).2)
    (fun p hp => ⟨(hv p hp).1, (hv p hp).2.trans (hw1 p hp).2⟩) hw1 hd
  have herr := truncErr_mono (smallP z Q) (x := fun p => ((Rs p).card : ℝ)) (y := fun _ => (c : ℝ))
    (fun p _ => by positivity)
    (fun p hp => by exact_mod_cast hRc p (hsmallP p hp).1 (hsmallP p hp).2) d
  have hLq : 0 ≤ L / q := by positivity
  have hA' : (A.card : ℝ) ≤ L / q * (1 - altE (smallP z Q) (fun p => (c : ℝ) / (p * p)) d) +
      μ * truncErr (smallP z Q) (fun _ => (c : ℝ)) d := by
    have e1 : L / q * (1 - altE (smallP z Q) (fun p => ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) d) ≤
        L / q * (1 - altE (smallP z Q) (fun p => (c : ℝ) / (p * p)) d) :=
      mul_le_mul_of_nonneg_left (by linarith) hLq
    have e2 : μ * truncErr (smallP z Q) (fun p => ((Rs p).card : ℝ)) d ≤
        μ * truncErr (smallP z Q) (fun _ => (c : ℝ)) d := mul_le_mul_of_nonneg_left herr hμ
    have : (A.card : ℝ) ≤ L / q * (1 - altE (smallP z Q)
        (fun p => ((Rs p).card : ℝ) / ((p * p : ℕ) : ℝ)) d) +
        μ * truncErr (smallP z Q) (fun p => ((Rs p).card : ℝ)) d := hA
    linarith
  -- medium primes
  have hB : ∀ p ∈ midP z w Q, ((B p).card : ℝ) ≤ (c : ℝ) * (L / q / (p * p)) + μ * c := by
    intro p hp
    have hpQ := (mem_filter.mp hp).2
    have h := dom_single_le hD q t p (Rs p) hq ht hpQ.1.pos (hRs p) (hcop p hpQ.1 hpQ.2) hokq
      (hokm p hp)
    have hRp : ((Rs p).card : ℝ) ≤ c := by exact_mod_cast hRc p hpQ.1 hpQ.2
    have : (0 : ℝ) ≤ L / q / (p * p) := by positivity
    calc ((B p).card : ℝ) ≤ ((Rs p).card : ℝ) * (L / q / (p * p)) + μ * (Rs p).card := h
      _ ≤ _ := by gcongr
  have := sum_le_sum hB
  linarith

/-! ### The domains of Section 10 -/

/-- Parity and a class mod an odd `Q` combine into one class mod `2Q`. -/
lemma odd_crt {Q : ℕ} (hQ : Odd Q) (e r : ℕ) (he : e < 2) (hr : r < Q) :
    ∃ s < 2 * Q, ∀ a, a % (2 * Q) = s ↔ a % 2 = e ∧ a % Q = r :=
  crt_class (Nat.coprime_two_left.mpr hQ) he hr

/-- `{odd a ∈ [1,N]} ∪ {even a ∈ [b,N]}` is a good domain of length `N - (b-1)/2`, error `2`,
for odd moduli. -/
theorem goodDom_split (N b : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N + 1) :
    GoodDom ((Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a)) (((2 * N + 1 - b : ℕ) : ℝ) / 2) 2 Odd := by
  intro Q r hQ hQo hr
  obtain ⟨s1, hs1, hs1'⟩ := odd_crt hQo 1 r (by norm_num) hr
  obtain ⟨s0, hs0, hs0'⟩ := odd_crt hQo 0 r (by norm_num) hr
  have h2Q : 0 < 2 * Q := by omega
  have hsplit : ((Icc 1 N).filter (fun a => a % 2 = 1 ∨ b ≤ a)).filter (fun a => a % Q = r) =
      (Icc 1 N).filter (fun a => a % (2 * Q) = s1) ∪ (Icc b N).filter (fun a => a % (2 * Q) = s0) := by
    ext a
    simp only [mem_filter, mem_union, mem_Icc, hs1', hs0']
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      rcases Nat.mod_two_eq_zero_or_one a with h | h
      · right; exact ⟨⟨by omega, h2⟩, h, h4⟩
      · left; exact ⟨⟨h1, h2⟩, h, h4⟩
    · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
      · exact ⟨⟨⟨h1, h2⟩, Or.inl h3⟩, h4⟩
      · exact ⟨⟨⟨by omega, h2⟩, Or.inr h1⟩, h4⟩
  have hdisj : Disjoint ((Icc 1 N).filter (fun a => a % (2 * Q) = s1))
      ((Icc b N).filter (fun a => a % (2 * Q) = s0)) := by
    rw [disjoint_left]; intro a ha hb'
    simp only [mem_filter, hs1', hs0'] at ha hb'
    omega
  rw [hsplit, card_union_of_disjoint hdisj]
  have e1 := card_mod_eq_real N (2 * Q) s1 h2Q hs1
  have e2 := goodDom_Icc b N hb hbN (2 * Q) s0 h2Q trivial hs0
  push_cast at e1 e2 ⊢
  have hL : (((2 * N + 1 - b : ℕ) : ℝ) / 2) / Q = (N : ℝ) / (2 * Q) + ((N + 1 - b : ℕ) : ℝ) / (2 * Q) := by
    have : ((2 * N + 1 - b : ℕ) : ℝ) = (N : ℝ) + ((N + 1 - b : ℕ) : ℝ) := by
      rw [show 2 * N + 1 - b = N + (N + 1 - b) by omega]; push_cast; ring
    rw [this]; field_simp
  rw [hL]
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-- `{a ∈ [b,N] : a ≡ e (mod 4)}` is a good domain of length `(N + 1 - b)/4`, error `1`, for odd
moduli. -/
theorem goodDom_mod4 (N b e : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N + 1) (he : e < 4) :
    GoodDom ((Icc b N).filter (fun a => a % 4 = e)) (((N + 1 - b : ℕ) : ℝ) / 4) 1 Odd := by
  intro Q r hQ hQo hr
  obtain ⟨s, hs, hs'⟩ := crt_class (m := 4) (n := Q) (a := e) (c := r)
    (by rcases hQo with ⟨k, rfl⟩; exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (by simp)) |>.symm.symm) he hr
  have h4Q : 0 < 4 * Q := by omega
  have hset : ((Icc b N).filter (fun a => a % 4 = e)).filter (fun a => a % Q = r) =
      (Icc b N).filter (fun a => a % (4 * Q) = s) := by
    ext a; simp only [mem_filter, hs']; tauto
  rw [hset]
  have := goodDom_Icc b N hb hbN (4 * Q) s h4Q trivial hs
  push_cast at this ⊢
  rwa [show (((N + 1 - b : ℕ) : ℝ) / 4) / Q = ((N + 1 - b : ℕ) : ℝ) / (4 * Q) by field_simp]

end Erdos848
