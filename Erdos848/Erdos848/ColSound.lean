import Erdos848.CompSound
import Erdos848.KPrime
import ErdosComp.Col

/-!
# Soundness of the small-case checker (`ErdosComp/Col.lean`)

* `sqfK_sound`: `sqfK n = true → Squarefree n`.
* `BT.get_set`: lookups after an update (complete trees of depth `16`).
* `colCheck_sound`: an accepted colouring certificate gives `Statement N` for all `N ≤ X`.
-/

namespace Erdos848

open Finset ErdosComp

/-! ### Squarefreeness -/

theorem smallPrimes4_filter : (List.range 10001).filter isPrimeB = smallPrimes4L := by decide +kernel

theorem PS4_eq : PS4 = smallPrimes4L.prod := by decide +kernel

theorem PS4_sq : smallPrimes4L.all (fun p => PS4 % (p * p) != 0) = true := by decide +kernel

lemma mem_smallPrimes4 {p : ℕ} : p ∈ smallPrimes4L ↔ p ≤ 10000 ∧ p.Prime := by
  rw [← smallPrimes4_filter, List.mem_filter, List.mem_range, isPrimeB_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma prime_dvd_PS4 {p : ℕ} (hp : p.Prime) (h : p ∣ PS4) : p ≤ 10000 := by
  rw [PS4_eq] at h
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff hp.prime).mp h
  have ha' := mem_smallPrimes4.mp ha
  have := (Nat.prime_dvd_prime_iff_eq hp ha'.2).mp hpa
  omega

lemma not_sq_dvd_PS4 {p : ℕ} (hp : p.Prime) : ¬ p * p ∣ PS4 := by
  intro h
  have hle := prime_dvd_PS4 hp (dvd_trans (dvd_mul_right p p) h)
  have hmem : p ∈ smallPrimes4L := mem_smallPrimes4.mpr ⟨hle, hp⟩
  have := List.all_eq_true.mp PS4_sq p hmem
  simp only [bne_iff_ne, ne_eq] at this
  exact this (Nat.mod_eq_zero_of_dvd h)

/-- **The squarefree test.** -/
theorem sqfK_sound {n : ℕ} (h : sqfK n = true) : Squarefree n := by
  unfold sqfK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hn0, hnB⟩, hcop⟩, hsq⟩ := h
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at hsq
  set g := Nat.gcd n PS4 with hg
  set m := n / g with hm
  have hgn : g ∣ n := Nat.gcd_dvd_left n PS4
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hn0
  have hnm : n = g * m := (Nat.mul_div_cancel' hgn).symm
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd hn0 hgn) hg0
  -- the prime factors of `m` are large
  have hbig : ∀ q, q.Prime → q ∣ m → 10007 ≤ q := by
    intro q hq hqm
    by_contra hlt
    have hq10 : q ≤ 10000 := by
      by_contra h'
      interval_cases q <;> norm_num at hq
    have hq4 : q ∈ smallPrimes4L := mem_smallPrimes4.mpr ⟨hq10, hq⟩
    have hqP : q ∣ PS4 := by rw [PS4_eq]; exact List.dvd_prod hq4
    have hqn : q ∣ n := hnm ▸ dvd_mul_of_dvd_right hqm g
    have hqg : q ∣ g := Nat.dvd_gcd hqn hqP
    have : q ∣ Nat.gcd g m := Nat.dvd_gcd hqg hqm
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hmsq : Squarefree m := by
    apply sqf_of_big_factors hm0 (lt_of_le_of_lt (Nat.div_le_self n g) hnB) hbig
    rintro ⟨h1, k, hk⟩
    rcases hsq with h' | h'
    · have : Nat.blt 1 m = true := Nat.blt_eq.mpr h1
      rw [this] at h'; exact Bool.noConfusion h'
    · unfold isSqK at h'
      rw [← hk, Nat.sqrt_eq k] at h'
      simp at h'
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  by_cases hpg : p ∣ g
  · -- `p ≤ 10⁴`: then `p ∣ m` too
    have hpP : p ∣ PS4 := dvd_trans hpg (Nat.gcd_dvd_right n PS4)
    have hpm : p ∣ m := by
      by_contra hpm
      have : p * p ∣ g := by
        rw [hnm] at hpp
        exact Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpm,
            (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm⟩) hpp
      exact not_sq_dvd_PS4 hp (dvd_trans this (Nat.gcd_dvd_right n PS4))
    have : p ∣ Nat.gcd g m := Nat.dvd_gcd hpg hpm
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · have hcop' : Nat.Coprime (p * p) g :=
      Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpg,
        (Nat.Prime.coprime_iff_not_dvd hp).mpr hpg⟩
    rw [hnm] at hpp
    have : p * p ∣ m := hcop'.dvd_of_dvd_mul_left hpp
    exact (Nat.squarefree_iff_prime_squarefree.mp hmsq) p hp this

end Erdos848

namespace ErdosComp

open Finset

/-! ### Trees -/

def BT.Full : ℕ → BT → Prop
  | 0, .lf _ => True
  | d + 1, .nd a b => BT.Full d a ∧ BT.Full d b
  | _, _ => False

lemma mkBT_full : ∀ d, (mkBT d).Full d
  | 0 => trivial
  | d + 1 => ⟨mkBT_full d, mkBT_full d⟩

lemma mkBT_get : ∀ d i, (mkBT d).get i = []
  | 0, _ => rfl
  | d + 1, i => by
    simp only [mkBT, BT.get]; cases (Nat.beq (i % 2) 0) <;> simp [mkBT_get d]

lemma BT.set_full : ∀ (d : ℕ) (t : BT) (i : ℕ) (x : List ℕ), t.Full d → (t.set i x).Full d
  | 0, .lf _, _, _, _ => trivial
  | d + 1, .nd a b, i, x, ⟨ha, hb⟩ => by
    simp only [BT.set]
    cases (Nat.beq (i % 2) 0)
    · exact ⟨ha, BT.set_full d b _ x hb⟩
    · exact ⟨BT.set_full d a _ x ha, hb⟩
  | 0, .nd _ _, _, _, h => h.elim
  | _ + 1, .lf _, _, _, h => h.elim

lemma BT.get_set : ∀ (d : ℕ) (t : BT) (i j : ℕ) (x : List ℕ), t.Full d → i < 2 ^ d → j < 2 ^ d →
    (t.set i x).get j = if i = j then x else t.get j
  | 0, .lf _, i, j, x, _, hi, hj => by
    simp only [pow_zero] at hi hj
    simp [BT.set, BT.get, show i = 0 by omega, show j = 0 by omega]
  | d + 1, .nd a b, i, j, x, ⟨ha, hb⟩, hi, hj => by
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    simp only [BT.set, BT.get]
    rcases Nat.mod_two_eq_zero_or_one i with ei | ei <;>
      rcases Nat.mod_two_eq_zero_or_one j with ej | ej <;>
      simp only [ei, ej, Nat.beq_refl, cond_true, cond_false, show Nat.beq 1 0 = false from rfl,
        BT.get]
    · rw [BT.get_set d a _ _ x ha hi2 hj2]
      by_cases hij : i = j
      · simp [hij]
      · have : i / 2 ≠ j / 2 := fun h => hij (by omega)
        simp [hij, this]
    · rw [if_neg (by omega)]
    · rw [if_neg (by omega)]
    · rw [BT.get_set d b _ _ x hb hi2 hj2]
      by_cases hij : i = j
      · simp [hij]
      · have : i / 2 ≠ j / 2 := fun h => hij (by omega)
        simp [hij, this]
  | 0, .nd _ _, _, _, _, h, _, _ => h.elim
  | _ + 1, .lf _, _, _, _, h, _, _ => h.elim

end ErdosComp

namespace Erdos848

open Finset ErdosComp

/-! ### Membership in the merged lists -/

lemma mem_mergeF : ∀ f (l1 l2 : List ℕ) x, x ∈ mergeF f l1 l2 ↔ x ∈ l1 ∨ x ∈ l2
  | 0, l1, l2, x => by simp [mergeF]
  | _ + 1, [], l, x => by simp [mergeF]
  | _ + 1, a :: as, [], x => by simp [mergeF]
  | f + 1, a :: as, b :: bs, x => by
    simp only [mergeF]
    cases Nat.ble a b
    · simp only [cond_false, List.mem_cons, mem_mergeF f (a :: as) bs x]; tauto
    · simp only [cond_true, List.mem_cons, mem_mergeF f as (b :: bs) x]; tauto

lemma mem_mergeL (l1 l2 : List ℕ) (x : ℕ) : x ∈ mergeL l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 :=
  mem_mergeF _ l1 l2 x

lemma mem_mergeRound : ∀ (ls : List (List ℕ)) x, (∃ l ∈ mergeRound ls, x ∈ l) ↔ ∃ l ∈ ls, x ∈ l
  | [], x => by simp [mergeRound]
  | [a], x => by simp [mergeRound]
  | a :: b :: rest, x => by
    simp only [mergeRound, List.mem_cons, exists_eq_or_imp, mem_mergeL, mem_mergeRound rest x]
    tauto

lemma mem_mergeAllF : ∀ f (ls : List (List ℕ)) x, x ∈ mergeAllF f ls ↔ ∃ l ∈ ls, x ∈ l
  | 0, ls, x => by simp [mergeAllF, List.mem_flatten]
  | _ + 1, [], x => by simp [mergeAllF]
  | _ + 1, [l], x => by simp [mergeAllF]
  | f + 1, a :: b :: rest, x => by
    simp only [mergeAllF]
    rw [mem_mergeAllF f, mem_mergeRound]

lemma mem_dedupS : ∀ (l : List ℕ) x, x ∈ dedupS l ↔ x ∈ l
  | [], x => by simp [dedupS]
  | [a], x => by simp [dedupS]
  | a :: b :: rest, x => by
    simp only [dedupS]
    have ih := mem_dedupS (b :: rest) x
    cases h : Nat.beq a b
    · simp only [cond_false, List.mem_cons] at ih ⊢; tauto
    · have hab := Nat.eq_of_beq_eq_true h
      subst hab
      simp only [cond_true, List.mem_cons] at ih ⊢; tauto

lemma mem_progL (X m : ℕ) : ∀ f r k, k < f → r + k * m ≤ X → r + k * m ∈ progL X m f r
  | 0, _, _, hk, _ => by omega
  | f + 1, r, 0, _, hX => by simp only [progL]; rw [show Nat.ble r X = true from Nat.ble_eq.mpr (by simpa using hX)]; simp
  | f + 1, r, k + 1, hk, hX => by
    simp only [progL]
    rw [show Nat.ble r X = true from Nat.ble_eq.mpr (by have := Nat.le_add_right r ((k + 1) * m); omega)]
    simp only [cond_true, List.mem_cons]
    right
    have := mem_progL X m f (r + m) k (by omega) (by
      have : r + m + k * m = r + (k + 1) * m := by ring
      omega)
    rwa [show r + m + k * m = r + (k + 1) * m by ring] at this

lemma mem_progL_pos (X m : ℕ) : ∀ f r x, x ∈ progL X m f r → r ≤ x
  | 0, _, _, h => by simp [progL] at h
  | f + 1, r, x, h => by
    simp only [progL] at h
    cases hb : Nat.ble r X
    · rw [hb] at h; simp at h
    · rw [hb] at h
      simp only [cond_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact le_rfl
      · have := mem_progL_pos X m f (r + m) x h; omega

/-! ### The roots -/

lemma rootsGo_spec (X : ℕ) : ∀ f n (rs : List (ℕ × ℕ)), rootsGo X f n rs = true → n % 4 = 1 →
    X < n + 4 * f → ∀ q, q % 4 = 1 → n ≤ q → q ≤ X → q < 20007729 → q.Prime →
      ∃ r, (q, r) ∈ rs ∧ r < q * q ∧ (r * r + 1) % (q * q) = 0
  | 0, n, rs, _, _, hf, q, _, h1, h2, _, _ => by omega
  | f + 1, n, rs, h, hn, hf, q, hq4, h1, h2, hqB, hq => by
    simp only [rootsGo] at h
    cases hX : Nat.blt X n
    · rw [hX] at h
      simp only [cond_false] at h
      have hnX : n ≤ X := by
        have : ¬ X < n := fun h' => by rw [Nat.blt_eq.mpr h'] at hX; exact Bool.noConfusion hX
        omega
      match rs, h with
      | (p, r) :: rest, h =>
        dsimp only at h
        cases hp : Nat.beq p n
        · rw [hp] at h
          simp only [cond_false, Bool.and_eq_true, Bool.not_eq_true'] at h
          rcases Nat.eq_or_lt_of_le h1 with heq | hlt
          · -- `q = n` is prime, but `fastP n = false`
            have := fastP_eq (n := n) (by omega)
            rw [h.1, (isPrimeB_iff n).mpr (heq ▸ hq)] at this
            exact Bool.noConfusion this
          · obtain ⟨r', hr', h'⟩ := rootsGo_spec X f (n + 4) _ h.2 (by omega) (by omega) q hq4
              (by omega) h2 hqB hq
            exact ⟨r', hr', h'⟩
        · rw [hp] at h
          have hpn := Nat.eq_of_beq_eq_true hp
          subst hpn
          simp only [cond_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
          obtain ⟨⟨hr1, hr2⟩, hrest⟩ := h
          rcases Nat.eq_or_lt_of_le h1 with heq | hlt
          · subst heq; exact ⟨r, List.mem_cons_self .., hr1, hr2⟩
          · obtain ⟨r', hr', h'⟩ := rootsGo_spec X f (p + 4) rest hrest (by omega) (by omega) q hq4
              (by omega) h2 hqB hq
            exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
      | [], h =>
        dsimp only at h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · have := fastP_eq (n := n) (by omega)
          rw [h.1, (isPrimeB_iff n).mpr (heq ▸ hq)] at this
          exact Bool.noConfusion this
        · exact rootsGo_spec X f (n + 4) [] h.2 (by omega) (by omega) q hq4 (by omega) h2 hqB hq
    · have : X < n := Nat.blt_eq.mp hX
      omega

/-- **Every vertex below `X` is a mark.** -/
theorem mem_marksOf {X : ℕ} {roots : List (ℕ × ℕ)} (hr : rootsOK X roots = true) {v : ℕ}
    (hv1 : 1 ≤ v) (hvX : v ≤ X) (hv : ¬ Squarefree (v * v + 1)) : v ∈ marksOf X roots := by
  unfold rootsOK at hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr
  obtain ⟨hXB, hgo⟩ := hr
  obtain ⟨p, hp, hpv⟩ := exists_prime_sq_dvd hv
  have hp4 := prime_mod_four_of_sq_dvd hp hpv
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p <;> simp_all
    · exact h
  have hpv' : p ≤ v := by
    have h1 := Nat.le_of_dvd (by positivity) hpv
    nlinarith
  obtain ⟨r, hmem, hr1, hr2⟩ := rootsGo_spec X _ 5 roots hgo rfl (by omega) p hp4 hp5
    (by omega) (by omega) hp
  -- `v` is congruent to `r` or `p² - r`
  have hroot := sqRoots_eq hp (by omega) hr1 (Nat.dvd_of_mod_eq_zero hr2) (v % (p * p)) (by
    simp only [sqRoots, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    have : (v % (p * p)) * (v % (p * p)) + 1 ≡ v * v + 1 [MOD p * p] :=
      Nat.ModEq.add_right 1 (Nat.ModEq.mul (Nat.mod_modEq v _) (Nat.mod_modEq v _))
    exact (Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr hpv)))
  )
  unfold marksOf
  rw [mem_dedupS, mem_mergeAllF]
  refine ⟨marksP X p r, List.mem_map.mpr ⟨(p, r), hmem, rfl⟩, ?_⟩
  unfold marksP
  rw [mem_mergeL]
  have hv' : v = v % (p * p) + v / (p * p) * (p * p) := by
    have := Nat.mod_add_div v (p * p); linarith
  have hk : v / (p * p) < X / (p * p) + 2 := by
    have := Nat.div_le_div_right (c := p * p) hvX; omega
  rcases hroot with e | e
  · left; rw [hv', e]; exact mem_progL X (p * p) _ r _ hk (by rw [← e, ← hv']; exact hvX)
  · right; rw [hv', e]; exact mem_progL X (p * p) _ (p * p - r) _ hk (by rw [← e, ← hv']; exact hvX)

lemma rootsGo_valid (X : ℕ) : ∀ f n (rs : List (ℕ × ℕ)), rootsGo X f n rs = true →
    ∀ pr ∈ rs, n ≤ pr.1 ∧ pr.2 < pr.1 * pr.1 ∧ (pr.2 * pr.2 + 1) % (pr.1 * pr.1) = 0
  | 0, n, rs, h, pr, hpr => by
    simp only [rootsGo, List.isEmpty_iff] at h; subst h; simp at hpr
  | f + 1, n, rs, h, pr, hpr => by
    simp only [rootsGo] at h
    cases hX : Nat.blt X n
    · rw [hX] at h
      simp only [cond_false] at h
      match rs, h, hpr with
      | (p, r) :: rest, h, hpr =>
        dsimp only at h
        cases hp : Nat.beq p n
        · rw [hp] at h
          simp only [cond_false, Bool.and_eq_true] at h
          have := rootsGo_valid X f (n + 4) _ h.2 pr hpr
          exact ⟨by omega, this.2⟩
        · rw [hp] at h
          have hpn := Nat.eq_of_beq_eq_true hp
          simp only [cond_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
          rcases List.mem_cons.mp hpr with rfl | hpr'
          · exact ⟨by simp [hpn], h.1.1, h.1.2⟩
          · have := rootsGo_valid X f (n + 4) rest h.2 pr hpr'
            exact ⟨by omega, this.2⟩
      | [], _, hpr => simp at hpr
    · rw [hX] at h
      simp only [cond_true, List.isEmpty_iff] at h
      subst h; simp at hpr

lemma marksOf_pos {X : ℕ} {roots : List (ℕ × ℕ)} (hr : rootsOK X roots = true) :
    ∀ m ∈ marksOf X roots, 1 ≤ m := by
  intro m hm
  unfold marksOf at hm
  rw [mem_dedupS, mem_mergeAllF] at hm
  obtain ⟨l, hl, hml⟩ := hm
  obtain ⟨⟨p, r⟩, hpr, rfl⟩ := List.mem_map.mp hl
  unfold rootsOK at hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr
  obtain ⟨h5, hr1, hr2⟩ := rootsGo_valid X _ 5 roots hr.2 (p, r) hpr
  simp only at h5 hr1 hr2
  have hr0 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      have : 1 % (p * p) = 1 := Nat.mod_eq_of_lt (by nlinarith)
      simp [this] at hr2
    · exact h0
  unfold marksP at hml
  rw [mem_mergeL] at hml
  rcases hml with h | h
  · exact le_trans hr0 (mem_progL_pos X _ _ r m h)
  · exact le_trans (by omega) (mem_progL_pos X _ _ (p * p - r) m h)

/-! ### The run -/

lemma strictInc_spec : ∀ l : List ℕ, strictInc l = true → l.Pairwise (· < ·)
  | [] => fun _ => List.Pairwise.nil
  | [a] => fun _ => by simp
  | a :: b :: rest => fun h => by
    simp only [strictInc, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := strictInc_spec (b :: rest) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

lemma markOK_spec {ms : List ℕ} {v : ℕ} (hs : ms.Pairwise (· < ·)) (h : markOK ms v = true) :
    ∀ m ∈ ms, v ≤ m := by
  intro m hm
  rcases ms with _ | ⟨a, rest⟩
  · simp at hm
  · simp only [markOK, Nat.ble_eq] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h
    · exact le_trans h (List.rel_of_pairwise_cons hs hm).le

lemma popMark_filter {M : List ℕ} (hM : M.Pairwise (· < ·)) {last v : ℕ} (hlv : last < v)
    (h : markOK (M.filter (fun m => last < m)) v = true) :
    popMark (M.filter (fun m => last < m)) v = M.filter (fun m => v < m) := by
  have hs : (M.filter (fun m => last < m)).Pairwise (· < ·) := hM.filter _
  have hge := markOK_spec hs h
  rcases hfl : M.filter (fun m => last < m) with _ | ⟨a, rest⟩
  · simp only [popMark]
    have : M.filter (fun m => v < m) = [] := by
      rw [List.filter_eq_nil_iff]; intro m hm hvm
      have hvm' : v < m := by simpa using hvm
      have : m ∈ M.filter (fun m => last < m) :=
        List.mem_filter.mpr ⟨hm, by simpa using (by omega : last < m)⟩
      rw [hfl] at this; simp at this
    rw [this]
  · have hsa : (a :: rest).Pairwise (· < ·) := hfl ▸ hs
    have hav : v ≤ a := hge a (by rw [hfl]; exact List.mem_cons_self ..)
    -- `M.filter (v < ·)` is the part of `a :: rest` above `v`
    have hfv : M.filter (fun m => v < m) = (a :: rest).filter (fun m => v < m) := by
      rw [← hfl, List.filter_filter]
      apply List.filter_congr
      intro m _
      by_cases h1 : v < m
      · simp [h1, show last < m by omega]
      · simp [h1]
    rw [hfv]
    cases hb : Nat.beq a v
    · simp only [popMark, hb, cond_false]
      have hav' : v < a := lt_of_le_of_ne hav (fun e => by rw [e] at hb; simp at hb)
      symm
      rw [List.filter_eq_self]
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · simpa using hav'
      · simpa using lt_trans hav' (List.rel_of_pairwise_cons hsa hm)
    · simp only [popMark, hb, cond_true]
      have hav' : a = v := Nat.eq_of_beq_eq_true hb
      subst hav'
      rw [List.filter_cons_of_neg (by simp)]
      symm
      rw [List.filter_eq_self]
      intro m hm
      simpa using List.rel_of_pairwise_cons hsa hm

section
variable {X : ℕ} {roots : List (ℕ × ℕ)}

/-- The invariant of the run. -/
def ColInv (M : List ℕ) (s : CSt) : Prop :=
  s.t.Full 16 ∧ s.cnt ≤ slots ∧
  (∀ j < s.cnt, ∀ u ∈ s.t.get j, ∀ w ∈ s.t.get j, u ≠ w → Squarefree (u * w + 1)) ∧
  (∀ m ∈ M, m ≤ s.last → ∃ j < s.cnt, m ∈ s.t.get j) ∧
  s.cnt ≤ c7 s.last ∧
  s.marks = M.filter (fun m => s.last < m)

lemma compatL_spec {v : ℕ} {l : List ℕ} (h : compatL v l = true) : ∀ u ∈ l, Squarefree (u * v + 1) :=
  fun u hu => sqfK_sound (List.all_eq_true.mp h u hu)

lemma slots_eq : slots = 2 ^ 16 := rfl

lemma stepC_inv {M : List ℕ} (hM : M.Pairwise (· < ·)) {s s' : CSt} {op : COp}
    (hs : ColInv M s) (h : stepC s op = some s') : ColInv M s' ∧ (s'.last = s.last ∨
      (s.last < s'.last ∧ markOK s.marks s'.last = true)) := by
  obtain ⟨hF, hcs, hP, hC, hc7, hmk⟩ := hs
  cases op with
  | nw v =>
    simp only [stepC] at h
    cases hc : (Nat.blt s.last v && Nat.ble (s.cnt + 1) (c7K v) && Nat.blt s.cnt slots &&
      markOK s.marks v)
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
      obtain ⟨⟨⟨hlv, hc7v⟩, hslot⟩, hmo⟩ := hc
      have hget : ∀ j, j < 2 ^ 16 → (s.t.set s.cnt [v]).get j = if s.cnt = j then [v] else s.t.get j :=
        fun j hj => BT.get_set 16 s.t s.cnt j [v] hF hslot hj
      refine ⟨⟨BT.set_full 16 s.t s.cnt [v] hF, by simpa using hslot, ?_, ?_, ?_, ?_⟩, Or.inr ⟨hlv, hmo⟩⟩
      · intro j hj u hu w hw huw
        simp only at hj
        rw [hget j (by rw [slots_eq] at hslot; omega)] at hu hw
        split_ifs at hu hw with hje
        · simp at hu hw; omega
        · exact hP j (by omega) u hu w hw huw
      · intro m hm hmv
        simp only at hmv ⊢
        by_cases hml : m ≤ s.last
        · obtain ⟨j, hj, hmj⟩ := hC m hm hml
          refine ⟨j, by omega, ?_⟩
          rw [hget j (by rw [slots_eq] at hslot; omega), if_neg (by omega)]; exact hmj
        · have hmm : m ∈ s.marks := by rw [hmk]; exact List.mem_filter.mpr ⟨hm, by simpa using (by omega : s.last < m)⟩
          have := markOK_spec (hmk ▸ hM.filter _) hmo m hmm
          have hmv' : m = v := by omega
          refine ⟨s.cnt, by omega, ?_⟩
          rw [hget s.cnt (by rw [slots_eq] at hslot; omega), if_pos rfl, hmv']; simp
      · simp only; exact hc7v
      · simp only; rw [hmk]; exact popMark_filter hM hlv (hmk ▸ hmo)
  | put v j =>
    simp only [stepC] at h
    cases hc : (Nat.blt s.last v && Nat.blt j s.cnt && markOK s.marks v && compatL v (s.t.get j))
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      obtain ⟨⟨⟨hlv, hj⟩, hmo⟩, hcomp⟩ := hc
      have hj16 : j < 2 ^ 16 := by rw [slots_eq] at hcs; omega
      have hget : ∀ i, i < 2 ^ 16 → (s.t.set j (v :: s.t.get j)).get i =
          if j = i then v :: s.t.get j else s.t.get i :=
        fun i hi => BT.get_set 16 s.t j i _ hF hj16 hi
      refine ⟨⟨BT.set_full 16 s.t j _ hF, hcs, ?_, ?_, ?_, ?_⟩, Or.inr ⟨hlv, hmo⟩⟩
      · intro i hi u hu w hw huw
        simp only at hi
        rw [hget i (by rw [slots_eq] at hcs; omega)] at hu hw
        split_ifs at hu hw with hji
        · subst hji
          rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hw with rfl | hw'
          · exact absurd rfl huw
          · rw [mul_comm]; exact compatL_spec hcomp w hw'
          · exact compatL_spec hcomp u hu'
          · exact hP j hj u hu' w hw' huw
        · exact hP i hi u hu w hw huw
      · intro m hm hmv
        simp only at hmv ⊢
        by_cases hml : m ≤ s.last
        · obtain ⟨i, hi, hmi⟩ := hC m hm hml
          refine ⟨i, hi, ?_⟩
          rw [hget i (by rw [slots_eq] at hcs; omega)]
          split_ifs with hji
          · subst hji; exact List.mem_cons_of_mem _ hmi
          · exact hmi
        · have hmm : m ∈ s.marks := by rw [hmk]; exact List.mem_filter.mpr ⟨hm, by simpa using (by omega : s.last < m)⟩
          have := markOK_spec (hmk ▸ hM.filter _) hmo m hmm
          have hmv' : m = v := by omega
          refine ⟨j, hj, ?_⟩
          rw [hget j hj16, if_pos rfl, hmv']; exact List.mem_cons_self ..
      · simp only; exact le_trans hc7 (Nat.div_le_div_right (by omega))
      · simp only; rw [hmk]; exact popMark_filter hM hlv (hmk ▸ hmo)
  | mv w c d =>
    simp only [stepC] at h
    cases hc : (Nat.blt c s.cnt && Nat.blt d s.cnt && !Nat.beq c d && (s.t.get c).contains w &&
        compatL w (s.t.get d))
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', List.contains_iff_mem] at hc
      obtain ⟨⟨⟨⟨hcc, hdc⟩, hcd⟩, hwc⟩, hcomp⟩ := hc
      have hcd' : c ≠ d := fun e => by rw [e] at hcd; simp at hcd
      have hc16 : c < 2 ^ 16 := by rw [slots_eq] at hcs; omega
      have hd16 : d < 2 ^ 16 := by rw [slots_eq] at hcs; omega
      have hF1 : (s.t.set c ((s.t.get c).erase w)).Full 16 := BT.set_full 16 s.t c _ hF
      have hget : ∀ i, i < 2 ^ 16 →
          ((s.t.set c ((s.t.get c).erase w)).set d (w :: s.t.get d)).get i =
          if d = i then w :: s.t.get d else if c = i then (s.t.get c).erase w else s.t.get i := by
        intro i hi
        rw [BT.get_set 16 _ d i _ hF1 hd16 hi, BT.get_set 16 s.t c i _ hF hc16 hi]
      refine ⟨⟨BT.set_full 16 _ d _ hF1, hcs, ?_, ?_, hc7, hmk⟩, Or.inl rfl⟩
      · intro i hi u hu w' hw' huw
        simp only at hi
        rw [hget i (by rw [slots_eq] at hcs; omega)] at hu hw'
        split_ifs at hu hw' with h1 h2
        · subst h1
          rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hw' with rfl | hw''
          · exact absurd rfl huw
          · rw [mul_comm]; exact compatL_spec hcomp w' hw''
          · exact compatL_spec hcomp u hu'
          · exact hP d hdc u hu' w' hw'' huw
        · subst h2
          exact hP c hcc u (List.mem_of_mem_erase hu) w' (List.mem_of_mem_erase hw') huw
        · exact hP i hi u hu w' hw' huw
      · intro m hm hml
        obtain ⟨i, hi, hmi⟩ := hC m hm hml
        by_cases hmw : m = w
        · refine ⟨d, hdc, ?_⟩
          rw [hget d hd16, if_pos rfl, hmw]; exact List.mem_cons_self ..
        · refine ⟨i, hi, ?_⟩
          rw [hget i (by rw [slots_eq] at hcs; omega)]
          split_ifs with h1 h2
          · subst h1; exact List.mem_cons_of_mem _ hmi
          · subst h2; exact (List.mem_erase_of_ne hmw).mpr hmi
          · exact hmi

/-- A state certifies `N` once every mark `≤ N` has been placed. -/
lemma certify {M : List ℕ} (hr : rootsOK X roots = true) (hM : M = marksOf X roots) {s : CSt}
    (hs : ColInv M s) {N : ℕ} (hlN : s.last ≤ N) (hNX : N ≤ X) (hmk : ∀ m ∈ s.marks, N < m) :
    Statement N := by
  classical
  obtain ⟨hF, hcs, hP, hC, hc7, hmks⟩ := hs
  intro A hsub hA
  have hcov : ∀ a ∈ A, ∃ j < s.cnt, a ∈ s.t.get j := by
    intro a ha
    have haI := mem_Icc.mp (hsub ha)
    have haM : a ∈ M := hM ▸ mem_marksOf hr haI.1 (by omega) (hA a ha a ha)
    have hal : a ≤ s.last := by
      by_contra hal
      have : a ∈ s.marks := by
        rw [hmks]; exact List.mem_filter.mpr ⟨haM, by simpa using (by omega : s.last < a)⟩
      have := hmk a this; omega
    exact hC a haM hal
  let f : ℕ → ℕ := fun a => if h : ∃ j < s.cnt, a ∈ s.t.get j then Classical.choose h else 0
  have hf : ∀ a ∈ A, f a < s.cnt ∧ a ∈ s.t.get (f a) := by
    intro a ha
    have h := hcov a ha
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  calc A.card ≤ (range s.cnt).card := by
        apply card_le_card_of_injOn f (fun a ha => mem_range.mpr (hf a ha).1)
        intro a ha b hb hab
        by_contra hne
        have h1 := hf a ha
        have h2 := hf b hb
        have hb' : b ∈ s.t.get (f a) := by rw [hab]; exact h2.2
        exact hA a ha b hb (hP (f a) h1.1 a h1.2 b hb' hne)
    _ = s.cnt := card_range _
    _ ≤ c7 s.last := hc7
    _ ≤ c7 N := Nat.div_le_div_right (by omega)

theorem runC_sound {M : List ℕ} (hr : rootsOK X roots = true) (hM : M = marksOf X roots)
    (hMs : M.Pairwise (· < ·)) : ∀ (ops : List COp) (s sf : CSt), ColInv M s →
    runC s ops = some sf → sf.marks = [] → ∀ N, s.last ≤ N → N ≤ X → Statement N := by
  intro ops
  induction ops with
  | nil =>
    intro s sf hs h hmk N hlN hNX
    simp only [runC, Option.some.injEq] at h
    subst h
    exact certify hr hM hs hlN hNX (by simp [hmk])
  | cons op ops ih =>
    intro s sf hs h hmk N hlN hNX
    simp only [runC] at h
    cases hst : stepC s op with
    | none => rw [hst] at h; simp at h
    | some s' =>
      rw [hst] at h
      obtain ⟨hs', hlast⟩ := stepC_inv hMs hs hst
      rcases hlast with e | ⟨hlt, hmo⟩
      · exact ih s' sf hs' h hmk N (by omega) hNX
      · by_cases hN : s'.last ≤ N
        · exact ih s' sf hs' h hmk N hN hNX
        · apply certify hr hM hs hlN hNX
          intro m hm
          have hsort : s.marks.Pairwise (· < ·) := hs.2.2.2.2.2 ▸ hMs.filter _
          have := markOK_spec hsort hmo m hm
          omega

/-- **The small cases.** An accepted certificate gives `Statement N` for every `N ≤ X`. -/
theorem colCheck_sound {ops : List COp} (hc : colCheck X roots ops = true)
    (hr : rootsOK X roots = true) : ∀ N ≤ X, Statement N := by
  unfold colCheck at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hinc, hrun⟩ := hc
  have hMs := strictInc_spec _ hinc
  have hpos := marksOf_pos hr
  cases h : runC ⟨0, mkBT 16, 0, marksOf X roots⟩ ops with
  | none => rw [h] at hrun; simp at hrun
  | some sf =>
    rw [h] at hrun
    simp only [List.isEmpty_iff] at hrun
    intro N hN
    refine runC_sound hr rfl hMs ops _ sf ⟨mkBT_full 16, by simp [slots], ?_, ?_, ?_, ?_⟩ h hrun N
      (Nat.zero_le N) hN
    · intro j hj; simp at hj
    · intro m hm hm0; have := hpos m hm; simp at hm0; omega
    · simp [c7]
    · simp only
      symm
      rw [List.filter_eq_self]
      intro m hm; have := hpos m hm; simp only [decide_eq_true_eq]; omega

/-! ### Windows -/

/-- Membership in a classes list is preserved by every step. -/
lemma stepC_cover {s s' : CSt} {op : COp} (hF : s.t.Full 16) (hcs : s.cnt ≤ slots)
    (h : stepC s op = some s') : ∀ x, (∃ j < s.cnt, x ∈ s.t.get j) → ∃ j < s'.cnt, x ∈ s'.t.get j := by
  intro x ⟨j, hj, hx⟩
  have hj16 : j < 2 ^ 16 := by rw [slots_eq] at hcs; omega
  cases op with
  | nw v =>
    simp only [stepC] at h
    cases hc : (Nat.blt s.last v && Nat.ble (s.cnt + 1) (c7K v) && Nat.blt s.cnt slots &&
      markOK s.marks v)
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      refine ⟨j, by simp only; omega, ?_⟩
      simp only
      rw [BT.get_set 16 s.t s.cnt j _ hF (by rw [slots_eq] at hc; exact hc.1.2) hj16, if_neg (by omega)]
      exact hx
  | put v i =>
    simp only [stepC] at h
    cases hc : (Nat.blt s.last v && Nat.blt i s.cnt && markOK s.marks v && compatL v (s.t.get i))
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      refine ⟨j, hj, ?_⟩
      simp only
      rw [BT.get_set 16 s.t i j _ hF (by rw [slots_eq] at hcs; omega) hj16]
      split_ifs with hij
      · subst hij; exact List.mem_cons_of_mem _ hx
      · exact hx
  | mv w c d =>
    simp only [stepC] at h
    cases hc : (Nat.blt c s.cnt && Nat.blt d s.cnt && !Nat.beq c d && (s.t.get c).contains w &&
        compatL w (s.t.get d))
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      have hc16 : c < 2 ^ 16 := by rw [slots_eq] at hcs; omega
      have hd16 : d < 2 ^ 16 := by rw [slots_eq] at hcs; omega
      have hF1 : (s.t.set c ((s.t.get c).erase w)).Full 16 := BT.set_full 16 s.t c _ hF
      simp only
      by_cases hxw : x = w
      · refine ⟨d, hc.1.1.1.2, ?_⟩
        rw [BT.get_set 16 _ d d _ hF1 hd16 hd16, if_pos rfl, hxw]; exact List.mem_cons_self ..
      · refine ⟨j, hj, ?_⟩
        rw [BT.get_set 16 _ d j _ hF1 hd16 hj16, BT.get_set 16 s.t c j _ hF hc16 hj16]
        split_ifs with h1 h2
        · subst h1; exact List.mem_cons_of_mem _ hx
        · subst h2; exact (List.mem_erase_of_ne hxw).mpr hx
        · exact hx

/-- A checkpoint: a tree of `cnt` classes covering every vertex `≤ X₀`, opened by time `last`. -/
def WinOK (X0 : ℕ) (t : BT) (cnt last : ℕ) : Prop :=
  t.Full 16 ∧ cnt ≤ slots ∧ last ≤ X0 ∧
  (∀ j < cnt, ∀ u ∈ t.get j, ∀ w ∈ t.get j, u ≠ w → Squarefree (u * w + 1)) ∧
  (∀ v, 1 ≤ v → v ≤ X0 → ¬ Squarefree (v * v + 1) → ∃ j < cnt, v ∈ t.get j) ∧
  cnt ≤ c7 last

lemma winOK_zero : WinOK 0 (mkBT 16) 0 0 :=
  ⟨mkBT_full 16, by simp [slots], le_rfl, fun j hj => by omega, fun v h1 h2 _ => by omega, by simp [c7]⟩

/-- Generic: classes covering all vertices `≤ N`, pairwise compatible, at most `c₇(N)`. -/
lemma statement_of_classes {N : ℕ} (k : ℕ) (g : ℕ → List ℕ)
    (hP : ∀ j < k, ∀ u ∈ g j, ∀ w ∈ g j, u ≠ w → Squarefree (u * w + 1))
    (hC : ∀ v, 1 ≤ v → v ≤ N → ¬ Squarefree (v * v + 1) → ∃ j < k, v ∈ g j) (hk : k ≤ c7 N) :
    Statement N := by
  classical
  intro A hsub hA
  let f : ℕ → ℕ := fun a => if h : ∃ j < k, a ∈ g j then Classical.choose h else 0
  have hf : ∀ a ∈ A, f a < k ∧ a ∈ g (f a) := by
    intro a ha
    have haI := mem_Icc.mp (hsub ha)
    have h := hC a haI.1 haI.2 (hA a ha a ha)
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  calc A.card ≤ (range k).card := by
        apply card_le_card_of_injOn f (fun a ha => mem_range.mpr (hf a ha).1)
        intro a ha b hb hab
        by_contra hne
        have h1 := hf a ha
        have h2 := hf b hb
        have hb' : b ∈ g (f a) := by rw [hab]; exact h2.2
        exact hA a ha b hb (hP (f a) h1.1 a h1.2 b hb' hne)
    _ = k := card_range _
    _ ≤ c7 N := hk

lemma winOK_statement {X0 : ℕ} {t : BT} {cnt last : ℕ} (h : WinOK X0 t cnt last) :
    ∀ N, last ≤ N → N ≤ X0 → Statement N := by
  obtain ⟨_, _, _, hP, hC, hc7⟩ := h
  intro N hlN hNX
  exact statement_of_classes cnt t.get hP (fun v h1 h2 h3 => hC v h1 (by omega) h3)
    (le_trans hc7 (Nat.div_le_div_right (by omega)))

/-! #### The marks of a window -/

/-- `⌈a/m⌉ m ≥ a`. -/
lemma ceil_mul_ge (a m : ℕ) (hm : 0 < m) : a ≤ (a + m - 1) / m * m := by
  have h1 := Nat.div_add_mod (a + m - 1) m
  have h2 := Nat.mod_lt (a + m - 1) hm
  rw [mul_comm] at h1
  generalize (a + m - 1) / m * m = t at *
  generalize (a + m - 1) % m = u at *
  omega

lemma ceil_le_of {a m k : ℕ} (hm : 0 < m) (h : a ≤ k * m) : (a + m - 1) / m ≤ k := by
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul hm, Nat.succ_mul]
  generalize k * m = t at *
  omega

lemma progFrom_mem {lo X m r k : ℕ} (hm : 0 < m) (hlo : lo ≤ r + k * m) (hvX : r + k * m ≤ X) :
    r + k * m ∈ progFrom lo X m r := by
  unfold progFrom
  cases hb : Nat.ble lo r
  · -- `r < lo`: start at `r + c m`, `c = ⌈(lo - r)/m⌉ ≤ k`
    simp only [cond_false]
    have hrl : r < lo := by
      have : ¬ lo ≤ r := fun h => by rw [Nat.ble_eq.mpr h] at hb; exact Bool.noConfusion hb
      omega
    set c := (lo - r + m - 1) / m with hc
    have hcm : lo - r ≤ c * m := ceil_mul_ge (lo - r) m hm
    have hck : c ≤ k := ceil_le_of hm (by omega)
    have hst : lo ≤ r + c * m := by omega
    have hkc : (k - c) * m + c * m = k * m := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hck]
    have hfuel : k - c < (X - lo) / m + 2 := by
      have : (k - c) * m ≤ X - lo := by omega
      have := (Nat.le_div_iff_mul_le hm).mpr this
      omega
    have := mem_progL X m _ (r + c * m) (k - c) hfuel (by omega)
    rwa [show r + c * m + (k - c) * m = r + k * m by omega] at this
  · simp only [cond_true]
    have hlr : lo ≤ r := Nat.ble_eq.mp hb
    have hfuel : k < (X - lo) / m + 2 := by
      have : k * m ≤ X - lo := by omega
      have := (Nat.le_div_iff_mul_le hm).mpr this
      omega
    exact mem_progL X m _ r k hfuel hvX

lemma progFrom_ge {lo X m r x : ℕ} (hm : 0 < m) (h : x ∈ progFrom lo X m r) : lo ≤ x := by
  unfold progFrom at h
  have := mem_progL_pos X m _ _ x h
  cases hb : Nat.ble lo r <;> simp only [hb, cond_true, cond_false] at this
  · have hrl : r < lo := by
      have : ¬ lo ≤ r := fun h' => by rw [Nat.ble_eq.mpr h'] at hb; exact Bool.noConfusion hb
      omega
    have hcm : lo - r ≤ (lo - r + m - 1) / m * m := ceil_mul_ge (lo - r) m hm
    omega
  · have := Nat.ble_eq.mp hb; omega

lemma marksWin_ge {X X0 X1 : ℕ} {roots : List (ℕ × ℕ)} (hr : rootsOK X roots = true) :
    ∀ m ∈ marksWin X0 X1 roots, X0 < m := by
  intro x hx
  unfold marksWin at hx
  rw [mem_dedupS, mem_mergeAllF] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  obtain ⟨⟨p, r⟩, hpr, rfl⟩ := List.mem_map.mp hl
  unfold rootsOK at hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr
  have h5 := (rootsGo_valid X _ 5 roots hr.2 (p, r) hpr).1
  simp only at h5
  have hm : 0 < p * p := by positivity
  rw [mem_mergeL] at hxl
  rcases hxl with h | h
  · have := progFrom_ge hm h; omega
  · have := progFrom_ge hm h; omega

/-- **Every vertex of the window is a mark.** -/
theorem mem_marksWin {X X0 X1 : ℕ} {roots : List (ℕ × ℕ)} (hr : rootsOK X roots = true)
    (hX1 : X1 ≤ X) {v : ℕ} (hv0 : X0 < v) (hvX : v ≤ X1) (hv : ¬ Squarefree (v * v + 1)) :
    v ∈ marksWin X0 X1 roots := by
  unfold rootsOK at hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr
  obtain ⟨hXB, hgo⟩ := hr
  obtain ⟨p, hp, hpv⟩ := exists_prime_sq_dvd hv
  have hp4 := prime_mod_four_of_sq_dvd hp hpv
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p <;> simp_all
    · exact h
  have hv1 : 1 ≤ v := by omega
  have hpv' : p ≤ v := by
    have h1 := Nat.le_of_dvd (by positivity) hpv
    nlinarith
  obtain ⟨r, hmem, hr1, hr2⟩ := rootsGo_spec X _ 5 roots hgo rfl (by omega) p hp4 hp5
    (by omega) (by omega) hp
  have hroot := sqRoots_eq hp (by omega) hr1 (Nat.dvd_of_mod_eq_zero hr2) (v % (p * p)) (by
    simp only [sqRoots, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    have : (v % (p * p)) * (v % (p * p)) + 1 ≡ v * v + 1 [MOD p * p] :=
      Nat.ModEq.add_right 1 (Nat.ModEq.mul (Nat.mod_modEq v _) (Nat.mod_modEq v _))
    exact (Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr hpv))))
  unfold marksWin
  rw [mem_dedupS, mem_mergeAllF]
  refine ⟨_, List.mem_map.mpr ⟨(p, r), hmem, rfl⟩, ?_⟩
  simp only
  rw [mem_mergeL]
  have hm : 0 < p * p := by positivity
  have hv' : v = v % (p * p) + v / (p * p) * (p * p) := by
    have := Nat.mod_add_div v (p * p); linarith
  rcases hroot with e | e
  · left
    have hvv : r + v / (p * p) * (p * p) = v := by rw [← e]; exact hv'.symm
    have := progFrom_mem (lo := X0 + 1) (X := X1) (r := r) (k := v / (p * p)) hm
      (by rw [hvv]; omega) (by rw [hvv]; exact hvX)
    rwa [hvv] at this
  · right
    have hvv : (p * p - r) + v / (p * p) * (p * p) = v := by rw [← e]; exact hv'.symm
    have := progFrom_mem (lo := X0 + 1) (X := X1) (r := p * p - r) (k := v / (p * p)) hm
      (by rw [hvv]; omega) (by rw [hvv]; exact hvX)
    rwa [hvv] at this

/-! #### Checkpoint trees -/

lemma listEq_spec : ∀ a b : List ℕ, listEq a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [listEq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, listEq_spec xs ys h.2]
  | [], _ :: _, h => by simp [listEq] at h
  | _ :: _, [], h => by simp [listEq] at h

lemma btEq_spec : ∀ a b : BT, btEq a b = true → a = b
  | .lf x, .lf y, h => by simp only [btEq] at h; rw [listEq_spec x y h]
  | .nd a b, .nd c d, h => by
    simp only [btEq, Bool.and_eq_true] at h
    rw [btEq_spec a c h.1, btEq_spec b d h.2]
  | .lf _, .nd _ _, h => by simp [btEq] at h
  | .nd _ _, .lf _, h => by simp [btEq] at h

/-! #### One window -/

section
variable {X X0 X1 : ℕ} {roots : List (ℕ × ℕ)}

/-- The vertices `≤ X₀` are covered. -/
def Cov0 (X0 : ℕ) (s : CSt) : Prop :=
  ∀ v, 1 ≤ v → v ≤ X0 → ¬ Squarefree (v * v + 1) → ∃ j < s.cnt, v ∈ s.t.get j

lemma runW_inv {M : List ℕ} (hM : M.Pairwise (· < ·)) : ∀ (ops : List COp) (s sf : CSt),
    ColInv M s → Cov0 X0 s → runC s ops = some sf → ColInv M sf ∧ Cov0 X0 sf ∧ s.last ≤ sf.last := by
  intro ops
  induction ops with
  | nil => intro s sf hs hc h; simp only [runC, Option.some.injEq] at h; subst h; exact ⟨hs, hc, le_rfl⟩
  | cons op ops ih =>
    intro s sf hs hc h
    simp only [runC] at h
    cases hst : stepC s op with
    | none => rw [hst] at h; simp at h
    | some s' =>
      rw [hst] at h
      obtain ⟨hs', hl⟩ := stepC_inv hM hs hst
      have hc' : Cov0 X0 s' := fun v h1 h2 h3 => stepC_cover hs.1 hs.2.1 hst v (hc v h1 h2 h3)
      obtain ⟨r1, r2, r3⟩ := ih s' sf hs' hc' h
      exact ⟨r1, r2, by rcases hl with e | ⟨e, _⟩ <;> omega⟩

lemma certifyW {M : List ℕ} (hr : rootsOK X roots = true) (hX1 : X1 ≤ X)
    (hMw : M = marksWin X0 X1 roots) {s : CSt} (hs : ColInv M s) (hc : Cov0 X0 s) {N : ℕ}
    (hlN : s.last ≤ N) (hNX : N ≤ X1) (hmk : ∀ m ∈ s.marks, N < m) : Statement N := by
  obtain ⟨hF, hcs, hP, hC, hc7, hmks⟩ := hs
  apply statement_of_classes s.cnt s.t.get hP
  · intro v h1 h2 h3
    by_cases hv0 : v ≤ X0
    · exact hc v h1 hv0 h3
    · have hvM : v ∈ M := hMw ▸ mem_marksWin hr hX1 (by omega) (by omega) h3
      have hvl : v ≤ s.last := by
        by_contra hvl
        have : v ∈ s.marks := by
          rw [hmks]; exact List.mem_filter.mpr ⟨hvM, by simpa using (by omega : s.last < v)⟩
        have := hmk v this; omega
      exact hC v hvM hvl
  · exact le_trans hc7 (Nat.div_le_div_right (by omega))

lemma runW_sound {M : List ℕ} (hr : rootsOK X roots = true) (hX1 : X1 ≤ X)
    (hMw : M = marksWin X0 X1 roots) (hM : M.Pairwise (· < ·)) : ∀ (ops : List COp) (s sf : CSt),
    ColInv M s → Cov0 X0 s → runC s ops = some sf → sf.marks = [] →
    ∀ N, s.last ≤ N → N ≤ X1 → Statement N := by
  intro ops
  induction ops with
  | nil =>
    intro s sf hs hc h hmk N hlN hNX
    simp only [runC, Option.some.injEq] at h
    subst h
    exact certifyW hr hX1 hMw hs hc hlN hNX (by simp [hmk])
  | cons op ops ih =>
    intro s sf hs hc h hmk N hlN hNX
    simp only [runC] at h
    cases hst : stepC s op with
    | none => rw [hst] at h; simp at h
    | some s' =>
      rw [hst] at h
      obtain ⟨hs', hl⟩ := stepC_inv hM hs hst
      have hc' : Cov0 X0 s' := fun v h1 h2 h3 => stepC_cover hs.1 hs.2.1 hst v (hc v h1 h2 h3)
      rcases hl with e | ⟨hlt, hmo⟩
      · exact ih s' sf hs' hc' h hmk N (by omega) hNX
      · by_cases hN : s'.last ≤ N
        · exact ih s' sf hs' hc' h hmk N hN hNX
        · apply certifyW hr hX1 hMw hs hc hlN hNX
          intro m hm
          have hsort : s.marks.Pairwise (· < ·) := hs.2.2.2.2.2 ▸ hM.filter _
          have := markOK_spec hsort hmo m hm
          omega

/-- **One window.** -/
theorem winCheck_sound (hr : rootsOK X roots = true) (hX1 : X1 ≤ X) {t0 t1 : BT}
    {cnt0 cnt1 last0 last1 : ℕ} {ops : List COp} (h0 : WinOK X0 t0 cnt0 last0)
    (hw : winCheck X0 X1 roots t0 cnt0 last0 ops t1 cnt1 last1 = true) :
    (∀ N, last0 ≤ N → N ≤ X1 → Statement N) ∧ WinOK X1 t1 cnt1 last1 := by
  unfold winCheck at hw
  simp only [Bool.and_eq_true, Nat.ble_eq] at hw
  obtain ⟨⟨⟨⟨hinc, hl0⟩, hl1⟩, hlen⟩, hrun⟩ := hw
  set M := marksWin X0 X1 roots with hMdef
  have hM := strictInc_spec _ hinc
  have hgt := marksWin_ge (X := X) (X0 := X0) (X1 := X1) hr
  obtain ⟨hF0, _, _, hP0, hC0, hc70⟩ := h0
  have hs0 : ColInv M ⟨cnt0, t0, last0, M⟩ := by
    refine ⟨hF0, hlen, hP0, ?_, hc70, ?_⟩
    · intro m hm hml
      have := hgt m hm; simp only at hml; omega
    · simp only
      symm; rw [List.filter_eq_self]
      intro m hm; have := hgt m hm; simp only [decide_eq_true_eq]; omega
  have hc0 : Cov0 X0 ⟨cnt0, t0, last0, M⟩ := hC0
  cases hR : runC ⟨cnt0, t0, last0, M⟩ ops with
  | none => rw [hR] at hrun; simp at hrun
  | some sf =>
    rw [hR] at hrun
    simp only [Bool.and_eq_true, List.isEmpty_iff, Nat.beq_eq] at hrun
    obtain ⟨⟨⟨hmk, hcnt⟩, hbt⟩, hlast⟩ := hrun
    refine ⟨fun N hN1 hN2 => runW_sound hr hX1 rfl hM ops _ sf hs0 hc0 hR hmk N hN1 hN2, ?_⟩
    obtain ⟨hsf, hcf, _⟩ := runW_inv hM ops _ sf hs0 hc0 hR
    obtain ⟨hFf, hcsf, hPf, hCf, hc7f, hmkf⟩ := hsf
    have ht := btEq_spec _ _ hbt
    subst ht; subst hcnt; subst hlast
    refine ⟨hFf, hcsf, hl1, hPf, ?_, hc7f⟩
    intro v h1 h2 h3
    by_cases hv0 : v ≤ X0
    · exact hcf v h1 hv0 h3
    · have hvM : v ∈ M := mem_marksWin hr hX1 (by omega) h2 h3
      have hvl : v ≤ sf.last := by
        by_contra hvl
        have : v ∈ sf.marks := by
          rw [hmkf]; exact List.mem_filter.mpr ⟨hvM, by simpa using (by omega : sf.last < v)⟩
        rw [hmk] at this; simp at this
      exact hCf v hvM hvl

end

end

end Erdos848
