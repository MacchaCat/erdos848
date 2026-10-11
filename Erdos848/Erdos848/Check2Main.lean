import Erdos848.Check2Ex

/-!
# Soundness of the §10 checker, part 5: one interval

`countBounds2_of_iv`: if `checkIv2` accepts an interval `[lo, hi]` (with a valid prime table,
admissible prefix table, structure lists and Lemma E2 table), then `CountBounds2 N` holds for
every `N ∈ [lo, hi]`.
-/

namespace Erdos848

open Finset ErdosComp

/-! ### Buckets -/

lemma bucketsGo_cover (N : ℕ) : ∀ f xa, N ≤ xa + f → ∀ b, xa ≤ b → b ≤ N → xa < N →
    ∃ bk ∈ bucketsGo N f xa, bk.1 ≤ b ∧ b ≤ bk.2 ∧ xa ≤ bk.1 ∧ bk.2 ≤ N
  | 0, xa, hf, b, h1, h2, h3 => by omega
  | f + 1, xa, hf, b, h1, h2, h3 => by
    simp only [bucketsGo, if_pos h3]
    set xb := min N (max (xa + 1) (xa * 13 / 10))
    by_cases hb : b ≤ xb
    · exact ⟨(xa, xb), List.mem_cons_self .., h1, hb, le_rfl, min_le_left _ _⟩
    · have hxb : xa + 1 ≤ xb ∨ xb = N := by
        rcases min_choice N (max (xa + 1) (xa * 13 / 10)) with e | e
        · right; exact e
        · left; rw [show xb = max (xa + 1) (xa * 13 / 10) from e]; exact le_max_left _ _
      have hxbN : xb ≤ N := min_le_left _ _
      obtain ⟨bk, hbk, h⟩ := bucketsGo_cover N f xb (by omega) b (by omega) h2 (by omega)
      exact ⟨bk, List.mem_cons_of_mem _ hbk, h.1, h.2.1, by omega, h.2.2.2⟩

lemma buckets_cover {N b : ℕ} (hb1 : 1 ≤ b) (hbN : b ≤ N) (hN : 2 ≤ N) :
    ∃ bk ∈ buckets N, bk.1 ≤ b ∧ b ≤ bk.2 ∧ 1 ≤ bk.1 ∧ bk.2 ≤ N :=
  bucketsGo_cover N N 1 (by omega) b hb1 hbN (by omega)

lemma maxBk_spec (f : ℕ × ℕ → BkD → Option ℚ) : ∀ (bks : List (ℕ × ℕ)) (ds : List BkD) (m : ℚ),
    maxBk f bks ds = some m → ∀ bk ∈ bks, ∃ d v, f bk d = some v ∧ v ≤ m
  | [], [], _, _, bk, hbk => by simp at hbk
  | b :: bs, d :: ds, m, h, bk, hbk => by
    simp only [maxBk] at h
    cases h1 : f b d with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : maxBk f bs ds with
      | none => rw [h1, h2] at h; simp at h
      | some y =>
        rw [h1, h2] at h
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hbk with rfl | hbk
        · exact ⟨d, x, h1, le_max_left _ _⟩
        · obtain ⟨d', v, hv, hvy⟩ := maxBk_spec f bs ds y h2 bk hbk
          exact ⟨d', v, hv, hvy.trans (le_max_right _ _)⟩
  | [], _ :: _, _, h, _, _ => by simp [maxBk] at h
  | _ :: _, [], _, h, _, _ => by simp [maxBk] at h

/-- A witness `b ≤ hi` lies in a bucket whose value is at most the maximum. -/
lemma bucket_of_maxBk {f : ℕ × ℕ → BkD → Option ℚ} {hi : ℕ} {ds : List BkD} {m : ℚ}
    (h : maxBk f (buckets hi) ds = some m) {b : ℕ} (hb1 : 1 ≤ b) (hbh : b ≤ hi) (hhi : 2 ≤ hi) :
    ∃ bk : ℕ × ℕ, bk.1 ≤ b ∧ b ≤ bk.2 ∧ 1 ≤ bk.1 ∧ bk.2 ≤ hi ∧ ∃ d v, f bk d = some v ∧ v ≤ m := by
  obtain ⟨bk, hbk, h1, h2, h3, h4⟩ := buckets_cover hb1 hbh hhi
  exact ⟨bk, h1, h2, h3, h4, maxBk_spec f _ ds m h bk hbk⟩

/-! ### The data -/

structure StrsOK (S : List StrE) (ci : ℕ) (D : List DiscE) : Prop where
  sorted : sortedBm S = true
  valid : S.all (strValid D) = true
  comp : ∀ e ≤ 3, completeE ci e S = true

structure DataOK (S : Strs) (D : List DiscE) : Prop where
  any5 : StrsOK S.any5 0 D
  odd : StrsOK S.odd 1 D
  even : StrsOK S.even 2 D
  disc : D.all discOK = true

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- A successful shared-set evaluation gives `Mid + Ex` for every witness of the bucket. -/
lemma sh_of_shQ {strs : List StrE} {ci : ℕ} {D : List DiscE} (hS : StrsOK strs ci D)
    (hD : D.all discOK = true) (hci : ci ≤ 2) {N hi pc xb : ℕ} {d : BkD} {s : ℚ}
    (h : shQ lk strs (bNsOf hi strs) hi pc xb d = some s) (hN : N ≤ hi) (hxb : xb ≤ 160000000)
    {b : ℕ} (hb1 : 1 ≤ b) (hbx : b ≤ xb) (hc : ConsP ci b) :
    ∃ E : ℚ, ((exSet N b d.Y).card : ℝ) ≤ E ∧ midB N pc d.Y + E ≤ (s : ℝ) := by
  unfold shQ at h
  split_ifs at h with hc'
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hY, hok⟩ := hc'
  refine ⟨(d.En : ℚ) / ((d.Y : ℚ) * KE), ?_, ?_⟩
  · have := ex_le hci hS.sorted hS.valid hS.comp hD hN hxb hY hok hb1 hbx hc
    push_cast; exact this
  · have h1 := midB_mono hN pc d.Y
    have h2 := midB_le hlk hi pc d.Y
    push_cast
    linarith

end

/-! ### From the bound to `c₇` -/

lemma le_c7_of_lt {x lo N : ℕ} (hx : (x : ℝ) < ((lo : ℝ) - 6) / 25) (hlo : lo ≤ N) : x ≤ c7 N := by
  have hc7 : ((N : ℝ) - 6) / 25 ≤ c7 N := by
    unfold c7
    have := Nat.div_add_mod (N + 18) 25
    have := Nat.mod_lt (N + 18) (show 0 < 25 by norm_num)
    have h : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast h
    linarith
  have hloR : (lo : ℝ) ≤ N := by exact_mod_cast hlo
  have : (x : ℝ) < c7 N + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

lemma below_spec {lo : ℕ} {o : Option ℚ} (h : below lo o = true) :
    ∃ v, o = some v ∧ (v : ℝ) < ((lo : ℝ) - 6) / 25 := by
  cases o with
  | none => simp [below] at h
  | some v =>
    simp only [below, decide_eq_true_eq] at h
    refine ⟨v, rfl, ?_⟩
    have := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at this; exact this

/-- `resR` at any `L ≤ L'` through the checker's linear form. -/
lemma resR_le_at {lk : Lk} (hlk : ∀ x, lk x = stAt x) {L L' : ℕ} (hL : L ≤ L') (q z pc dA : ℕ)
    (hq : 0 < q) (excl : Finset ℕ) (exclL : List ℕ) (hex : ∀ p, p ∈ excl ↔ p ∈ exclL)
    (h0 : 0 ≤ (resLin lk q z pc dA exclL).1) :
    resR (L : ℝ) q z pc dA excl ≤ ((evalLin (resLin lk q z pc dA exclL) (L' : ℚ) : ℚ) : ℝ) := by
  have := resR_le hlk (L : ℝ) (Nat.cast_nonneg L) q z pc dA hq excl exclL hex
  unfold evalLin; push_cast
  have h0R : (0 : ℝ) ≤ (((resLin lk q z pc dA exclL).1 : ℚ) : ℝ) := by exact_mod_cast h0
  have hLR : (L : ℝ) ≤ L' := by exact_mod_cast hL
  nlinarith

lemma lemBR_le_at {lk : Lk} (hlk : ∀ x, lk x = stAt x) {L L' : ℕ} (hL : L ≤ L') (zB pT dB : ℕ)
    (h0 : 0 ≤ (lemBLin lk zB pT dB).1) :
    lemBR (L : ℝ) zB pT dB ≤ ((evalLin (lemBLin lk zB pT dB) (L' : ℚ) : ℚ) : ℝ) := by
  have := lemBR_le hlk (L : ℝ) (Nat.cast_nonneg L) zB pT dB
  unfold evalLin; push_cast
  have h0R : (0 : ℝ) ≤ (((lemBLin lk zB pT dB).1 : ℚ) : ℝ) := by exact_mod_cast h0
  have hLR : (L : ℝ) ≤ L' := by exact_mod_cast hL
  nlinarith

lemma prmOK_spec {p : Prm2} (h : prmOK p = true) :
    Odd p.dA ∧ Odd p.dB ∧ Odd p.dC ∧ 5 ≤ p.z₂ ∧ 1 ≤ p.Yt := by
  unfold prmOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨Nat.odd_iff.mpr h1, Nat.odd_iff.mpr h2, Nat.odd_iff.mpr h3, h4, h5⟩

lemma consP0 {b : ℕ} (h : b % 25 = 7 ∨ b % 25 = 18) : ConsP 0 b :=
  ⟨fun _ h5 => by omega, fun h => by omega, fun h => by omega⟩

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- **Case I.b** of an interval. -/
theorem caseIb_of {S : Strs} {D : List DiscE} (hSD : DataOK S D) {lo hi N : ℕ} {p : Prm2}
    {ds : List BkD} (hb : below lo (caseIbQ lk S hi p ds) = true) (hp : prmOK p = true)
    (hlo : lo ≤ N) (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h7 : 7 ≤ lo) :
    ∀ b b', Witness N b → b % 25 = 7 → Witness N b' → b' % 25 = 18 →
      badCount N (fun a => a % 25 = 18 ∧ b' ≤ a) b +
        badCount N (fun a => a % 25 = 7 ∧ b ≤ a) b' ≤ c7 N := by
  obtain ⟨v, hv, hvlt⟩ := below_spec hb
  obtain ⟨hdA, -, -, -, -⟩ := prmOK_spec hp
  unfold caseIbQ at hv
  dsimp only at hv
  split_ifs at hv with hr
  set r := resLin lk 25 p.z p.pc p.dA [5]
  cases hm : maxBk (fun b d => (shQ lk S.any5 (bNsOf hi S.any5) hi p.pc b.2 d).map
      (fun s => evalLin r ((hi + 1 - b.1 : ℕ) : ℚ) + s)) (buckets hi) ds with
  | none => rw [hm] at hv; simp at hv
  | some m =>
  rw [hm] at hv
  simp only [Option.map_some, Option.some.injEq] at hv
  subst hv
  intro b b' hw h7b hw' h18
  have hr0 : 0 ≤ r.1 := by simpa using hr
  -- the bucket of a witness
  have key : ∀ c, Witness N c → (c % 25 = 7 ∨ c % 25 = 18) → ∃ Y : ℕ, ∃ E : ℚ,
      ((exSet N c Y).card : ℝ) ≤ E ∧
      resR ((N + 1 - c : ℕ) : ℝ) 25 p.z p.pc p.dA {5} + midB N p.pc Y + E ≤ (m : ℝ) := by
    intro c hw hc
    obtain ⟨bk, h1, h2, h3, h4, d, v, hf, hvm⟩ :=
      bucket_of_maxBk hm hw.1 (hw.2.1.trans hhi) (by omega)
    cases hs : shQ lk S.any5 (bNsOf hi S.any5) hi p.pc bk.2 d with
    | none => rw [hs] at hf; simp at hf
    | some s =>
    rw [hs] at hf
    simp only [Option.map_some, Option.some.injEq] at hf
    subst hf
    obtain ⟨E, hE, hmid⟩ := sh_of_shQ hlk hSD.any5 hSD.disc (by norm_num) hs hhi (by omega) hw.1 h2
      (consP0 hc)
    refine ⟨d.Y, E, hE, ?_⟩
    have hR := resR_le_at hlk (L := N + 1 - c) (L' := hi + 1 - bk.1) (by omega) 25 p.z p.pc p.dA
      (by norm_num) {5} [5] (by intro q; simp) hr0
    have hvm' : ((evalLin r ((hi + 1 - bk.1 : ℕ) : ℚ) + s : ℚ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hvm
    push_cast at hvm'
    linarith
  obtain ⟨Y, E, hE, hY⟩ := key b hw (Or.inl h7b)
  obtain ⟨Y', E', hE', hY'⟩ := key b' hw' (Or.inr h18)
  have := caseIb2 N b b' p.z p.pc p.dA Y Y' E E' hw h7b hw' h18 hdA hE hE'
  apply le_c7_of_lt _ hlo
  push_cast at hvlt this ⊢
  linarith

end

lemma nSOK_spec {x : ℕ} (h : nSOK x = true) : PrefixOK x (nSOf x) := by
  unfold nSOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold PrefixOK
  rw [← ulProd_u1 h.1]
  exact h.2

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- **Case II** of an interval. -/
theorem caseII_of {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) {S : Strs} {D : List DiscE}
    (hSD : DataOK S D) {lo hi N : ℕ} {p : Prm2} {ds : List BkD}
    (hb : below lo (caseIIQ lk pre S hi p ds) = true) (hp : prmOK p = true)
    (hlo : lo ≤ N) (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h7 : 7 ≤ lo) :
    ∀ b, Witness N b → IsStar b → b % 2 = 0 →
      badCount N (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount2 N b ≤ c7 N := by
  obtain ⟨v, hv, hvlt⟩ := below_spec hb
  obtain ⟨hdA, -, hdC, hz₂, hYt⟩ := prmOK_spec hp
  unfold caseIIQ at hv
  dsimp only at hv
  split_ifs at hv with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hcc, hr0⟩ := hc
  set r := resLin lk 25 p.z p.pc p.dA [2, 5]
  set cc := cConst lk p.z₁ p.z₂ p.pB p.pc p.dC
  cases ht : tailQ lk pre hi p.pB p.Yt p.Kt with
  | none => rw [ht] at hv; simp at hv
  | some t =>
  cases hm : maxBk (fun b d => if nSOK b.2 then (shQ lk S.even (bNsOf hi S.even) hi p.pc b.2 d).map
      (fun s => min (coreF cc (mkCF cc) (2 * (2 * hi + 1 - b.1)) 2 (nSOf b.2))
        (coreF cc (mkCF cc) (4 * hi) 1 (nSOf b.2)) + s) else none) (buckets hi) ds with
  | none => rw [ht, hm] at hv; simp at hv
  | some m =>
  rw [ht, hm] at hv
  simp only [Option.some.injEq] at hv
  subst hv
  intro b hw hs he
  obtain ⟨bk, h1, h2, h3, h4, d, v, hf, hvm⟩ := bucket_of_maxBk hm hw.1 (hw.2.1.trans hhi) (by omega)
  split_ifs at hf with hns
  cases hsh : shQ lk S.even (bNsOf hi S.even) hi p.pc bk.2 d with
  | none => rw [hsh] at hf; simp at hf
  | some s =>
  rw [hsh] at hf
  simp only [Option.map_some, Option.some.injEq] at hf
  subst hf
  obtain ⟨E, hE, hmid⟩ := sh_of_shQ hlk hSD.even hSD.disc (by norm_num) hsh hhi (by omega) hw.1 h2
    ⟨fun h => by omega, fun h => by omega, fun _ => he⟩
  obtain ⟨τ₁, hτ₁, hc₁⟩ := coreB_le hlk p.z₁ p.z₂ p.pB p.pc p.dC (nSOf bk.2)
    (2 * (2 * hi + 1 - bk.1)) 2 (((2 * N + 1 - b : ℕ) : ℝ) / 2) (by positivity)
    (by
      have hb' : ((2 * N + 1 - b : ℕ) : ℝ) ≤ ((2 * hi + 1 - bk.1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * N + 1 - b ≤ 2 * hi + 1 - bk.1)
      push_cast [Nat.cast_mul]; linarith) hcc
  obtain ⟨τ₂, hτ₂, hc₂⟩ := coreB_le hlk p.z₁ p.z₂ p.pB p.pc p.dC (nSOf bk.2) (4 * hi) 1 (N : ℝ)
    (Nat.cast_nonneg N)
    (by have : (N : ℝ) ≤ hi := by exact_mod_cast hhi
        push_cast; linarith) hcc
  have := caseII2 N b bk.2 p.z p.pc p.dA d.Y p.z₁ p.z₂ p.pB (nSOf bk.2) p.dC p.Yt τ₁ τ₂ E
    hw hs he h2 hdA hdC hz₂ hτ₁ hτ₂ hYt (nSOK_spec hns) hE
  have hR := resR_le_at hlk (L := N) (L' := hi) hhi 25 p.z p.pc p.dA (by norm_num) {2, 5} [2, 5]
    (by intro q; simp) (by simpa using hr0)
  have hT := (tailB_mono hhi p.pB p.Yt).trans (tailB_le hlk hpre hi p.pB p.Yt p.Kt t ht)
  have hmin : min (coreB (((2 * N + 1 - b : ℕ) : ℝ) / 2) 2 p.z₁ p.z₂ p.pB p.pc (nSOf bk.2) p.dC τ₁)
      (coreB (N : ℝ) 1 p.z₁ p.z₂ p.pB p.pc (nSOf bk.2) p.dC τ₂) ≤
      ((min (coreF cc (mkCF cc) (2 * (2 * hi + 1 - bk.1)) 2 (nSOf bk.2))
        (coreF cc (mkCF cc) (4 * hi) 1 (nSOf bk.2)) : ℚ) : ℝ) := by
    push_cast; exact min_le_min (by push_cast at hc₁; exact hc₁) (by push_cast at hc₂; exact hc₂)
  have hvm' := (Rat.cast_le (K := ℝ)).mpr hvm
  apply le_c7_of_lt _ hlo
  push_cast at hvlt this hvm' hmin ⊢
  unfold evalLin at hR hvlt
  push_cast at hR hvlt
  linarith

/-- The shared part of case III: an odd witness in a bucket. -/
lemma shb_of {S : Strs} {D : List DiscE} (hSD : DataOK S D) {hi N : ℕ} {p : Prm2} {ds : List BkD}
    {sm : ℚ} (hsh : shbQ lk S hi p ds = some sm) (hhi : N ≤ hi) (hhi' : hi ≤ 160000000)
    (h2 : 2 ≤ hi) {b : ℕ} (hw : Witness N b) (hodd : b % 2 = 1) :
    ∃ xb Y nS : ℕ, ∃ τ : ℝ, ∃ E : ℚ, b ≤ xb ∧ PrefixOK xb nS ∧ 0 ≤ τ ∧
      ((exSet N b Y).card : ℝ) ≤ E ∧
      min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) p.zB p.pB p.dB)
        (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 p.z₁ p.z₂ p.pB p.pc nS p.dC τ) +
        midB N p.pc Y + E ≤ (sm : ℝ) := by
  unfold shbQ at hsh
  dsimp only at hsh
  split_ifs at hsh with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hcc, hlb⟩ := hc
  obtain ⟨bk, hb1, hb2, hb3, hb4, d, v, hf, hvm⟩ := bucket_of_maxBk hsh hw.1 (hw.2.1.trans hhi) h2
  split_ifs at hf with hns
  cases hs : shQ lk S.odd (bNsOf hi S.odd) hi p.pc bk.2 d with
  | none => rw [hs] at hf; simp at hf
  | some s =>
  rw [hs] at hf
  simp only [Option.map_some, Option.some.injEq] at hf
  subst hf
  obtain ⟨E, hE, hmid⟩ := sh_of_shQ hlk hSD.odd hSD.disc (by norm_num) hs hhi (by omega) hw.1 hb2
    ⟨fun h => by omega, fun _ => hodd, fun h => by omega⟩
  obtain ⟨τ, hτ, hcB⟩ := coreB_le hlk p.z₁ p.z₂ p.pB p.pc p.dC (nSOf bk.2)
    (hi + 1 - bk.1) 1 (((N + 1 - b : ℕ) : ℝ) / 4) (by positivity)
    (by
      have hb' : ((N + 1 - b : ℕ) : ℝ) ≤ ((hi + 1 - bk.1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : N + 1 - b ≤ hi + 1 - bk.1)
      linarith) hcc
  refine ⟨bk.2, d.Y, nSOf bk.2, τ, E, hb2, nSOK_spec hns, hτ, hE, ?_⟩
  have hB := lemBR_le_at hlk (L := N + 1 - b) (L' := hi + 1 - bk.1) (by omega) p.zB p.pB p.dB hlb
  have hvm' := (Rat.cast_le (K := ℝ)).mpr hvm
  push_cast at hvm' hcB
  have hmin : min (23 * lemBR ((N + 1 - b : ℕ) : ℝ) p.zB p.pB p.dB)
      (coreB (((N + 1 - b : ℕ) : ℝ) / 4) 1 p.z₁ p.z₂ p.pB p.pc (nSOf bk.2) p.dC τ) ≤
      min (23 * (((evalLin (lemBLin lk p.zB p.pB p.dB) ((hi + 1 - bk.1 : ℕ) : ℚ)) : ℚ) : ℝ))
        ((coreF (cConst lk p.z₁ p.z₂ p.pB p.pc p.dC) (mkCF (cConst lk p.z₁ p.z₂ p.pB p.pc p.dC))
          (hi + 1 - bk.1) 1 (nSOf bk.2) : ℚ) : ℝ) :=
    min_le_min (by linarith) (by push_cast; exact hcB)
  push_cast at hmin
  linarith

end

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- **Case III.1** of an interval. -/
theorem caseIII1_of {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) {S : Strs} {D : List DiscE}
    (hSD : DataOK S D) {lo hi N : ℕ} {p : Prm2} {ds : List BkD}
    (hb : below lo (caseIII1Q lk pre S hi p ds) = true) (hp : prmOK p = true)
    (hlo : lo ≤ N) (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h7 : 7 ≤ lo) :
    ∀ b₁ b₃, Witness N b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness N b₃ → IsStar b₃ → b₃ % 4 = 3 →
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
      badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
      starCount N b₁ 1 + starCount N b₃ 3 ≤ c7 N := by
  obtain ⟨v, hv, hvlt⟩ := below_spec hb
  obtain ⟨hdA, hdB, hdC, hz₂, hYt⟩ := prmOK_spec hp
  unfold caseIII1Q at hv
  dsimp only at hv
  split_ifs at hv with hr0
  cases hsh : shbQ lk S hi p ds with
  | none => rw [hsh] at hv; simp at hv
  | some sm =>
  cases ht : tailQ lk pre hi p.pB p.Yt p.Kt with
  | none => rw [hsh, ht] at hv; simp at hv
  | some t =>
  rw [hsh, ht] at hv
  simp only [Option.some.injEq] at hv
  subst hv
  intro b₁ b₃ hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
  obtain ⟨xb₁, Y₁, nS₁, τ₁, E₁, hx₁, hp₁, hτ₁, hE₁, hv₁⟩ :=
    shb_of hlk hSD hsh hhi hhi' (by omega) hw₁ (by omega)
  obtain ⟨xb₃, Y₃, nS₃, τ₃, E₃, hx₃, hp₃, hτ₃, hE₃, hv₃⟩ :=
    shb_of hlk hSD hsh hhi hhi' (by omega) hw₃ (by omega)
  have := caseIII1_2 N b₁ b₃ xb₁ xb₃ p.z p.pc p.dA Y₁ Y₃ p.zB p.pB p.dB p.z₁ p.z₂ nS₁ nS₃ p.dC p.Yt
    τ₁ τ₃ E₁ E₃ hw₁ hs₁ hr₁ hw₃ hs₃ hr₃ hx₁ hx₃ hdA hdB hdC hz₂ hτ₁ hτ₃ hYt hp₁ hp₃ hE₁ hE₃
  have hR := resR_le_at hlk (L := N) (L' := hi) hhi 100 p.z p.pc p.dA (by norm_num) {2, 5} [2, 5]
    (by intro q; simp) (by simpa using hr0)
  have hT := (tailB_mono hhi p.pB p.Yt).trans (tailB_le hlk hpre hi p.pB p.Yt p.Kt t ht)
  apply le_c7_of_lt _ hlo
  push_cast at hvlt this ⊢
  unfold evalLin at hR hvlt
  push_cast at hR hvlt
  linarith

/-- **Case III.2 β** of an interval. -/
theorem caseIII2beta_of {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) {S : Strs} {D : List DiscE}
    (hSD : DataOK S D) {lo hi N : ℕ} {p : Prm2} {ds : List BkD}
    (hb : below lo (caseIII2bQ lk pre S hi p ds) = true) (hp : prmOK p = true)
    (hlo : lo ≤ N) (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h7 : 7 ≤ lo) :
    ∀ b r s s', Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
      ((s = 7 ∧ s' = 18) ∨ (s = 18 ∧ s' = 7)) →
      classCount N (Unsieved s r) +
      badCount N (fun a => (a % 25 = s ∧ ¬ a % 4 = 4 - r) ∨ (a % 25 = s' ∧ a % 4 = r)) b +
      starCount N b r ≤ c7 N := by
  obtain ⟨v, hv, hvlt⟩ := below_spec hb
  obtain ⟨hdA, hdB, hdC, hz₂, hYt⟩ := prmOK_spec hp
  unfold caseIII2bQ at hv
  dsimp only at hv
  split_ifs at hv with hr0
  cases hsh : shbQ lk S hi p ds with
  | none => rw [hsh] at hv; simp at hv
  | some sm =>
  cases ht : tailQ lk pre hi p.pB p.Yt p.Kt with
  | none => rw [hsh, ht] at hv; simp at hv
  | some t =>
  rw [hsh, ht] at hv
  simp only [Option.some.injEq] at hv
  subst hv
  intro b r s s' hw hbs hbr hr hss
  obtain ⟨xb, Y, nS, τ, E, hx, hpr, hτ, hE, hvb⟩ :=
    shb_of hlk hSD hsh hhi hhi' (by omega) hw (by omega)
  have := caseIII2beta2 N b r s s' xb p.z p.pc p.dA Y p.zB p.pB p.dB p.z₁ p.z₂ nS p.dC p.Yt τ E
    hw hbs hbr hr hss hx hdA hdB hdC hz₂ hτ hYt hpr hE
  have hR := resR_le_at hlk (L := N) (L' := hi) hhi 100 p.z p.pc p.dA (by norm_num) {2, 5} [2, 5]
    (by intro q; simp) (by simpa using hr0)
  have hT := (tailB_mono hhi p.pB p.Yt).trans (tailB_le hlk hpre hi p.pB p.Yt p.Kt t ht)
  have hNR : (N : ℝ) / 100 + 1 ≤ (hi : ℝ) / 100 + 1 := by
    have : (N : ℝ) ≤ hi := by exact_mod_cast hhi
    linarith
  apply le_c7_of_lt _ hlo
  push_cast at hvlt this ⊢
  unfold evalLin at hR hvlt
  push_cast at hR hvlt
  linarith

/-- An `A₇`/`A₁₈` witness in a bucket of the any-class list (case III.2 α). -/
lemma any5_of {S : Strs} {D : List DiscE} (hSD : DataOK S D) {hi N : ℕ} {p : Prm2}
    {ds : List BkD} {k : ℚ} (hk : 0 ≤ k) {m : ℚ}
    (hm : maxBk (fun b d => (shQ lk S.any5 (bNsOf hi S.any5) hi p.pc b.2 d).map
      (fun s => k * evalLin (resLin lk 100 p.z p.pc p.dA [2, 5]) ((hi + 1 - b.1 : ℕ) : ℚ) + s))
      (buckets hi) ds = some m)
    (hr0 : 0 ≤ (resLin lk 100 p.z p.pc p.dA [2, 5]).1)
    (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h2 : 2 ≤ hi) {c : ℕ} (hw : Witness N c)
    (hc : c % 25 = 7 ∨ c % 25 = 18) :
    ∃ Y : ℕ, ∃ E : ℚ, ((exSet N c Y).card : ℝ) ≤ E ∧
      (k : ℝ) * resR ((N + 1 - c : ℕ) : ℝ) 100 p.z p.pc p.dA {2, 5} + midB N p.pc Y + E ≤ (m : ℝ) := by
  obtain ⟨bk, h1, h2', h3, h4, d, v, hf, hvm⟩ := bucket_of_maxBk hm hw.1 (hw.2.1.trans hhi) h2
  cases hs : shQ lk S.any5 (bNsOf hi S.any5) hi p.pc bk.2 d with
  | none => rw [hs] at hf; simp at hf
  | some s =>
  rw [hs] at hf
  simp only [Option.map_some, Option.some.injEq] at hf
  subst hf
  obtain ⟨E, hE, hmid⟩ := sh_of_shQ hlk hSD.any5 hSD.disc (by norm_num) hs hhi (by omega) hw.1 h2'
    (consP0 hc)
  refine ⟨d.Y, E, hE, ?_⟩
  have hR := resR_le_at hlk (L := N + 1 - c) (L' := hi + 1 - bk.1) (by omega) 100 p.z p.pc p.dA
    (by norm_num) {2, 5} [2, 5] (by intro q; simp) hr0
  have hvm' := (Rat.cast_le (K := ℝ)).mpr hvm
  push_cast at hvm'
  have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
  unfold evalLin at hvm' hR
  push_cast at hvm' hR
  nlinarith

/-- Same with the class bound at `N` (the two-witness bound of case III.2 α). -/
lemma any5N_of {S : Strs} {D : List DiscE} (hSD : DataOK S D) {hi N : ℕ} {p : Prm2}
    {ds : List BkD} {m : ℚ}
    (hm : maxBk (fun b d => (shQ lk S.any5 (bNsOf hi S.any5) hi p.pc b.2 d).map
      (fun s => evalLin (resLin lk 100 p.z p.pc p.dA [2, 5]) (hi : ℚ) + s))
      (buckets hi) ds = some m)
    (hr0 : 0 ≤ (resLin lk 100 p.z p.pc p.dA [2, 5]).1)
    (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h2 : 2 ≤ hi) {c : ℕ} (hw : Witness N c)
    (hc : c % 25 = 7 ∨ c % 25 = 18) :
    ∃ Y : ℕ, ∃ E : ℚ, ((exSet N c Y).card : ℝ) ≤ E ∧
      resR (N : ℝ) 100 p.z p.pc p.dA {2, 5} + midB N p.pc Y + E ≤ (m : ℝ) := by
  obtain ⟨bk, h1, h2', h3, h4, d, v, hf, hvm⟩ := bucket_of_maxBk hm hw.1 (hw.2.1.trans hhi) h2
  cases hs : shQ lk S.any5 (bNsOf hi S.any5) hi p.pc bk.2 d with
  | none => rw [hs] at hf; simp at hf
  | some s =>
  rw [hs] at hf
  simp only [Option.map_some, Option.some.injEq] at hf
  subst hf
  obtain ⟨E, hE, hmid⟩ := sh_of_shQ hlk hSD.any5 hSD.disc (by norm_num) hs hhi (by omega) hw.1 h2'
    (consP0 hc)
  refine ⟨d.Y, E, hE, ?_⟩
  have hR := resR_le_at hlk (L := N) (L' := hi) hhi 100 p.z p.pc p.dA
    (by norm_num) {2, 5} [2, 5] (by intro q; simp) hr0
  have hvm' := (Rat.cast_le (K := ℝ)).mpr hvm
  push_cast at hvm'
  linarith

end

section
variable {lk : Lk} (hlk : ∀ x, lk x = stAt x)
include hlk

/-- **Case III.2 α** of an interval. -/
theorem caseIII2alpha_of {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) {S : Strs} {D : List DiscE}
    (hSD : DataOK S D) {lo hi N : ℕ} {p : Prm2} {ds ds' : List BkD}
    (hb : below lo (caseIII2aQ lk pre S hi p ds ds') = true) (hp : prmOK p = true)
    (hlo : lo ≤ N) (hhi : N ≤ hi) (hhi' : hi ≤ 160000000) (h7 : 7 ≤ lo) :
    ∀ b r c c', Witness N b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
      Witness N c → c % 25 = 7 → ¬ c % 4 = r → Witness N c' → c' % 25 = 18 → ¬ c' % 4 = r →
      (badCount N (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) ∨
          (a % 25 = 7 ∧ a % 2 = 0 ∧ c ≤ a) ∨ (a % 25 = 18 ∧ a % 2 = 0 ∧ c' ≤ a)) b +
        badCount N (fun a => Unsieved 7 r a ∧ c ≤ a) c' +
        badCount N (fun a => Unsieved 18 r a ∧ c' ≤ a) c +
        starCount N b r ≤ c7 N) ∨
      (classCount N (Unsieved 7 r) +
        badCount N (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Unsieved 7 r a ∧ ¬ Unsieved 18 r a) b +
        badCount N (Unsieved 18 r) c +
        starCount N b r ≤ c7 N) := by
  obtain ⟨v, hv, hvlt⟩ := below_spec hb
  obtain ⟨hdA, hdB, hdC, hz₂, hYt⟩ := prmOK_spec hp
  unfold caseIII2aQ at hv
  dsimp only at hv
  split_ifs at hv with hr0
  have hr0' : 0 ≤ (resLin lk 100 p.z p.pc p.dA [2, 5]).1 := by simpa using hr0
  cases hsh : shbQ lk S hi p ds with
  | none => rw [hsh] at hv; simp at hv
  | some sm =>
  cases ht : tailQ lk pre hi p.pB p.Yt p.Kt with
  | none => rw [hsh, ht] at hv; simp at hv
  | some t =>
  cases hm3 : maxBk (fun b d => (shQ lk S.any5 (bNsOf hi S.any5) hi p.pc b.2 d).map
      (fun s => 3 * evalLin (resLin lk 100 p.z p.pc p.dA [2, 5]) ((hi + 1 - b.1 : ℕ) : ℚ) + s))
      (buckets hi) ds' with
  | none => rw [hsh, ht, hm3] at hv; simp at hv
  | some m3 =>
  cases hm1 : maxBk (fun b d => (shQ lk S.any5 (bNsOf hi S.any5) hi p.pc b.2 d).map
      (fun s => evalLin (resLin lk 100 p.z p.pc p.dA [2, 5]) (hi : ℚ) + s)) (buckets hi) ds' with
  | none => rw [hsh, ht, hm3, hm1] at hv; simp at hv
  | some m1 =>
  rw [hsh, ht, hm3, hm1] at hv
  simp only [Option.some.injEq] at hv
  subst hv
  intro b r c c' hw hbs hbr hr hwc hc7 hcr hwc' hc18 hcr'
  obtain ⟨xb, Y, nS, τ, E, hx, hpr, hτ, hE, hvb⟩ :=
    shb_of hlk hSD hsh hhi hhi' (by omega) hw (by unfold IsStar at hbs; omega)
  obtain ⟨Yc, Ec, hEc, hc3⟩ := any5_of hlk hSD (k := 3) (by norm_num) hm3 hr0' hhi hhi' (by omega)
    hwc (Or.inl hc7)
  obtain ⟨Yc', Ec', hEc', hc3'⟩ := any5_of hlk hSD (k := 3) (by norm_num) hm3 hr0' hhi hhi' (by omega)
    hwc' (Or.inr hc18)
  obtain ⟨Yd, Ed, hEd, hc1⟩ := any5N_of hlk hSD hm1 hr0' hhi hhi' (by omega) hwc (Or.inl hc7)
  have A3 := (caseIII2alpha2 N b r c c' xb p.z p.pc p.dA Y Yc Yc' p.zB p.pB p.dB p.z₁ p.z₂ nS p.dC
    p.Yt τ E Ec Ec' hw hbs hbr hr hwc hc7 hcr hwc' hc18 hcr' hx hdA hdB hdC hz₂ hτ hYt hpr hE hEc
    hEc').1
  have A2 := (caseIII2alpha2 N b r c c' xb p.z p.pc p.dA Y Yd Yc' p.zB p.pB p.dB p.z₁ p.z₂ nS p.dC
    p.Yt τ E Ed Ec' hw hbs hbr hr hwc hc7 hcr hwc' hc18 hcr' hx hdA hdB hdC hz₂ hτ hYt hpr hE hEd
    hEc').2
  have hR := resR_le_at hlk (L := N) (L' := hi) hhi 100 p.z p.pc p.dA (by norm_num) {2, 5} [2, 5]
    (by intro q; simp) hr0'
  have hT := (tailB_mono hhi p.pB p.Yt).trans (tailB_le hlk hpre hi p.pB p.Yt p.Kt t ht)
  have hNR : (N : ℝ) / 100 + 1 ≤ (hi : ℝ) / 100 + 1 := by
    have : (N : ℝ) ≤ hi := by exact_mod_cast hhi
    linarith
  unfold evalLin at hR hvlt
  push_cast at hR hvlt hc3 hc3' A3 A2
  rcases min_lt_iff.mp hvlt with h | h
  · left
    apply le_c7_of_lt _ hlo
    push_cast at ⊢
    linarith
  · right
    apply le_c7_of_lt _ hlo
    push_cast at ⊢
    linarith

/-- **One interval of the §10 certificate.** -/
theorem countBounds2_of_iv {pre : List ℕ} (hpre : admPreOK pre 0 0 = true) {S : Strs}
    {D : List DiscE} (hSD : DataOK S D) (iv : Iv2) (h : checkIv2 lk pre S iv = true) (N : ℕ)
    (hlo : iv.lo ≤ N) (hhi : N ≤ iv.hi) : CountBounds2 N := by
  unfold checkIv2 at h
  split at h
  · rename_i p0 p1 p2 p3 p4 d0 d1 d2 d3 d4 d5 _ _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h7, hlh⟩, hhi'⟩, q0⟩, q1⟩, q2⟩, q3⟩, q4⟩, B0⟩, B1⟩, B2⟩, B3⟩, B4⟩ := h
    exact ⟨caseIb_of hlk hSD B0 q0 hlo hhi hhi' h7,
      caseII_of hlk hpre hSD B1 q1 hlo hhi hhi' h7,
      caseIII1_of hlk hpre hSD B2 q2 hlo hhi hhi' h7,
      caseIII2beta_of hlk hpre hSD B3 q3 hlo hhi hhi' h7,
      caseIII2alpha_of hlk hpre hSD B4 q4 hlo hhi hhi' h7⟩
  · simp at h

end

end Erdos848
