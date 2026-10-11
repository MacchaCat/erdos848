import Erdos848.CheckSound

/-!
# Phase 7 (part 4): the tail `N > 10⁶⁰`

A `ρ` bound valid for every `b`: `ρ(b)⁵ · (3·5⋯31) ≤ 1024 · 32¹⁰ · b`
(each odd prime `> 31` contributes a factor `≥ 32` to `b`).
-/

namespace Erdos848

open Finset ErdosComp

/-- The odd primes up to 31. -/
def P10 : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

lemma P10_prod : ∏ p ∈ P10, p = 100280245065 := by decide

lemma mem_P10 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h31 : p ≤ 31) : p ∈ P10 := by
  have : ∀ p ≤ 31, p.Prime → p ≠ 2 → p ∈ P10 := by decide
  exact this p h31 hp h2

lemma P10_card : P10.card = 10 := by decide

lemma P10_le (p : ℕ) (hp : p ∈ P10) : p ≤ 32 := by
  simp only [P10, mem_insert, mem_singleton] at hp; omega

theorem pow32_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    32 ^ S.card * 100280245065 ≤ 32 ^ 10 * ∏ p ∈ S, p := by
  classical
  set S1 := S.filter (· ≤ 31)
  set S2 := S.filter (fun p => ¬ p ≤ 31)
  have hcard : S.card = S1.card + S2.card := (card_filter_add_card_filter_not _).symm
  have hprod : ∏ p ∈ S, p = (∏ p ∈ S1, p) * ∏ p ∈ S2, p := (prod_filter_mul_prod_filter_not S (· ≤ 31) (fun p => p)).symm
  have hS1 : S1 ⊆ P10 := fun p hp => by
    have h := mem_filter.mp hp
    exact mem_P10 (hS p h.1).1 (hS p h.1).2 h.2
  have h2 : 32 ^ S2.card ≤ ∏ p ∈ S2, p := by
    rw [← prod_const]
    apply prod_le_prod ; intro p hp
    have h := mem_filter.mp hp
    omega
  have hsd : (∏ p ∈ S1, p) * ∏ p ∈ P10 \ S1, p = 100280245065 := by
    rw [mul_comm, prod_sdiff hS1, P10_prod]
  have hrest : ∏ p ∈ P10 \ S1, p ≤ 32 ^ (P10 \ S1).card := by
    rw [← prod_const]
    exact prod_le_prod (fun p hp => P10_le p (mem_sdiff.mp hp).1)
  have hcd : (P10 \ S1).card + S1.card = 10 := by
    rw [card_sdiff_add_card_eq_card hS1, P10_card]
  rw [hcard, hprod, ← hsd, pow_add]
  calc 32 ^ S1.card * 32 ^ S2.card * ((∏ p ∈ S1, p) * ∏ p ∈ P10 \ S1, p)
      ≤ 32 ^ S1.card * 32 ^ S2.card * ((∏ p ∈ S1, p) * 32 ^ (P10 \ S1).card) := by gcongr
    _ = 32 ^ ((P10 \ S1).card + S1.card) * ((∏ p ∈ S1, p) * 32 ^ S2.card) := by ring
    _ ≤ 32 ^ ((P10 \ S1).card + S1.card) * ((∏ p ∈ S1, p) * ∏ p ∈ S2, p) := by gcongr
    _ = 32 ^ 10 * ((∏ p ∈ S1, p) * ∏ p ∈ S2, p) := by rw [hcd]

/-- **`ρ` for every `b`.** -/
theorem rhoBound_pow5 {b : ℕ} (hb : 1 ≤ b) :
    rhoBound b ^ 5 * 100280245065 ≤ 1024 * 32 ^ 10 * b := by
  have hP := pow32_le_prod (oddPF b) (fun p hp => oddPF_prime hp)
  have hdiv : ∏ p ∈ oddPF b, p ≤ b := Nat.le_of_dvd (by omega) (prod_oddPF_dvd b)
  have htf : twoFactor b ≤ 4 := by unfold twoFactor; split_ifs <;> omega
  have hr : rhoBound b ≤ 4 * 2 ^ (oddPF b).card := by
    unfold rhoBound; rw [oddOmega_eq]; exact Nat.mul_le_mul_right _ htf
  have h5 : rhoBound b ^ 5 ≤ 1024 * 32 ^ (oddPF b).card := by
    calc rhoBound b ^ 5 ≤ (4 * 2 ^ (oddPF b).card) ^ 5 := Nat.pow_le_pow_left hr 5
      _ = 1024 * 32 ^ (oddPF b).card := by
          rw [mul_pow, ← pow_mul, mul_comm (oddPF b).card 5, pow_mul]; norm_num
  calc rhoBound b ^ 5 * 100280245065 ≤ 1024 * 32 ^ (oddPF b).card * 100280245065 :=
        Nat.mul_le_mul_right _ h5
    _ = 1024 * (32 ^ (oddPF b).card * 100280245065) := by ring
    _ ≤ 1024 * (32 ^ 10 * ∏ p ∈ oddPF b, p) := Nat.mul_le_mul_left _ hP
    _ ≤ 1024 * (32 ^ 10 * b) := by gcongr
    _ = 1024 * 32 ^ 10 * b := by ring

/-! ### The parameters `t = ⌊N^{1/4}⌋`, `Y = ⌊N/t⌋` -/

def tt (N : ℕ) : ℕ := Nat.sqrt (Nat.sqrt N)
def Yt (N : ℕ) : ℕ := N / tt N

lemma tt_pow4_le (N : ℕ) : tt N ^ 4 ≤ N := by
  have h1 := Nat.sqrt_le (Nat.sqrt N)
  have h2 := Nat.sqrt_le N
  unfold tt
  calc Nat.sqrt (Nat.sqrt N) ^ 4 =
        (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) * (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) := by ring
    _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul h1 h1
    _ ≤ N := h2

lemma lt_tt_pow4 (N : ℕ) : N < (tt N + 1) ^ 4 := by
  have h1 := Nat.lt_succ_sqrt (Nat.sqrt N)
  have h2 := Nat.lt_succ_sqrt N
  unfold tt
  set s := Nat.sqrt N
  set u := Nat.sqrt s
  have : s + 1 ≤ (u + 1) * (u + 1) := h1
  calc N < (s + 1) * (s + 1) := h2
    _ ≤ ((u + 1) * (u + 1)) * ((u + 1) * (u + 1)) := Nat.mul_le_mul this this
    _ = (u + 1) ^ 4 := by ring

lemma tt_ge {N : ℕ} (hN : 10 ^ 60 ≤ N) : 10 ^ 14 ≤ tt N := by
  by_contra h; push Not at h
  have h1 : (tt N + 1) ^ 4 ≤ (10 ^ 14) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have := lt_tt_pow4 N
  norm_num at h1; omega

lemma pow4_le_pow3 : ∀ k, 9 ≤ k → (k + 1) ^ 4 ≤ 3 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (k + 2) ^ 4 ≤ 3 * (k + 1) ^ 4 := by nlinarith [sq_nonneg (k * k), sq_nonneg k]
    calc (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring
      _ ≤ 3 * (k + 1) ^ 4 := this
      _ ≤ 3 * 3 ^ k := by omega
      _ = 3 ^ (k + 1) := by ring

lemma log3_lt_tt {N : ℕ} (hN : 10 ^ 60 ≤ N) : Nat.log 3 N + 1 ≤ tt N := by
  have ht := tt_ge hN
  set k := Nat.log 3 N
  by_cases hk : 9 ≤ k
  · have h1 := pow4_le_pow3 k hk
    have h2 : 3 ^ k ≤ N := Nat.pow_log_le_self 3 (by omega)
    have h3 := lt_tt_pow4 N
    have : (k + 1) ^ 4 < (tt N + 1) ^ 4 := by omega
    have := (Nat.pow_lt_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp this
    omega
  · omega

/-! ### Growth bounds -/

section
variable {N : ℕ} (hN : 10 ^ 60 ≤ N)
include hN

omit hN in
lemma Yt_mul_le : Yt N * tt N ≤ N := Nat.div_mul_le_self N (tt N)

lemma lt_Yt_mul : N < (Yt N + 1) * tt N := by
  have ht : 0 < tt N := by have := tt_ge hN; omega
  have := Nat.lt_div_mul_add (a := N) ht
  unfold Yt; nlinarith

lemma Yt_ge : tt N ^ 3 ≤ Yt N := by
  have ht : 0 < tt N := by have := tt_ge hN; omega
  unfold Yt
  rw [Nat.le_div_iff_mul_le ht]
  have := tt_pow4_le N
  calc tt N ^ 3 * tt N = tt N ^ 4 := by ring
    _ ≤ N := this

lemma Yt_big : PM < Yt N := by
  have h1 := Yt_ge hN
  have h2 : (10 ^ 14) ^ 3 ≤ tt N ^ 3 := Nat.pow_le_pow_left (tt_ge hN) 3
  unfold PM; norm_num at h2; omega

lemma Yt_pos : 1 ≤ Yt N := by have := Yt_big hN; unfold PM at this; omega

lemma growth_Y : (Yt N : ℝ) ≤ N / 10 ^ 14 := by
  have h1 := Yt_mul_le (N := N)
  have h2 := tt_ge hN
  have : Yt N * 10 ^ 14 ≤ N := le_trans (Nat.mul_le_mul_left _ h2) h1
  rw [le_div_iff₀ (by positivity)]; exact_mod_cast this

lemma growth_pell :
    (((N ^ 2 + 1) / (Yt N + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) ≤ N / 10 ^ 14 := by
  have ht := tt_ge hN
  have h1 := lt_Yt_mul hN
  have hdiv : (N ^ 2 + 1) / (Yt N + 1) ^ 2 ≤ tt N ^ 2 := by
    apply Nat.div_le_of_le_mul
    have : N + 1 ≤ (Yt N + 1) * tt N := h1
    nlinarith
  have hlog := log3_lt_tt hN
  have h4 := tt_pow4_le N
  have : (N ^ 2 + 1) / (Yt N + 1) ^ 2 * (Nat.log 3 N + 1) * 10 ^ 14 ≤ N := by
    calc (N ^ 2 + 1) / (Yt N + 1) ^ 2 * (Nat.log 3 N + 1) * 10 ^ 14
        ≤ tt N ^ 2 * tt N * tt N := by gcongr
      _ = tt N ^ 4 := by ring
      _ ≤ N := h4
  rw [le_div_iff₀ (by positivity)]; exact_mod_cast this

lemma rho_tt_le {b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) : 10 ^ 6 * rhoBound b * tt N ^ 2 ≤ N := by
  have h5 := rhoBound_pow5 hb
  have h4 := tt_pow4_le N
  set ρ := rhoBound b
  set t := tt N
  have hC : ρ ^ 5 * 100280245065 ≤ 1024 * 32 ^ 10 * N :=
    h5.trans (Nat.mul_le_mul_left _ hbN)
  have hN3 : 10 ^ 60 * (1024 * 32 ^ 10) ^ 2 ≤ N ^ 3 := by
    have : (10 ^ 60) ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
    norm_num at this ⊢; omega
  have key : (10 ^ 6 * ρ * t ^ 2) ^ 10 * 100280245065 ^ 2 ≤ N ^ 10 * 100280245065 ^ 2 := by
    calc (10 ^ 6 * ρ * t ^ 2) ^ 10 * 100280245065 ^ 2
        = 10 ^ 60 * (ρ ^ 5 * 100280245065) ^ 2 * (t ^ 4) ^ 5 := by ring
      _ ≤ 10 ^ 60 * (1024 * 32 ^ 10 * N) ^ 2 * N ^ 5 := by gcongr
      _ = (10 ^ 60 * (1024 * 32 ^ 10) ^ 2) * N ^ 7 := by ring
      _ ≤ N ^ 3 * N ^ 7 := Nat.mul_le_mul_right _ hN3
      _ ≤ N ^ 10 * 100280245065 ^ 2 := by
          rw [← pow_add]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have := Nat.le_of_mul_le_mul_right key (by positivity)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (10 : ℕ) ≠ 0)).mp this

lemma growth_rho {b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) :
    (rhoBound b : ℝ) * (2 * ((N : ℝ) + 1) / (Yt N) + ((N : ℝ) * b + 1) / ((Yt N : ℝ) ^ 2)) ≤
      N / 50000 := by
  have hρ := rho_tt_le hN hb hbN
  have h1 := lt_Yt_mul hN
  have hY1 := Yt_pos hN
  have htt := tt_ge hN
  have hNY' : N ≤ 2 * Yt N * tt N := by nlinarith
  have hNY : (N : ℝ) ≤ 2 * (Yt N : ℝ) * (tt N : ℝ) := by exact_mod_cast hNY'
  have hYR : (1 : ℝ) ≤ Yt N := by exact_mod_cast hY1
  have hNR : (10 : ℝ) ^ 60 ≤ N := by exact_mod_cast hN
  have hbR : (b : ℝ) ≤ N := by exact_mod_cast hbN
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hYpos : (0 : ℝ) < Yt N := by linarith
  have ht1 : (1 : ℝ) ≤ tt N := by exact_mod_cast (show 1 ≤ tt N by omega)
  have e1 : 2 * ((N : ℝ) + 1) / Yt N ≤ 8 * (tt N : ℝ) := by
    rw [div_le_iff₀ hYpos]; nlinarith
  have e2 : ((N : ℝ) * b + 1) / (Yt N : ℝ) ^ 2 ≤ 8 * (tt N : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (N : ℝ) * b + 1 ≤ 2 * (N : ℝ) * N := by nlinarith
    have hsq : (N : ℝ) * N ≤ (2 * (Yt N : ℝ) * tt N) * (2 * (Yt N : ℝ) * tt N) := by
      have : (0 : ℝ) ≤ N := by positivity
      exact mul_self_le_mul_self this hNY
    nlinarith
  have hρR : (10 : ℝ) ^ 6 * rhoBound b * (tt N : ℝ) ^ 2 ≤ N := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) ≤ rhoBound b := by positivity
  calc (rhoBound b : ℝ) * (2 * ((N : ℝ) + 1) / Yt N + ((N : ℝ) * b + 1) / (Yt N : ℝ) ^ 2)
      ≤ rhoBound b * (8 * (tt N : ℝ) + 8 * (tt N : ℝ) ^ 2) := by gcongr
    _ ≤ rhoBound b * (16 * (tt N : ℝ) ^ 2) := by gcongr; nlinarith
    _ ≤ N / 50000 := by rw [le_div_iff₀ (by norm_num)]; nlinarith

end

/-! ### Tail components -/

lemma s2P_big (tab : List (ℕ × PSt)) {lo Y : ℕ} (hlo : lo ≤ PM) (hY : PM < Y) :
    s2P tab lo Y = s2P tab lo PM1 := by
  unfold s2P PM1; simp [show ¬ Y ≤ PM by omega, hlo]

lemma s2U_big (tab : List (ℕ × PSt)) {lo Y : ℕ} (hlo : lo ≤ PM) (hY : PM < Y) :
    s2U tab lo Y = s2U tab lo PM1 := by
  unfold s2U PM1; simp [show ¬ Y ≤ PM by omega, hlo]

lemma card_Ioc_filter_le (lo Y : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (((Ioc lo Y).filter P).card : ℝ) ≤ Y := by
  have : ((Ioc lo Y).filter P).card ≤ Y :=
    (card_filter_le _ _).trans (by rw [Nat.card_Ioc]; omega)
  exact_mod_cast this

lemma smallP_U1000 : smallP 1000 IsU1 = (range 1001).filter (fun p => isU1B p = true) := by
  ext p; simp only [smallP, mem_filter, isU1B_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2⟩⟩

lemma gall_sound (N Nt : ℕ) (hN : Nt ≤ N) :
    ∑ p ∈ smallP 1000 IsU1, max (gC N 41 p) 0 ≤
      ((gAllC : ℚ) : ℝ) * N + ((gAllE Nt : ℚ) : ℝ) := by
  unfold gAllC gAllE
  rw [sumF_eq, sumF_eq, ← smallP_U1000]
  push_cast
  rw [sum_mul, ← sum_add_distrib]
  apply sum_le_sum; intro p _
  rw [gC_eq]
  have := gmax_le ((gA p : ℚ) : ℝ) ((gE p : ℚ) : ℝ) (gA_nonneg _)
    (show (Nt : ℝ) ≤ N by exact_mod_cast hN)
  push_cast at this
  linarith

section
variable {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
include htab

lemma shT_sound (N b Y : ℕ) (hY : PM < Y) :
    shB N b 2000 Y ≤ ((shT tab).1 : ℝ) * N + ((shT tab).2 : ℝ) + Y +
      rhoBound b * (2 * (N + 1) / Y + (N * b + 1) / (Y : ℝ) ^ 2) := by
  unfold shB shT
  have h1 := midsum_le _ _ (midP_sub_primesIn 2000 Y (fun p => 2000 < p)) (N : ℝ) (by positivity)
  have h2 := S2_primesIn_le htab 2000 Y
  rw [s2P_big tab (by unfold PM; norm_num) hY] at h2
  have h3 : ((primesIn 2000 Y).card : ℝ) ≤ Y := card_Ioc_filter_le 2000 Y Nat.Prime
  have hN : (0 : ℝ) ≤ N := by positivity
  have := mul_le_mul_of_nonneg_left h2 hN
  dsimp only; push_cast
  linarith

lemma lemBT_sound (N q T Y : ℕ) (hY : PM < Y) :
    lemBB N q T 41 2000 Y ≤ ((lemBT tab q T).1 : ℝ) * N + ((lemBT tab q T).2 : ℝ) + 2 * Y +
      (((N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  unfold lemBB lemBT
  have h1 := u1Sum_le htab 41 2000 IsU1 (fun _ h => h) ((N : ℝ) / q) (by positivity)
  have h2 := midsum_le _ _ (midP_sub_u1In 2000 Y (fun p => IsU1 p ∧ 2000 < p) (fun _ h => h.1))
    (N : ℝ) (by positivity)
  have h3 := S2_u1In_le htab 2000 Y
  rw [s2U_big tab (by unfold PM; norm_num) hY] at h3
  have h4 : ((u1In 2000 Y).card : ℝ) ≤ Y := card_Ioc_filter_le 2000 Y IsU1
  have hT : (0 : ℝ) ≤ T := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hT
  have h3' := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ N by positivity)
  rw [sum_two, sum_two]
  dsimp only; push_cast
  rw [prodU_cast, kU_eq]
  unfold PU
  push_cast
  linear_combination 2 * h1' + 2 * h2 + 2 * h3' + 2 * h4

lemma lemCT_sound (N Nt Y : ℕ) (hY : PM < Y) (hNt : Nt ≤ N) :
    lemCB N 41 1000 2000 Y 2000 (∑ p ∈ smallP 1000 IsU1, max (gC N 41 p) 0) ≤
      ((lemCT tab Nt).1 : ℝ) * N + ((lemCT tab Nt).2 : ℝ) + 2 * Y +
      (((N ^ 2 + 1) / (Y + 1) ^ 2 * (Nat.log 3 N + 1) : ℕ) : ℝ) := by
  unfold lemCB lemCT
  have e1 := u1Sum_le htab 41 2000 (fun p => IsU1 p ∧ 41 < p) (fun _ h => h.1) ((N : ℝ) / 25)
    (by positivity)
  have e2 := midsum_le _ _ (midP_sub_u1In 2000 Y (fun p => IsU1 p ∧ 2000 < p) (fun _ h => h.1))
    (N : ℝ) (by positivity)
  have e3 := S2_u1In_le htab 2000 Y
  rw [s2U_big tab (by unfold PM; norm_num) hY] at e3
  have e3' := mul_le_mul_of_nonneg_left e3 (show (0 : ℝ) ≤ N by positivity)
  have e4 : ((u1In 2000 Y).card : ℝ) ≤ Y := card_Ioc_filter_le 2000 Y IsU1
  have e5 := sumNon_eq N
  have e6 := gall_sound N Nt hNt
  have e7 := primeSum_le htab 1000 2000 (fun p => 1000 < p) (N : ℝ) (Nat.cast_nonneg N)
  rw [sum_two, sum_two]
  dsimp only; push_cast
  rw [prodU_cast, kU_eq]
  push_cast at e6
  linarith

end

/-! ### The tail -/

lemma lemmaD_tail {c : CE} {N X : ℕ} (hok : okT c = true) (hN : 10 ^ 60 ≤ N) (g : ℝ)
    (hg : g ≤ N / 10000) (hX : (X : ℝ) ≤ (c.1 : ℝ) * N + c.2 + g) : X ≤ c7 N := by
  unfold okT at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  have h1R : (c.1 : ℝ) ≤ 1 / 25 - 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2R : (c.2 : ℝ) ≤ 10 ^ 30 := by
    have := (Rat.cast_le (K := ℝ)).mpr h2; push_cast at this; exact this
  have hNR : (10 : ℝ) ^ 60 ≤ N := by exact_mod_cast hN
  have hc7 : ((N : ℝ) - 6) / 25 ≤ c7 N := by
    unfold c7
    have := Nat.div_add_mod (N + 18) 25
    have := Nat.mod_lt (N + 18) (show 0 < 25 by norm_num)
    have h : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast h
    linarith
  have : (X : ℝ) < c7 N := by nlinarith
  exact_mod_cast this.le

/-- **The analytic part for `N ≥ 10⁶⁰`**, given a valid table on which the tail check passes
(the check itself is `checkTailK` in `KAnalytic.lean`). -/
theorem countBounds_tail_of {tab : List (ℕ × PSt)} (htab : ∀ e ∈ tab, e.2 = stAt e.1)
    (hc : checkTailWith tab (10 ^ 60) = true) (N : ℕ) (hN : 10 ^ 60 ≤ N) : CountBounds N := by
  unfold checkTailWith at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨okIb, okII⟩, okIII1⟩, okIIIa⟩, okIIIb⟩ := hc
  set Y := Yt N
  have hYbig := Yt_big hN
  have hY1 := Yt_pos hN
  have gY := growth_Y hN
  have gP := growth_pell hN
  have gR : ∀ b, Witness N b → (rhoBound b : ℝ) * (2 * ((N : ℝ) + 1) / Y +
      ((N : ℝ) * b + 1) / (Y : ℝ) ^ 2) ≤ N / 50000 := fun b hw => growth_rho hN hw.1 hw.2.1
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hS5 := smallP_excl5
  have hS25 := smallP_excl25
  have sh := fun b => shT_sound htab N b Y hYbig
  constructor
  · intro b b' hw h7 hw' h18
    have := caseIb_real N b b' 31 2000 Y hY1 hw h7 hw' h18
    have r1 := res_sound htab N 25 1 2000 {5} [5] hS5
    have s1 := sh b; have s2 := sh b'
    have g1 := gR b hw; have g2 := gR b' hw'
    apply lemmaD_tail okIb hN (2 * Y + N / 50000 + N / 50000) (by linarith)
    simp only [caseIbT, addCE]; push_cast; linarith
  · intro b hw hs he
    have := caseII_real N b 31 2000 Y 41 1000 2000 Y _ hY1 hw hs he (by norm_num)
      (gBound_all N 41 1000)
    have r1 := res_sound htab N 25 2 2000 {2, 5} [2, 5] hS25
    have c1 := lemCT_sound htab N (10 ^ 60) Y hYbig hN
    have s1 := sh b
    have g1 := gR b hw
    apply lemmaD_tail okII hN (3 * Y + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIIT, addCE]; push_cast; linarith
  · intro b₁ b₃ hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
    have := caseIII1_real N b₁ b₃ 31 2000 Y 41 2000 Y hY1 hw₁ hs₁ hr₁ hw₃ hs₃ hr₃
    have r1 := res_sound htab N 100 6 2000 {2, 5} [2, 5] hS25
    have r2 := res_sound htab N 100 2 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound htab N 50 23 Y hYbig
    have s1 := sh b₁; have s2 := sh b₃
    have g1 := gR b₁ hw₁; have g2 := gR b₃ hw₃
    apply lemmaD_tail okIII1 hN (4 * Y + N / 50000 + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII1T, addCE]; push_cast; linarith
  · intro b rr hw hs hbr hrr
    have := caseIII2a_real N b rr 31 2000 Y 41 2000 Y hY1 hw hs hbr hrr
    have r1 := res_sound htab N 100 2 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound htab N 100 23 Y hYbig
    have s1 := sh b
    have g1 := gR b hw
    apply lemmaD_tail okIIIa hN (3 * Y + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII2aT, addCE]; push_cast; linarith
  · intro b b' rr hw hs hbr hrr hw' h7 he
    have := caseIII2b7_real N b b' rr 31 2000 Y 41 2000 Y hY1 hw hs hbr hrr hw' h7 he
    have r1 := res_sound htab N 100 3 2000 {2, 5} [2, 5] hS25
    have r2 := res_sound htab N 25 1 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound htab N 100 23 Y hYbig
    have s1 := sh b; have s2 := sh b'
    have g1 := gR b hw; have g2 := gR b' hw'
    apply lemmaD_tail okIIIb hN (4 * Y + N / 50000 + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII2bT, addCE]; push_cast; linarith
  · intro b b' rr hw hs hbr hrr hw' h18 he
    have := caseIII2b18_real N b b' rr 31 2000 Y 41 2000 Y hY1 hw hs hbr hrr hw' h18 he
    have r1 := res_sound htab N 100 3 2000 {2, 5} [2, 5] hS25
    have r2 := res_sound htab N 25 1 2000 {2, 5} [2, 5] hS25
    have l1 := lemBT_sound htab N 100 23 Y hYbig
    have s1 := sh b; have s2 := sh b'
    have g1 := gR b hw; have g2 := gR b' hw'
    apply lemmaD_tail okIIIb hN (4 * Y + N / 50000 + N / 50000 + N / 10 ^ 14) (by linarith)
    simp only [caseIII2bT, addCE]; push_cast; linarith

end Erdos848
