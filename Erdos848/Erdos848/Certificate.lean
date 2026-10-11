import Erdos848.Basic

/-!
# Colouring certificates

A certificate for `N` is a list of pairs `(vertex, colour)`.  `checkCert N cert` verifies:
1. every `n ∈ [1,N]` with `n² + 1` not squarefree has a colour `< c7 N`;
2. any two entries with different vertices and equal colours have `uv+1` squarefree.
`checkCert_sound` shows that a passing certificate proves `Statement N`.
The certificate itself may come from any (untrusted) algorithm.
-/

namespace Erdos848

/-- Association-list lookup (first match). -/
def lk : List (ℕ × ℕ) → ℕ → Option ℕ
  | [], _ => none
  | (a, c) :: t, n => if a = n then some c else lk t n

lemma lk_mem {l : List (ℕ × ℕ)} {n c : ℕ} (h : lk l n = some c) : (n, c) ∈ l := by
  induction l with
  | nil => simp [lk] at h
  | cons hd t ih =>
    obtain ⟨a, d⟩ := hd
    simp only [lk] at h
    split_ifs at h with hEq
    · subst hEq; simp only [Option.some.injEq] at h; subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- Condition 1 for a single `n`. -/
def coveredB (k : ℕ) (cert : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  decide (Squarefree (n * n + 1)) ||
    (match lk cert n with
     | some c => decide (c < k)
     | none => false)

/-- Condition 2 for a single pair of entries. -/
def pairOkB (p q : ℕ × ℕ) : Bool :=
  decide (p.1 = q.1) || decide (p.2 ≠ q.2) || decide (Squarefree (p.1 * q.1 + 1))

def checkCert (N : ℕ) (cert : List (ℕ × ℕ)) : Bool :=
  (List.range' 1 N).all (coveredB (c7 N) cert) &&
    cert.all (fun p => cert.all (fun q => pairOkB p q))

theorem checkCert_sound {N : ℕ} {cert : List (ℕ × ℕ)} (h : checkCert N cert = true) :
    Statement N := by
  intro A hAsub hA
  simp only [checkCert, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcov, hpair⟩ := h
  -- every element of A has a colour < c7 N
  have hcol : ∀ a ∈ A, ∃ c, lk cert a = some c ∧ c < c7 N := by
    intro a ha
    have haN := hAsub ha
    rw [Finset.mem_Icc] at haN
    have hin : a ∈ List.range' 1 N := by
      rw [List.mem_range'_1]; omega
    have hc := hcov a hin
    simp only [coveredB, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hsq | hsome
    · exact absurd hsq (hA a ha a ha)
    · revert hsome
      cases hl : lk cert a with
      | none => simp
      | some c => intro hc'; exact ⟨c, rfl, by simpa using hc'⟩
  let f : ℕ → ℕ := fun n => (lk cert n).getD 0
  apply card_le_of_coloring f hA
  · intro a ha
    obtain ⟨c, hc, hlt⟩ := hcol a ha
    simp [f, hc, hlt]
  · intro a ha b hb hne hfab
    obtain ⟨ca, hca, -⟩ := hcol a ha
    obtain ⟨cb, hcb, -⟩ := hcol b hb
    have hma := lk_mem hca
    have hmb := lk_mem hcb
    have hfa : f a = ca := by simp [f, hca]
    have hfb : f b = cb := by simp [f, hcb]
    have hp := hpair (a, ca) hma (b, cb) hmb
    simp only [pairOkB, Bool.or_eq_true, decide_eq_true_eq] at hp
    rcases hp with (h1 | h2) | h3
    · exact absurd h1 hne
    · exact absurd (hfa ▸ hfb ▸ hfab) h2
    · exact h3

end Erdos848
