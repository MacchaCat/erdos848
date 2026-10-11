import ErdosComp.Check2

/-!
# Splitting the kernel checks

The kernel keeps every reduction of a declaration until the declaration is checked, so large
checks are split into many declarations and reassembled here:

* `checkIv2_of_cases`: `checkIv2 … iv = true` from the five case checks;
* `all_of_chunks`: `l.all P = true` from the chunks `(l.drop (j n)).take n`;
* `admPreOK_glue`: the prefix table of admissible `m` checked block by block.
-/

namespace ErdosComp

def dPrm : Prm2 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The cheap part of `checkIv2`. -/
def ivBasic (iv : Iv2) : Bool :=
  decide (7 ≤ iv.lo) && decide (iv.lo ≤ iv.hi) && decide (iv.hi ≤ 160000000) &&
    prmOK (iv.p.getD 0 dPrm) && prmOK (iv.p.getD 1 dPrm) && prmOK (iv.p.getD 2 dPrm) &&
    prmOK (iv.p.getD 3 dPrm) && prmOK (iv.p.getD 4 dPrm)

theorem checkIv2_of_cases (lk : Lk) (pre : List Nat) (S : Strs) (iv : Iv2)
    (hp : iv.p = [iv.p.getD 0 dPrm, iv.p.getD 1 dPrm, iv.p.getD 2 dPrm, iv.p.getD 3 dPrm,
      iv.p.getD 4 dPrm])
    (hd : iv.d = [iv.d.getD 0 [], iv.d.getD 1 [], iv.d.getD 2 [], iv.d.getD 3 [], iv.d.getD 4 [],
      iv.d.getD 5 []])
    (hb : ivBasic iv = true)
    (h0 : below iv.lo (caseIbQ lk S iv.hi (iv.p.getD 0 dPrm) (iv.d.getD 0 [])) = true)
    (h1 : below iv.lo (caseIIQ lk pre S iv.hi (iv.p.getD 1 dPrm) (iv.d.getD 1 [])) = true)
    (h2 : below iv.lo (caseIII1Q lk pre S iv.hi (iv.p.getD 2 dPrm) (iv.d.getD 2 [])) = true)
    (h3 : below iv.lo (caseIII2bQ lk pre S iv.hi (iv.p.getD 3 dPrm) (iv.d.getD 3 [])) = true)
    (h4 : below iv.lo (caseIII2aQ lk pre S iv.hi (iv.p.getD 4 dPrm) (iv.d.getD 4 [])
      (iv.d.getD 5 [])) = true) :
    checkIv2 lk pre S iv = true := by
  unfold checkIv2
  rw [hp, hd]
  unfold ivBasic at hb
  simp only [hb, h0, h1, h2, h3, h4, Bool.and_self]

theorem all_of_chunks {α : Type} (P : α → Bool) (n : Nat) :
    ∀ (k : Nat) (l : List α), l.length ≤ k * n →
      (∀ j, j < k → ((l.drop (j * n)).take n).all P = true) → l.all P = true
  | 0, l, hl, _ => by
    simp at hl
    simp [hl]
  | k + 1, l, hl, h => by
    have h0 : (l.take n).all P = true := by simpa using h 0 (by omega)
    have hr : (l.drop n).all P = true := by
      apply all_of_chunks P n k (l.drop n)
      · simp only [List.length_drop]; rw [Nat.succ_mul] at hl; omega
      · intro j hj
        have e : (l.drop n).drop (j * n) = l.drop ((j + 1) * n) := by
          rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]
        rw [e]; exact h (j + 1) (by omega)
    rw [← List.take_append_drop n l, List.all_append, h0, hr]; rfl

theorem admPreOK_glue (x : Nat) (rest : List Nat) : ∀ (t : List Nat) (i acc : Nat),
    admPreOK (t ++ [x]) i acc = true → admPreOK (x :: rest) (i + t.length) x = true →
    admPreOK (t ++ x :: rest) i acc = true
  | [], i, acc, h1, h2 => by
    simp only [List.nil_append, admPreOK, Bool.and_true, Nat.beq_eq] at h1
    subst h1
    simpa using h2
  | c :: cs, i, acc, h1, h2 => by
    simp only [List.cons_append, admPreOK, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, admPreOK_glue x rest cs (i + 1) _ h1.2 ?_⟩
    have e : i + 1 + cs.length = i + (c :: cs).length := by simp; omega
    rw [e]; exact h2

end ErdosComp
