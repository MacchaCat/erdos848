import Erdos848.ColSound

/-!
# Gluing `rootsGo` runs

A single `rootsGo` run over all of `[5, 986746]` is very slow in the kernel, so
`Erdos848/KColW/Roots.lean` checks each chunk of roots on its own range and glues the runs.
-/

namespace Erdos848

open ErdosComp

/-- Gluing two `rootsGo` runs: the first on `[n, M]`, the second from `m`, the first value
`≡ n (mod 4)` above `M`. -/
lemma rootsGo_append (X M m g : ℕ) (rs2 : List (ℕ × ℕ)) (h2 : rootsGo X g m rs2 = true)
    (hm : M < m) (hm4 : m ≤ M + 4) (hMX : M ≤ X) :
    ∀ k n f (rs1 : List (ℕ × ℕ)), n + 4 * k = m → k < f → rootsGo M f n rs1 = true →
      rootsGo X (k + g) n (rs1 ++ rs2) = true
  | _, _, 0, _, _, hf, _ => (Nat.not_lt_zero _ hf).elim
  | 0, n, f + 1, rs1, hk, _, h1 => by
    have hn : n = m := by omega
    subst hn
    have hb : Nat.blt M n = true := Nat.blt_eq.mpr hm
    simp only [rootsGo, hb, cond_true, List.isEmpty_iff] at h1
    subst h1
    simpa using h2
  | k + 1, n, f + 1, rs1, hk, hf, h1 => by
    have hbM : Nat.blt M n = false := by
      rw [Bool.eq_false_iff]; intro h; have := Nat.blt_eq.mp h; omega
    have hbX : Nat.blt X n = false := by
      rw [Bool.eq_false_iff]; intro h; have := Nat.blt_eq.mp h; omega
    rw [show k + 1 + g = (k + g) + 1 by omega]
    simp only [rootsGo, hbM, hbX, cond_false] at h1 ⊢
    match rs1, h1 with
    | (p, r) :: rest, h1 =>
      simp only [List.cons_append]
      cases hp : Nat.beq p n
      · simp only [hp, cond_false, Bool.and_eq_true] at h1 ⊢
        exact ⟨h1.1, rootsGo_append X M m g rs2 h2 hm hm4 hMX k (n + 4) f _ (by omega) (by omega) h1.2⟩
      · simp only [hp, cond_true, Bool.and_eq_true] at h1 ⊢
        exact ⟨h1.1, rootsGo_append X M m g rs2 h2 hm hm4 hMX k (n + 4) f rest (by omega) (by omega)
          h1.2⟩
    | [], h1 =>
      simp only [Bool.and_eq_true] at h1
      have hrest := rootsGo_append X M m g rs2 h2 hm hm4 hMX k (n + 4) f [] (by omega) (by omega) h1.2
      simp only [List.nil_append] at hrest ⊢
      have hv := rootsGo_valid X g m rs2 h2
      match rs2, hrest, hv with
      | (p, r) :: rest, hrest, hv =>
        have hpm := (hv (p, r) (by simp)).1
        have hp : Nat.beq p n = false := by
          rw [Bool.eq_false_iff]; intro h; have := Nat.eq_of_beq_eq_true h; simp only at hpm; omega
        simp only [hp, cond_false, Bool.and_eq_true]
        exact ⟨h1.1, hrest⟩
      | [], hrest, _ =>
        simp only [Bool.and_eq_true]
        exact ⟨h1.1, hrest⟩

end Erdos848
