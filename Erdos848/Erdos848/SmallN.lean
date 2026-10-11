import Erdos848.Certificate

/-!
# Small `N`: certificates generated inside Lean and checked by `checkCert`

`colourStep` is an *untrusted* incremental colouring heuristic (first fit, then a one-step repair).
Its output is only used through `checkCert`, whose soundness is proved in `Certificate.lean`.

-/

namespace Erdos848

/-- Is `v` free of conflicts with every member of `cl`? -/
def freeIn (v : ℕ) (cl : List ℕ) : Bool := cl.all fun u => decide (Squarefree (u * v + 1))

/-- The members of `cl` in conflict with `v`. -/
def conflicts (v : ℕ) (cl : List ℕ) : List ℕ := cl.filter fun u => !decide (Squarefree (u * v + 1))

/-- Insert vertex `v` into the colouring `cls` (array of colour classes). -/
def colourStep (cls : Array (List ℕ)) (v : ℕ) : Array (List ℕ) :=
  if v % 25 = 7 then cls.push [v] else
  match (List.range cls.size).find? (fun c => freeIn v cls[c]!) with
  | some c => cls.set! c (v :: cls[c]!)
  | none =>
    -- one-step repair: a class `c` whose only conflict is `u`; move `u` to a free class `c2`
    let cand := (List.range cls.size).filterMap fun c =>
      match conflicts v cls[c]! with
      | [u] => if u % 25 = 7 then none else
          match (List.range cls.size).find? (fun c2 => c2 != c && freeIn u cls[c2]!) with
          | some c2 => some (c, u, c2)
          | none => none
      | _ => none
    match cand.head? with
    | some (c, u, c2) =>
        let cls := cls.set! c (v :: (cls[c]!.erase u))
        cls.set! c2 (u :: cls[c2]!)
    | none => cls   -- give up; the certificate check will then fail

def toCert (cls : Array (List ℕ)) : List (ℕ × ℕ) :=
  (List.range cls.size).flatMap fun c => cls[c]!.map fun u => (u, c)

/-- Run the colouring for `n = 1..M`, recording a certificate after each `n`. -/
def allCerts (M : ℕ) : List (ℕ × List (ℕ × ℕ)) :=
  ((List.range' 1 M).foldl (fun (acc : Array (List ℕ) × List (ℕ × List (ℕ × ℕ))) n =>
      let cls := if decide (Squarefree (n * n + 1)) then acc.1 else colourStep acc.1 n
      (cls, (n, toCert cls) :: acc.2)) (#[], [])).2.reverse

def smallCheck (M : ℕ) : Bool :=
  let L := allCerts M
  (L.map Prod.fst == List.range' 1 M) && L.all (fun p => checkCert p.1 p.2)

theorem statement_zero : Statement 0 := by
  intro A hA _
  have : A = ∅ := by
    ext x; constructor
    · intro hx; have := hA hx; simp at this
    · simp
  simp [this]

theorem smallCheck_sound {M : ℕ} (h : smallCheck M = true) : ∀ N ≤ M, Statement N := by
  intro N hN
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · exact statement_zero
  simp only [smallCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hfst, hall⟩ := h
  have hmem : N ∈ (allCerts M).map Prod.fst := by
    rw [hfst, List.mem_range'_1]; omega
  obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hmem
  have := hall p hp
  rw [hpN] at this
  exact checkCert_sound this

end Erdos848
