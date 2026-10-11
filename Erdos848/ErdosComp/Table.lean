/-!
# Executable part of the prime table (core Lean only, precompiled)

Everything here is plain structural recursion so that it can be reasoned about in
`Erdos848/PrimeTable.lean`.  The primality test only needs to accept every prime
(`Erdos848.isPrimeB_of_prime`); accepting a composite would only weaken the bounds.
-/

namespace ErdosComp

/-- Trial division by `k, k+2, k+4, …` (with fuel); returns `n` if no divisor is found. -/
def minFacAux (n : Nat) : Nat → Nat → Nat
  | _, 0 => n
  | k, f + 1 => if n < k * k then n else if n % k == 0 then k else minFacAux n (k + 2) f

def isPrimeB (n : Nat) : Bool :=
  if n < 2 then false else if n % 2 == 0 then n == 2 else minFacAux n 3 n == n

def isU1B (n : Nat) : Bool := isPrimeB n && n % 4 == 1 && 13 ≤ n

/-- Scale for the reciprocal squares. -/
def KS : Nat := 10 ^ 30

/-- `⌈K/p²⌉`. -/
def ceilK (p : Nat) : Nat := (KS + p * p - 1) / (p * p)

structure PSt where
  cp : Nat
  cu : Nat
  fp : Nat
  fu : Nat

def stepSt (n : Nat) (s : PSt) : PSt :=
  if isPrimeB n then
    if isU1B n then ⟨s.cp + 1, s.cu + 1, s.fp + ceilK n, s.fu + ceilK n⟩
    else ⟨s.cp + 1, s.cu, s.fp + ceilK n, s.fu⟩
  else s

/-- The state after processing `1, …, n` (specification; slow). -/
def stAt : Nat → PSt
  | 0 => ⟨0, 0, 0, 0⟩
  | n + 1 => stepSt (n + 1) (stAt n)

/-- `k` more steps from position `n` (tail recursive). -/
def advance : Nat → Nat → PSt → PSt
  | 0, _, s => s
  | k + 1, n, s => advance k (n + 1) (stepSt (n + 1) s)

/-- One pass through the requested points (in increasing order). -/
def evalPts : List Nat → Nat → PSt → List (Nat × PSt)
  | [], _, _ => []
  | x :: xs, n, s =>
    (n + (x - n), advance (x - n) n s) :: evalPts xs (n + (x - n)) (advance (x - n) n s)

/-- Look a point up in the table (falling back to the specification). -/
def lookD (tab : List (Nat × PSt)) (x : Nat) : PSt :=
  match tab.find? (fun e => e.1 == x) with
  | some e => e.2
  | none => stAt x

end ErdosComp
