import ErdosComp.Table

/-!
# Rational upper bounds for prime sums and prime counts (executable)
-/

namespace ErdosComp

/-- Limit of the prime table. -/
def PM : Nat := 20000000

/-- `log 2 > 0.6931471803`. -/
def log2Lo : Rat := 6931471803 / 10000000000

/-- A rational lower bound for `log x`: `k log 2 + (1 - 2^k/x)` with `k = ⌊log₂ x⌋`. -/
def logLo (x : Nat) : Rat := (Nat.log2 x : Rat) * log2Lo + (1 - (2 ^ Nat.log2 x : Nat) / (x : Rat))

/-- `√x ≤ (x/s + s)/2`, `s = 2^⌊log₂ x / 2⌋`. -/
def sqrtUp (x : Nat) : Rat :=
  let s : Nat := 2 ^ (Nat.log2 x / 2)
  ((x : Rat) / s + s) / 2

/-- Chebyshev: `π(x) ≤ √x + 2 log 4 · x / log x` (and trivially `π(x) ≤ x`). -/
def chebUp (x : Nat) : Rat :=
  if 0 < logLo x then sqrtUp x + 2 * (13863 / 10000) * x / logLo x else x

/-- Upper bound for `∑_{p ∈ (lo, hi]} 1/p²` over primes. -/
def s2P (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).fp - (lookD tab lo).fp : Nat) : Rat) / KS
  else if lo ≤ PM then (((lookD tab PM).fp - (lookD tab lo).fp : Nat) : Rat) / KS + 1 / PM
  else 1 / lo

/-- Upper bound for `∑_{p ∈ (lo, hi]} 1/p²` over U1 primes. -/
def s2U (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).fu - (lookD tab lo).fu : Nat) : Rat) / KS
  else if lo ≤ PM then (((lookD tab PM).fu - (lookD tab lo).fu : Nat) : Rat) / KS + 1 / PM
  else 1 / lo

/-- Upper bound for the number of primes in `(lo, hi]`. -/
def cP (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).cp - (lookD tab lo).cp : Nat) : Rat) else chebUp hi

/-- Upper bound for the number of U1 primes in `(lo, hi]`. -/
def cU (tab : List (Nat × PSt)) (lo hi : Nat) : Rat :=
  if hi ≤ PM then (((lookD tab hi).cu - (lookD tab lo).cu : Nat) : Rat) else chebUp hi

end ErdosComp
