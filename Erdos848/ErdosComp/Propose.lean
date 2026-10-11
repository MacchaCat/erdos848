import ErdosComp.Comp

/-!
# The untrusted proposer (a port of `code/incr.cpp`)

Nothing here needs to be correct: every operation it proposes is re-checked by `runFrom`.
-/

namespace ErdosComp

structure Aux where
  has18 : Array Bool
  free18 : Array Nat
  posFree : Array Nat   -- position in `free18`, or `none18`
  rng : UInt64

def none18 : Nat := 1000000000000

def Aux.init : Aux := ⟨#[], #[], #[], 88172645463325252⟩

def Aux.next : Aux → UInt64 × Aux
  | ⟨h, f, p, x⟩ =>
    let x := x ^^^ (x <<< 13)
    let x := x ^^^ (x >>> 7)
    let x := x ^^^ (x <<< 17)
    (x, ⟨h, f, p, x⟩)

def Aux.markFree (a : Aux) (c : Nat) (fr : Bool) : Aux :=
  match a with
  | ⟨h, f, p, r⟩ =>
    let pos := p.getD c none18
    if fr && pos == none18 then
      let sz := f.size
      ⟨h, f.push c, p.set! c sz, r⟩
    else if !fr && pos != none18 then
      let last := f.back!
      let f := (f.set! pos last).pop
      let p := (p.set! last pos).set! c none18
      ⟨h, f, p, r⟩
    else ⟨h, f, p, r⟩

def Aux.setHas (a : Aux) (c : Nat) (b : Bool) : Aux :=
  match a with
  | ⟨h, f, p, r⟩ => ⟨h.set! c b, f, p, r⟩

def Aux.newClass (a : Aux) : Aux :=
  match a with
  | ⟨h, f, p, r⟩ => ⟨h.push false, f, p.push none18, r⟩

def smallSq : List Nat := [4, 9, 25, 49, 121, 169, 289, 361, 529, 841, 961, 1369, 1681, 1849, 2209,
  2809, 3481, 3721, 4489, 5041, 5329, 6241, 6889, 7921, 9409]

/-- Cheap sufficient test for non-squarefreeness. -/
def quickConf (n : Nat) : Bool := smallSq.any (fun q => n % q == 0)

/-- Number of members of `cls[c]` (other than `skip`) incompatible with `v`, capped at 2. -/
def conf (cls : Array (Array Nat)) (v c skip : Nat) : Nat × Nat := Id.run do
  let mut cnt := 0
  let mut who := 0
  let arr := cls[c]!
  -- cheap pass
  for u in arr do
    if u != skip && u != v && quickConf (u * v + 1) then
      who := u
      cnt := cnt + 1
      if cnt ≥ 2 then return (2, who)
  -- full pass on the others
  for u in arr do
    if u != skip && u != v && !quickConf (u * v + 1) && !sqfTest (u * v + 1) then
      who := u
      cnt := cnt + 1
      if cnt ≥ 2 then return (2, who)
  return (cnt, who)

def rngNext (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- The search (read-only on `aux`): operations for `v` and the class of `v`. -/
def search (aux : Aux) (cls : Array (Array Nat)) (v : Nat) (rng0 : UInt64) :
    Option (List Op × Nat) × UInt64 := Id.run do
  let mut rng := rng0
  let K := cls.size
  if K == 0 then return (none, rng)
  let is18 := v % 25 == 18
  -- phase 0: C18 arrivals try the C18-free classes
  if is18 then
    for c in aux.free18 do
      if (conf cls v c 0).1 == 0 then return (some ([.place v c], c), rng)
  -- phase 1: random classes
  let mut single : Array (Nat × Nat) := #[]
  for _ in [0:48] do
    rng := rngNext rng
    let c := (rng % K.toUInt64).toNat
    let (k, who) := conf cls v c 0
    if k == 0 then return (some ([.place v c], c), rng)
    if k == 1 then single := single.push (c, who)
  -- phase 2: move the unique conflicting member elsewhere
  for (c, u) in single do
    if u % 25 == 7 then continue
    if u % 25 == 18 then
      for c₂ in aux.free18 do
        if c₂ != c && (conf cls u c₂ 0).1 == 0 then
          return (some ([.move u c c₂, .place v c], c), rng)
    else
      for _ in [0:48] do
        rng := rngNext rng
        let c₂ := (rng % K.toUInt64).toNat
        if c₂ != c && (conf cls u c₂ 0).1 == 0 then
          return (some ([.move u c c₂, .place v c], c), rng)
  -- phase 3: two-step chains v → c (evict u), u → c₂ (evict w), w → c₃
  for (c, u) in single do
    if u % 25 == 7 then continue
    for _ in [0:32] do
      rng := rngNext rng
      let c₂ := (rng % K.toUInt64).toNat
      if c₂ == c then continue
      let (k, w) := conf cls u c₂ 0
      if k != 1 || w % 25 == 7 then continue
      if u % 25 == 18 && w % 25 != 18 && aux.has18.getD c₂ false then continue
      for _ in [0:48] do
        let mut c₃ := 0
        if w % 25 == 18 then
          if aux.free18.size == 0 then break
          rng := rngNext rng
          c₃ := aux.free18[(rng % aux.free18.size.toUInt64).toNat]!
        else
          rng := rngNext rng
          c₃ := (rng % K.toUInt64).toNat
        if c₃ == c || c₃ == c₂ then continue
        if (conf cls w c₃ 0).1 != 0 then continue
        return (some ([.move w c₂ c₃, .move u c c₂, .place v c], c), rng)
  -- phase 4: exhaustive one-step search
  let mut single2 : Array (Nat × Nat) := #[]
  for c in [0:K] do
    let (k, who) := conf cls v c 0
    if k == 0 then return (some ([.place v c], c), rng)
    if k == 1 then single2 := single2.push (c, who)
  for (c, u) in single2 do
    if u % 25 == 7 then continue
    for c₂ in [0:K] do
      if c₂ != c && (conf cls u c₂ 0).1 == 0 then
        return (some ([.move u c c₂, .place v c], c), rng)
  return (none, rng)

/-- C18 bookkeeping for one operation. -/
def Aux.update (a : Aux) : Op → Aux
  | .opn _ => a
  | .place v c => if v % 25 == 18 then (a.setHas c true).markFree c false else a
  | .move u c₁ c₂ =>
    if u % 25 == 18 then
      let a := (a.setHas c₁ false).markFree c₁ true
      (a.setHas c₂ true).markFree c₂ false
    else a

def propose (marks : Array Bool) (aux : Aux) (cls : Array (Array Nat)) (v : Nat) :
    List Op × Nat × Aux :=
  if !(marks.getD v true) then ([], 0, aux)
  else if v % 25 == 7 then
    let c := cls.size
    ([.opn v], c, (aux.newClass).markFree c true)
  else
    let (res, rng) := search aux cls v aux.rng
    match res with
    | none => ([], 0, aux)
    | some (ops, c) =>
      let aux := match aux with | ⟨h, f, p, _⟩ => (⟨h, f, p, rng⟩ : Aux)
      (ops, c, ops.foldl Aux.update aux)

/-- The whole computation up to `X`. -/
def compCheck (X : Nat) : Bool :=
  match buildMarks X certGen with
  | none => false
  | some marks => runFrom (propose marks) marks X 1 Aux.init #[]

end ErdosComp
