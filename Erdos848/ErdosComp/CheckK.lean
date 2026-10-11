import ErdosComp.Check
import ErdosComp.TabK
import ErdosComp.RowsK

/-!
# The analytic checker with a kernel-verified prime table

Each certificate row only consults the prime table at a dozen points; `rowTab` looks them up in
the search tree `treeK` (whose entries are verified segment by segment, `Erdos848/KTab`).
-/

namespace ErdosComp

/-- The points at which `checkRow` consults the table. -/
def rowPts (r : Row) : List Nat :=
  [31, 41, 1000, PM, r.pc, r.Y, r.Y25, r.Y50, r.Y100, r.pB25, r.pB50, r.pB100].filter
    (fun x => Nat.ble x PM)

def rowTab (t : PTree) (r : Row) : List (Nat × PSt) := (rowPts r).map (fun x => (x, lookDT t x))

def tailTab (t : PTree) : List (Nat × PSt) := [31, 41, 1000, 2000, PM].map (fun x => (x, lookDT t x))

end ErdosComp
