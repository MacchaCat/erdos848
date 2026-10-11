import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK72_ok : rowsK72.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
