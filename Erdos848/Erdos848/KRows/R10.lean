import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK60_ok : rowsK60.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK61_ok : rowsK61.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK62_ok : rowsK62.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK63_ok : rowsK63.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK64_ok : rowsK64.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK65_ok : rowsK65.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
