import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK42_ok : rowsK42.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK43_ok : rowsK43.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK44_ok : rowsK44.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK45_ok : rowsK45.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK46_ok : rowsK46.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK47_ok : rowsK47.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
