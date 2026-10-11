import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK36_ok : rowsK36.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK37_ok : rowsK37.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK38_ok : rowsK38.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK39_ok : rowsK39.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK40_ok : rowsK40.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK41_ok : rowsK41.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
