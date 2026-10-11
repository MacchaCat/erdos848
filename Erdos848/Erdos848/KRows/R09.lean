import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK54_ok : rowsK54.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK55_ok : rowsK55.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK56_ok : rowsK56.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK57_ok : rowsK57.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK58_ok : rowsK58.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK59_ok : rowsK59.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
