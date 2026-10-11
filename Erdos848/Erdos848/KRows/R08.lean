import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK48_ok : rowsK48.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK49_ok : rowsK49.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK50_ok : rowsK50.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK51_ok : rowsK51.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK52_ok : rowsK52.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK53_ok : rowsK53.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
