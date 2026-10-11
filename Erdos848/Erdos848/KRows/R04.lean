import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK24_ok : rowsK24.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK25_ok : rowsK25.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK26_ok : rowsK26.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK27_ok : rowsK27.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK28_ok : rowsK28.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK29_ok : rowsK29.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
