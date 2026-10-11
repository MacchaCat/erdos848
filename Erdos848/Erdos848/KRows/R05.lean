import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK30_ok : rowsK30.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK31_ok : rowsK31.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK32_ok : rowsK32.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK33_ok : rowsK33.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK34_ok : rowsK34.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK35_ok : rowsK35.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
