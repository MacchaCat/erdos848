import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK6_ok : rowsK6.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK7_ok : rowsK7.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK8_ok : rowsK8.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK9_ok : rowsK9.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK10_ok : rowsK10.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK11_ok : rowsK11.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
