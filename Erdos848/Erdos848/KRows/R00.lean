import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK0_ok : rowsK0.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK1_ok : rowsK1.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK2_ok : rowsK2.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK3_ok : rowsK3.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK4_ok : rowsK4.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK5_ok : rowsK5.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
