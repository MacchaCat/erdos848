import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK18_ok : rowsK18.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK19_ok : rowsK19.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK20_ok : rowsK20.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK21_ok : rowsK21.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK22_ok : rowsK22.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK23_ok : rowsK23.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
