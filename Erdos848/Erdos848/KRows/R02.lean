import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK12_ok : rowsK12.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK13_ok : rowsK13.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK14_ok : rowsK14.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK15_ok : rowsK15.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK16_ok : rowsK16.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK17_ok : rowsK17.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
