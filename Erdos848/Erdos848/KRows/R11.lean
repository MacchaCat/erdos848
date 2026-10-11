import ErdosComp.CheckK

namespace ErdosComp

set_option maxRecDepth 100000

theorem rowsK66_ok : rowsK66.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK67_ok : rowsK67.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK68_ok : rowsK68.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK69_ok : rowsK69.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK70_ok : rowsK70.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

theorem rowsK71_ok : rowsK71.all (fun r => checkRow (rowTab treeK r) r) = true := by
  decide +kernel

end ErdosComp
