import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP68_ok : chainOK tabS68.1 tabS68.2 tabP68 = true := by decide +kernel

theorem tabP69_ok : chainOK tabS69.1 tabS69.2 tabP69 = true := by decide +kernel

theorem tabP70_ok : chainOK tabS70.1 tabS70.2 tabP70 = true := by decide +kernel

theorem tabP71_ok : chainOK tabS71.1 tabS71.2 tabP71 = true := by decide +kernel

end ErdosComp
