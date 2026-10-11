import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP40_ok : chainOK tabS40.1 tabS40.2 tabP40 = true := by decide +kernel

theorem tabP41_ok : chainOK tabS41.1 tabS41.2 tabP41 = true := by decide +kernel

theorem tabP42_ok : chainOK tabS42.1 tabS42.2 tabP42 = true := by decide +kernel

theorem tabP43_ok : chainOK tabS43.1 tabS43.2 tabP43 = true := by decide +kernel

end ErdosComp
