import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP72_ok : chainOK tabS72.1 tabS72.2 tabP72 = true := by decide +kernel

theorem tabP73_ok : chainOK tabS73.1 tabS73.2 tabP73 = true := by decide +kernel

theorem tabP74_ok : chainOK tabS74.1 tabS74.2 tabP74 = true := by decide +kernel

theorem tabP75_ok : chainOK tabS75.1 tabS75.2 tabP75 = true := by decide +kernel

end ErdosComp
