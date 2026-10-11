import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP24_ok : chainOK tabS24.1 tabS24.2 tabP24 = true := by decide +kernel

theorem tabP25_ok : chainOK tabS25.1 tabS25.2 tabP25 = true := by decide +kernel

theorem tabP26_ok : chainOK tabS26.1 tabS26.2 tabP26 = true := by decide +kernel

theorem tabP27_ok : chainOK tabS27.1 tabS27.2 tabP27 = true := by decide +kernel

end ErdosComp
