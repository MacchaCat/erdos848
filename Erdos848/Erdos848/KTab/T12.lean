import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP48_ok : chainOK tabS48.1 tabS48.2 tabP48 = true := by decide +kernel

theorem tabP49_ok : chainOK tabS49.1 tabS49.2 tabP49 = true := by decide +kernel

theorem tabP50_ok : chainOK tabS50.1 tabS50.2 tabP50 = true := by decide +kernel

theorem tabP51_ok : chainOK tabS51.1 tabS51.2 tabP51 = true := by decide +kernel

end ErdosComp
