import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP64_ok : chainOK tabS64.1 tabS64.2 tabP64 = true := by decide +kernel

theorem tabP65_ok : chainOK tabS65.1 tabS65.2 tabP65 = true := by decide +kernel

theorem tabP66_ok : chainOK tabS66.1 tabS66.2 tabP66 = true := by decide +kernel

theorem tabP67_ok : chainOK tabS67.1 tabS67.2 tabP67 = true := by decide +kernel

end ErdosComp
