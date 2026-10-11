import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP8_ok : chainOK tabS8.1 tabS8.2 tabP8 = true := by decide +kernel

theorem tabP9_ok : chainOK tabS9.1 tabS9.2 tabP9 = true := by decide +kernel

theorem tabP10_ok : chainOK tabS10.1 tabS10.2 tabP10 = true := by decide +kernel

theorem tabP11_ok : chainOK tabS11.1 tabS11.2 tabP11 = true := by decide +kernel

end ErdosComp
