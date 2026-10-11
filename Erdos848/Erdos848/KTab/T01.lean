import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP4_ok : chainOK tabS4.1 tabS4.2 tabP4 = true := by decide +kernel

theorem tabP5_ok : chainOK tabS5.1 tabS5.2 tabP5 = true := by decide +kernel

theorem tabP6_ok : chainOK tabS6.1 tabS6.2 tabP6 = true := by decide +kernel

theorem tabP7_ok : chainOK tabS7.1 tabS7.2 tabP7 = true := by decide +kernel

end ErdosComp
