import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP20_ok : chainOK tabS20.1 tabS20.2 tabP20 = true := by decide +kernel

theorem tabP21_ok : chainOK tabS21.1 tabS21.2 tabP21 = true := by decide +kernel

theorem tabP22_ok : chainOK tabS22.1 tabS22.2 tabP22 = true := by decide +kernel

theorem tabP23_ok : chainOK tabS23.1 tabS23.2 tabP23 = true := by decide +kernel

end ErdosComp
