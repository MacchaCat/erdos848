import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP16_ok : chainOK tabS16.1 tabS16.2 tabP16 = true := by decide +kernel

theorem tabP17_ok : chainOK tabS17.1 tabS17.2 tabP17 = true := by decide +kernel

theorem tabP18_ok : chainOK tabS18.1 tabS18.2 tabP18 = true := by decide +kernel

theorem tabP19_ok : chainOK tabS19.1 tabS19.2 tabP19 = true := by decide +kernel

end ErdosComp
