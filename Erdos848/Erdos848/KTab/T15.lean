import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP60_ok : chainOK tabS60.1 tabS60.2 tabP60 = true := by decide +kernel

theorem tabP61_ok : chainOK tabS61.1 tabS61.2 tabP61 = true := by decide +kernel

theorem tabP62_ok : chainOK tabS62.1 tabS62.2 tabP62 = true := by decide +kernel

theorem tabP63_ok : chainOK tabS63.1 tabS63.2 tabP63 = true := by decide +kernel

end ErdosComp
