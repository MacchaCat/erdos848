import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP76_ok : chainOK tabS76.1 tabS76.2 tabP76 = true := by decide +kernel

theorem tabP77_ok : chainOK tabS77.1 tabS77.2 tabP77 = true := by decide +kernel

theorem tabP78_ok : chainOK tabS78.1 tabS78.2 tabP78 = true := by decide +kernel

end ErdosComp
