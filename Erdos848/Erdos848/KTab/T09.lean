import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP36_ok : chainOK tabS36.1 tabS36.2 tabP36 = true := by decide +kernel

theorem tabP37_ok : chainOK tabS37.1 tabS37.2 tabP37 = true := by decide +kernel

theorem tabP38_ok : chainOK tabS38.1 tabS38.2 tabP38 = true := by decide +kernel

theorem tabP39_ok : chainOK tabS39.1 tabS39.2 tabP39 = true := by decide +kernel

end ErdosComp
