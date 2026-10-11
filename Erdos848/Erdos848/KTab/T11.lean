import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP44_ok : chainOK tabS44.1 tabS44.2 tabP44 = true := by decide +kernel

theorem tabP45_ok : chainOK tabS45.1 tabS45.2 tabP45 = true := by decide +kernel

theorem tabP46_ok : chainOK tabS46.1 tabS46.2 tabP46 = true := by decide +kernel

theorem tabP47_ok : chainOK tabS47.1 tabS47.2 tabP47 = true := by decide +kernel

end ErdosComp
