import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP28_ok : chainOK tabS28.1 tabS28.2 tabP28 = true := by decide +kernel

theorem tabP29_ok : chainOK tabS29.1 tabS29.2 tabP29 = true := by decide +kernel

theorem tabP30_ok : chainOK tabS30.1 tabS30.2 tabP30 = true := by decide +kernel

theorem tabP31_ok : chainOK tabS31.1 tabS31.2 tabP31 = true := by decide +kernel

end ErdosComp
