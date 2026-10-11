import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP52_ok : chainOK tabS52.1 tabS52.2 tabP52 = true := by decide +kernel

theorem tabP53_ok : chainOK tabS53.1 tabS53.2 tabP53 = true := by decide +kernel

theorem tabP54_ok : chainOK tabS54.1 tabS54.2 tabP54 = true := by decide +kernel

theorem tabP55_ok : chainOK tabS55.1 tabS55.2 tabP55 = true := by decide +kernel

end ErdosComp
