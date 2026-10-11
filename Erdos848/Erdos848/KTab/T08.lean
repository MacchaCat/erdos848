import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP32_ok : chainOK tabS32.1 tabS32.2 tabP32 = true := by decide +kernel

theorem tabP33_ok : chainOK tabS33.1 tabS33.2 tabP33 = true := by decide +kernel

theorem tabP34_ok : chainOK tabS34.1 tabS34.2 tabP34 = true := by decide +kernel

theorem tabP35_ok : chainOK tabS35.1 tabS35.2 tabP35 = true := by decide +kernel

end ErdosComp
