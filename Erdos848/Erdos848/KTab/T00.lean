import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP0_ok : chainOK tabS0.1 tabS0.2 tabP0 = true := by decide +kernel

theorem tabP1_ok : chainOK tabS1.1 tabS1.2 tabP1 = true := by decide +kernel

theorem tabP2_ok : chainOK tabS2.1 tabS2.2 tabP2 = true := by decide +kernel

theorem tabP3_ok : chainOK tabS3.1 tabS3.2 tabP3 = true := by decide +kernel

end ErdosComp
