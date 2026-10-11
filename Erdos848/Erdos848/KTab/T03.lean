import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP12_ok : chainOK tabS12.1 tabS12.2 tabP12 = true := by decide +kernel

theorem tabP13_ok : chainOK tabS13.1 tabS13.2 tabP13 = true := by decide +kernel

theorem tabP14_ok : chainOK tabS14.1 tabS14.2 tabP14 = true := by decide +kernel

theorem tabP15_ok : chainOK tabS15.1 tabS15.2 tabP15 = true := by decide +kernel

end ErdosComp
