import ErdosComp.TabK

namespace ErdosComp

set_option maxRecDepth 100000

theorem tabP56_ok : chainOK tabS56.1 tabS56.2 tabP56 = true := by decide +kernel

theorem tabP57_ok : chainOK tabS57.1 tabS57.2 tabP57 = true := by decide +kernel

theorem tabP58_ok : chainOK tabS58.1 tabS58.2 tabP58 = true := by decide +kernel

theorem tabP59_ok : chainOK tabS59.1 tabS59.2 tabP59 = true := by decide +kernel

end ErdosComp
