import Erdos848.ColW.Roots
import Erdos848.ColW.W30
import Erdos848.ColW.W29

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win30_ok : winCheck winX29 winX30 rootsW ckT29 ckCnt29 ckLast29 winOps30 ckT30 ckCnt30 ckLast30 = true := by
  decide +kernel

end ErdosComp
