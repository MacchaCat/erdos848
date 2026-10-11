import Erdos848.ColW.Roots
import Erdos848.ColW.W31
import Erdos848.ColW.W30

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win31_ok : winCheck winX30 winX31 rootsW ckT30 ckCnt30 ckLast30 winOps31 ckT31 ckCnt31 ckLast31 = true := by
  decide +kernel

end ErdosComp
