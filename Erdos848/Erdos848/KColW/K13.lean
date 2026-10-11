import Erdos848.ColW.Roots
import Erdos848.ColW.W13
import Erdos848.ColW.W12

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win13_ok : winCheck winX12 winX13 rootsW ckT12 ckCnt12 ckLast12 winOps13 ckT13 ckCnt13 ckLast13 = true := by
  decide +kernel

end ErdosComp
