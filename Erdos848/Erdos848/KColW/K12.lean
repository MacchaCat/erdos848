import Erdos848.ColW.Roots
import Erdos848.ColW.W12
import Erdos848.ColW.W11

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win12_ok : winCheck winX11 winX12 rootsW ckT11 ckCnt11 ckLast11 winOps12 ckT12 ckCnt12 ckLast12 = true := by
  decide +kernel

end ErdosComp
