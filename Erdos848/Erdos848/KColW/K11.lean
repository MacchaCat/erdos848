import Erdos848.ColW.Roots
import Erdos848.ColW.W11
import Erdos848.ColW.W10

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win11_ok : winCheck winX10 winX11 rootsW ckT10 ckCnt10 ckLast10 winOps11 ckT11 ckCnt11 ckLast11 = true := by
  decide +kernel

end ErdosComp
