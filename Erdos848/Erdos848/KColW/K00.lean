import Erdos848.ColW.Roots
import Erdos848.ColW.W00

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win0_ok : winCheck 0 winX0 rootsW (mkBT 16) 0 0 winOps0 ckT0 ckCnt0 ckLast0 = true := by
  decide +kernel

end ErdosComp
