import Erdos848.ColW.Roots
import Erdos848.ColW.W29
import Erdos848.ColW.W28

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win29_ok : winCheck winX28 winX29 rootsW ckT28 ckCnt28 ckLast28 winOps29 ckT29 ckCnt29 ckLast29 = true := by
  decide +kernel

end ErdosComp
