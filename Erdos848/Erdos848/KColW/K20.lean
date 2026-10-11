import Erdos848.ColW.Roots
import Erdos848.ColW.W20
import Erdos848.ColW.W19

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win20_ok : winCheck winX19 winX20 rootsW ckT19 ckCnt19 ckLast19 winOps20 ckT20 ckCnt20 ckLast20 = true := by
  decide +kernel

end ErdosComp
