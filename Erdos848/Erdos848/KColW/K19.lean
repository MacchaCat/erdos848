import Erdos848.ColW.Roots
import Erdos848.ColW.W19
import Erdos848.ColW.W18

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win19_ok : winCheck winX18 winX19 rootsW ckT18 ckCnt18 ckLast18 winOps19 ckT19 ckCnt19 ckLast19 = true := by
  decide +kernel

end ErdosComp
