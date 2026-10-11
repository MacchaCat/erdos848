import Erdos848.ColW.Roots
import Erdos848.ColW.W28
import Erdos848.ColW.W27

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win28_ok : winCheck winX27 winX28 rootsW ckT27 ckCnt27 ckLast27 winOps28 ckT28 ckCnt28 ckLast28 = true := by
  decide +kernel

end ErdosComp
