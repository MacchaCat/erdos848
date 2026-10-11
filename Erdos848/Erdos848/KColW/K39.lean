import Erdos848.ColW.Roots
import Erdos848.ColW.W39
import Erdos848.ColW.W38

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win39_ok : winCheck winX38 winX39 rootsW ckT38 ckCnt38 ckLast38 winOps39 ckT39 ckCnt39 ckLast39 = true := by
  decide +kernel

end ErdosComp
