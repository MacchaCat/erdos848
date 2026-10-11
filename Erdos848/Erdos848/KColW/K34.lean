import Erdos848.ColW.Roots
import Erdos848.ColW.W34
import Erdos848.ColW.W33

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win34_ok : winCheck winX33 winX34 rootsW ckT33 ckCnt33 ckLast33 winOps34 ckT34 ckCnt34 ckLast34 = true := by
  decide +kernel

end ErdosComp
