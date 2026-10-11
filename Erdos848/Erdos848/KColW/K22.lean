import Erdos848.ColW.Roots
import Erdos848.ColW.W22
import Erdos848.ColW.W21

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem win22_ok : winCheck winX21 winX22 rootsW ckT21 ckCnt21 ckLast21 winOps22 ckT22 ckCnt22 ckLast22 = true := by
  decide +kernel

end ErdosComp
