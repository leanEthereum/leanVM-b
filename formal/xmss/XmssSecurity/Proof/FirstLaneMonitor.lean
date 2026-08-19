import XmssSecurity.Statement

namespace XmssSecurity.FirstLaneMonitor

inductive ControllerAction (Control Index : Type) where
  | stop
  | skip (next : Control)
  | encodingQuery (epoch : Epoch) (next : HashOutput → Control)
  | encodingSignAttempt (epoch : Epoch) (next : HashOutput → Control)
  | probe (index : Index) (target : Digest) (next : Bool → Control)
  | reveal (index : Index) (next : Digest → Control)

end XmssSecurity.FirstLaneMonitor
