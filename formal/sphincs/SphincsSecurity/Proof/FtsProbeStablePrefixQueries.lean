import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liftHashSource (computation : OracleComp HashSpec α) : OracleComp (OracleWorld + SigningSpec) α :=
  simulateQ (fun input => (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input))) :
    OracleComp (OracleWorld + SigningSpec) HashOutput)) computation

theorem liftHashSource_query_bind (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    liftHashSource ((liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput) >>= next) =
      ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input))) :
        OracleComp (OracleWorld + SigningSpec) HashOutput) >>= fun output => liftHashSource (next output)) := by
  rw [liftHashSource, simulateQ_bind, simulateQ_spec_query]
  rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
