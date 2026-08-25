import SphincsSecurity.Proof.Arith
import SphincsSecurity.Proof.Bytes
import SphincsSecurity.Proof.Code
import SphincsSecurity.Proof.Guess
import SphincsSecurity.Proof.QueryBound
import SphincsSecurity.Proof.CacheSize
import SphincsSecurity.Proof.Amortized
import SphincsSecurity.Proof.Position
import SphincsSecurity.Proof.Game
import SphincsSecurity.Proof.Secrets
import SphincsSecurity.Proof.Logged
import SphincsSecurity.Proof.Support
import SphincsSecurity.Proof.Hybrid
import SphincsSecurity.Proof.LeakArith
import SphincsSecurity.Proof.Chain
import SphincsSecurity.Proof.Eval
import SphincsSecurity.Proof.StatementLemmas
import SphincsSecurity.Proof.OneTime
import SphincsSecurity.Proof.Merkle
import SphincsSecurity.Proof.FewTime
import SphincsSecurity.Proof.Layer
import SphincsSecurity.Proof.Hypertree
import SphincsSecurity.Proof.Correctness
import SphincsSecurity.Proof.Extract
import SphincsSecurity.Proof.ExtractChain
import SphincsSecurity.Proof.ExtractOts
import SphincsSecurity.Proof.ExtractFts
import SphincsSecurity.Proof.Honest
import SphincsSecurity.Proof.Settled
import SphincsSecurity.Proof.Slot
import SphincsSecurity.Proof.Charge
import SphincsSecurity.Proof.ChargeStep
import SphincsSecurity.Proof.HitBad
import SphincsSecurity.Proof.Queried
import SphincsSecurity.Proof.Cached
import SphincsSecurity.Proof.SettledPath
import SphincsSecurity.Proof.Descent
import SphincsSecurity.Proof.Execution
import SphincsSecurity.Proof.ReplayWorld
import SphincsSecurity.Proof.SigningReplay
import SphincsSecurity.Proof.SigningTrace
import SphincsSecurity.Proof.TracedGame
import SphincsSecurity.Proof.RootCache
import SphincsSecurity.Proof.NoMessage
import SphincsSecurity.Proof.SignerDigestSource
import SphincsSecurity.Proof.FullTrace
import SphincsSecurity.Proof.SignSupport
import SphincsSecurity.Proof.EncodingCached
import SphincsSecurity.Proof.LayerCompare
import SphincsSecurity.Proof.FewTimeCompare
import SphincsSecurity.Proof.ForgeryClassify
import SphincsSecurity.Proof.Replay
import SphincsSecurity.Proof.Sampling
import SphincsSecurity.Proof.OneTimeEvents
import SphincsSecurity.Proof.TerminalCache
import SphincsSecurity.Proof.FewTimeWitness
import SphincsSecurity.Proof.FewTimePatterns
import SphincsSecurity.Proof.FewTimeProbability
import SphincsSecurity.Proof.FewTimeTrace
import SphincsSecurity.Proof.FewTimeSource
import SphincsSecurity.Proof.MessagePrehit
import SphincsSecurity.Proof.FewTimeUniform
import SphincsSecurity.Proof.FewTimeLoop
import SphincsSecurity.Proof.FewTimeSignerView
import SphincsSecurity.Proof.FewTimeViewTrace
import SphincsSecurity.Proof.FewTimePadding
import SphincsSecurity.Proof.FewTimeFresh
import SphincsSecurity.Proof.FewTimePrehit
import SphincsSecurity.Proof.FewTimeSourceCount
import SphincsSecurity.Proof.FewTimePrehitArith
import SphincsSecurity.Proof.FewTimeRace
import SphincsSecurity.Proof.FewTimeOrigins

/-!
The proof of `SphincsSecurityStatement`, in progress. Only `SphincsSecurity/Statement.lean` has to
be trusted; everything here is checked by Lean.

What is proven so far is correctness: `Correctness.eval_verify` says `Ver` accepts a signature built
from the secrets, under an arbitrary answer function rather than under the lazy oracle. That is the
form the reduction needs, the random oracle's support being characterized by total answer functions,
and it is what rules out the statement holding vacuously for want of an accepting run.

`Bytes.tweakBytes_injective` is the other half of the foundation: a tweak names one structural
position, so one query bears on one position and an inversion stays at `2^-n` per query with no
multi-target factor. `Amortized.probEvent_bad_le_amortized` is what turns that into a bound on a
run: it is the only probabilistic argument the reduction makes, and `README.md` explains the shape
it imposes on everything else.
-/
