import SphincsSecurity.Proof.Arith
import SphincsSecurity.Proof.Bytes
import SphincsSecurity.Proof.Guess
import SphincsSecurity.Proof.QueryBound
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

/-!
The proof of `SphincsSecurityStatement`, in progress. Only `SphincsSecurity/Statement.lean` has to
be trusted; everything here is checked by Lean.

What is proven so far is correctness: `Correctness.eval_verify` says `Ver` accepts a signature built
from the secrets, under an arbitrary answer function rather than under the lazy oracle. That is the
form the reduction needs, the random oracle's support being characterized by total answer functions,
and it is what rules out the statement holding vacuously for want of an accepting run.

`Bytes.tweakBytes_injective` is the other half of the foundation: a tweak names one structural
position, so one query bears on one position and an inversion stays at `2^-n` per query with no
multi-target factor.
-/
