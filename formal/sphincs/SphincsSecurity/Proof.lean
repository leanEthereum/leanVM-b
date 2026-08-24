import SphincsSecurity.Proof.Arith
import SphincsSecurity.Proof.Chain
import SphincsSecurity.Proof.Eval
import SphincsSecurity.Proof.StatementLemmas
import SphincsSecurity.Proof.OneTime
import SphincsSecurity.Proof.Merkle
import SphincsSecurity.Proof.FewTime
import SphincsSecurity.Proof.Layer
import SphincsSecurity.Proof.Hypertree

/-!
The proof of `SphincsSecurityStatement`, in progress. Only `SphincsSecurity/Statement.lean` has to
be trusted; everything here is checked by Lean.

What is proven so far is the structure of the three primitives, each as an equality between what the
signer produces and what the verifier recomputes, under an arbitrary answer function. That is the
form the reduction needs, the random oracle's support being characterized by total answer functions.
-/
