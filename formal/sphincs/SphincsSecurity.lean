import SphincsSecurity.Statement

namespace SphincsSecurity

/-!
The claim to be proven. Its statement lives entirely in the single module `SphincsSecurity.Statement`, whose parameters, algorithms and experiment are the specification of `doc/sphincs/main.tex`.

The `sorry` below is the whole point of this project: it is the goal, and the build says out loud that nothing proves it yet. `formal/xmss` proves the analogous claim for the stateful scheme, and the two share the tweakable hash, the target-sum code and the shape of the bound, so the one-time and Merkle halves of that proof carry over; what is new here is the hypertree, the few-time forest, the digest that picks the index, and the counter search under a tweak shared across attempts.
-/

/-- `120` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signatures per key pair. -/
theorem sphincs_has_120_bits_of_classical_security : SphincsSecurityStatement := by
  sorry

end SphincsSecurity
