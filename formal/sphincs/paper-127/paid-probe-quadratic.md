# A quadratic primitive bound that pays for message queries

This paper result strengthens two-probe-quadratic.md by including a reward for message queries made before failure. It also describes the proposed exact exposure of the concrete signature game needed to apply it. The charged FTS coverage estimate remains a separate obligation.

## Abstract bound

There are independent hidden labels, uniform on an N-element set. At most q<=N/2 rounds are available. A probe round can test one candidate against each of at most two distinct still-hidden labels. A matching probe is failure and stops the process. A paid round performs no probe and earns reward 3/(2N). Other rounds may be ignored or treated as probe rounds. Coordinate disclosures chosen using already visible information and independent randomness are permitted; disclosed coordinates are not subsequently probed. No additional leakage about hidden labels is permitted.

Let B be failure, and A the number of paid rounds before failure or earlier termination. Then

    P[B] + (3/(2N)) E[A] <= 2x-x^2/8,       x=q/N.

This is an expected accumulated-reward bound in a single stopped execution. It is not obtained by adding two independent success estimates.

## A scalar upper game

After t rounds, each undisclosed label has at most t distinct failed guesses. Conditioned on survival, it remains uniform on its unexcluded values. For two distinct labels, the conditional failure probability of the next probe round is at most

    h_t = 1-((N-t-1)/(N-t))^2.

The same upper bound covers fewer probes and repeats. Two sequential probes may choose the second coordinate using the first miss. Distinctness ensures its count before the round was still at most t.

Consider the scalar decision problem whose state is t alone: either take reward 3/(2N), or fail with probability h_t and otherwise continue. Its continuation value obeys

    V_q=0,
    V_t=max{3/(2N)+V_(t+1), h_t+(1-h_t)V_(t+1)}.

This upper game permits the largest hazard even after paid rounds. Its optimal action sequence consists of a prefix of paid rounds followed by probe rounds. Indeed V_t>=V_(t+1), h_t increases with t, and h_t(1-V_(t+1)) increases with t whenever V_(t+1)<=1. If a continuation value exceeds one, the paid action is preferred and all earlier actions can likewise be paid. These observations prove the prefix property without presuming the value is below one.

The probe survival factors telescope. Hence

    V_0 = max_(0<=a<=q) [3a/(2N)+1-((N-q)/(N-a))^2].

The bound below proves V_0<1 for q<=N/2 (apart from the trivial zero-round case). The same holds for later continuation values, which are no greater than V_0. Thus replacing actual probe hazards by h_t is valid: the payoff upon failure, one, is at least the continuation value.

## Elementary inequality

For 0<=s<=x<=1/2,

    (3/2)s+1-((1-x)/(1-s))^2 <= 2x-x^2/8.

The case x=0 is immediate. Otherwise put r=s/x in [0,1]. Subtract the left side from the right side and multiply by (1-s)^2/x^2. The resulting expression is

    F(x,r)=1-4r+2r^2+x(2r^2-(3/2)r^3)+r/(2x)
              -(1/8)(1-rx)^2.

For r>0 and x<=1/2 its derivative in x is negative, since

    dF/dx <= r[-2+2r-(3/2)r^2+1/4] <= -(13/12)r.

For r=0, F=7/8. Therefore it suffices to evaluate x=1/2:

    32 F(1/2,r)=28-92r+95r^2-24r^3.

The derivative of this polynomial is -2(36r-23)(r-2), so its minimum on [0,1] occurs at r=23/36. The minimum is 6767/3888>0. This proves the inequality and the abstract bound. The finite dynamic program was also checked with exact rational arithmetic for N=4,6,10,20,50 and all q<=N/2.

## Exposing the canonical graph in the signature experiment

Use the exact reference-counter and codeword construction in reference-frontier-transfer.md. After sampling J,D, generate the canonical structural graph by independently sampling every honest n-bit node label and programming the corresponding domain's function at its unique honest input. Leaves are the independently sampled secrets. The graph is acyclic, and every honest hash has a distinct tweak, so this produces exactly the original random-function law: conditional on earlier nodes, the next programmed input is fixed and its answer is uniformly sampled. Off that input, all rows remain independent uniform answers. The extra high 128 output bits are independent as well.

For analysis, reveal all canonical OTS frontier values at digits D, every OTS chain value above those frontiers, every OTS leaf and Merkle node, every FTS leaf hash and internal node, all reference counters and words, and the actual public key. Keep every OTS prefix label below its frontier and every FTS secret hidden. Conditional on the disclosed labels, these hidden labels remain independent uniforms. Canonical messages M_p are among the disclosed values. The encoding table is generated using these messages,J,D and independent randomness as in reference-frontier-transfer.md.

Only the canonical labels are disclosed here, not the full structural function tables. The original adversary ignores the additional advice. The real game, including all hash answers, signing responses, and costs, keeps its original marginal law.

Maintain a separate table of externally observed noncanonical oracle rows. Honest secret-dependent evaluations read the preprogrammed graph and are simulated internally. Their query inputs and intermediate values are not exposed. Their hash calls still count toward the original syntactic budget. Their outputs to the adversary consist of already exposed canonical OTS data, already exposed authentication nodes, and the selected FTS secrets on successful signing. The index and leaf selections depend on the visible transcript, message-oracle answers, and independent signing randomness. Whether the finite encoding searches succeed is determined by the exposed J values. Thus disclosure of selected FTS secrets is a permitted coordinate disclosure; it is not chosen by inspecting their hidden values.

Before primitive failure, externally requested hashes can be simulated as follows.

- An OTS prefix call first tests its input against its hidden honest child label. On a miss it is a noncanonical row; a fresh uniform low answer is tested against the honest parent label. The child and parent are different positions. If the parent is already public, the second test instead compares the fresh uniform answer coordinate with that public value.
- An FTS leaf call for an undisclosed secret similarly tests the candidate secret and then a fresh answer against its public leaf hash. After disclosure, the canonical input is public and ordinary reads there cause no failure; a fresh noncanonical answer still has one output-match test.
- Other structural inputs have public canonical children and outputs. Canonical reads cause no failure; a fresh noncanonical row has one output-match test against its public honest value.
- A nonreference encoding call at an unrestricted cell has one test of a fresh uniform low answer against the public reference codeword. Invalid prefix cells cannot match a valid reference; canonical reference reads cause no failure.
- A message-domain call has no primitive probe and is a paid round. Other unrelated inputs and internal honest calls need no primitive probe.

Cache repeats cannot create a first match: an earlier noncanonical answer was already tested, and a prior missed input remains different from its honest child. Independent high output bits reveal no additional information. Prefix child and parent probes always address distinct hidden coordinates; fresh answer coordinates are new labels. All information produced between rounds is either already public data, independent randomness, prior replies, or an allowed FTS-secret disclosure.

Define B as the first match in this simulation, including an internal guess that might not yet be useful for a forgery. The original adversary is not given a correct-guess flag. Stopping at B is only an upper-bound device. With A counting message-domain hash calls before B, the abstract reward bound applies to the original execution under this exact augmentation:

    P[B] + (3/(2N)) E[A] <= 2x-x^2/8.

This argument uses the same original q, including honest calls. Unused budget can be padded with inactive rounds. It does not charge internal legitimate secret-dependent reads as adversarial guesses.

## Relationship to the remaining coverage argument

On a run with no B, an accepting OTS component must use its canonical message, counter, chain values, and authentication nodes. A different codeword has a backward step and requires a hidden-prefix match or a noncanonical output match; the same codeword at a nonreference input is an encoding match. For FTS, accepted secrets must have been disclosed already, and all authentication nodes are canonical. Otherwise verification causes a hidden-secret match or a noncanonical output match.

Hence a strong forgery without B must use a message-hash input whose forest coordinates are all covered by successful signing responses at other inputs. If the same message and randomizer had produced a successful signature, the canonical component values make the accepted signature identical to that response, so it is not a strong forgery. This preserves target-input exclusion. Retry exhaustion does not create an exception: a canonical OTS input with J=none has no accepted counter.

To conclude the desired full bound, one still needs the charged coverage inequality in this same stopped experiment,

    P[covered forgery and no B] <= (3/(2N)) E[A] + 2^-16 x + epsilon.

The paid-probe estimate would then give P[forge]<=2x-x^2/8+2^-16 x+epsilon. Ordinary index occupancy alone does not prove the displayed coverage inequality for previously cached targets. That remains a genuine gap.
