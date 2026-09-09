# Initial hidden-coordinate sampling and the next composition gate

This is a paper derivation against `3bf4e874`. It changes no Lean code. The public security theorem remains 126 bits. The result derived here is the initial product prior required by `publicSigningRun_posterior` in [PublicSigningNative.lean](../SphincsSecurity/Proof/PublicSigningNative.lean); the adaptive original-game correspondence and the 127-bit probability bounds remain formalization obligations.

The initial sampling identities are now formalized in [CanonicalCoordinateSampling.lean](../SphincsSecurity/Proof/CanonicalCoordinateSampling.lean), [UniformPublicCoordinates.lean](../SphincsSecurity/Proof/UniformPublicCoordinates.lean) and [CanonicalPublicPrior.lean](../SphincsSecurity/Proof/CanonicalPublicPrior.lean). [ReferenceCoordinateGame.lean](../SphincsSecurity/Proof/ReferenceCoordinateGame.lean) transports them to the original SUF game with its hash bound, and [PublicSigningInitial.lean](../SphincsSecurity/Proof/PublicSigningInitial.lean) connects the concrete prior to the lazy signing record. The remaining composition checks below are still required.

[AdaptiveResidualLabels.lean](../SphincsSecurity/Proof/AdaptiveResidualLabels.lean) and [AdaptiveResidualErasure.lean](../SphincsSecurity/Proof/AdaptiveResidualErasure.lean) now formalize joint completion through an adaptive residual-read, probe and disclosure interface, including retained auxiliary stops. [ReferenceJointPrior.lean](../SphincsSecurity/Proof/ReferenceJointPrior.lean) supplies the original game's matching initial joint sampler. The transition classification, private signing translation, original cost accounting and coverage correspondence below still have to connect the concrete SPHINCS execution to that interface.

## An exact finite reindexing

Let \(D=\{0,\ldots,N-1\}\), where \(N=2^{128}\). Let \(A\) index the OTS starting secrets, \(F\) index the FTS secrets, and \(P\) index canonical graph positions. These are the finite index types already present in `Statement.lean` and `CanonicalHiddenCoordinates.lean`. Write their cardinalities as \(a,f,p\), and put \(C=A\sqcup F\sqcup P\).

After the established graph and reference sampling transformations, the original experiment samples independent uniform secret tables \(S_A\in D^A\), \(S_F\in D^F\), and full graph replies \(G\in(D\times D)^P\). Here a full reply is identified bijectively with its low and high 128-bit halves. It also samples a reference auxiliary \(\xi=(J,E,R)\), consisting of all first-success selections, the conditionally sampled encoding rows, and an independent full residual seed on a fixed finite input envelope. The auxiliary is independent of the secret tables and graph replies. Its internal components need not be mutually independent.

Define

\[
L(c)=
\begin{cases}
S_A(c),&c\in A,\\
S_F(c),&c\in F,\\
\operatorname{low}(G(c)),&c\in P,
\end{cases}
\qquad V(p)=\operatorname{high}(G(p)).
\]

This map is a bijection from \(D^A\times D^F\times(D\times D)^P\) to \(D^C\times D^P\). Its inverse reads the two secret tables from their tagged coordinates and reconstructs each full graph reply from \((L(p),V(p))\). Every source atom has mass

\[
N^{-a}N^{-f}N^{-2p}=N^{-|C|}N^{-p}.
\]

Consequently \(L\) is a uniform table on all canonical coordinates, \(V\) is an independent uniform table of high halves, and both are independent of \(\xi\). This is a joint distribution identity retaining every secret and full graph reply. It does not discard high halves, assume that distinct coordinates have distinct numerical values, or assert that a real chain endpoint is independent of the functions leading to it. The programmed oracle must still be reconstructed from these samples.

## Revealing the initial public coordinates

Fix a supported auxiliary value \(\xi\) and the fixed valid dummy used on encoding exhaustion. Its selections determine the reference words \(w\). With no FTS disclosures initially, let \(H_w\subseteq C\) be exactly the coordinates satisfying `CanonicalCoordinate.Hidden w (fun _ _ _ => False)`, and let \(U_w=C\setminus H_w\). This partition depends on \(\xi\), but not on \(L\) or \(V\).

Sample \(K\) uniformly in \(D^{U_w}\), and define candidate sets

\[
\mathcal A_{w,K}(c)=
\begin{cases}
D,&c\in H_w,\\
\{K(c)\},&c\in U_w.
\end{cases}
\]

Every set is nonempty. Sampling a uniform \(L\in D^C\) and retaining its public restriction is equivalent to sampling \(K\), then independently completing these candidate sets. For every compatible full table, the latter sampler assigns mass

\[
N^{-|U_w|}\prod_{c\in C}|\mathcal A_{w,K}(c)|^{-1}
=N^{-|U_w|}N^{-|H_w|}=N^{-|C|}.
\]

In particular,

\[
\mathcal L\bigl(L\mid \xi,V,L|_{U_w}=K\bigr)
=\bigotimes_{c\in C}\operatorname{Unif}(\mathcal A_{w,K}(c)).
\]

The statement holds pointwise for every supported conditioning value. Equivalently, substitute the two-stage sampler inside any continuation depending on the auxiliary, high halves, public restriction and completed labels. This stronger form is the appropriate connection to `referenceResidualGame_eq_auxiliary` and `UniformTableCompletion.complete`.

Extend \(K\) to the interface's `known` table by using a fixed zero at hidden coordinates. Then `PublicAgreement` holds on every supported completion. Define `publicReplies` by pairing this known low half with \(V\) at each graph position. It agrees with the actual full reply whenever the parent graph coordinate is public. The byte router returns such a reply only when the canonical input has no hidden child; `parent_public_of_no_hidden_child` proves that its parent is then public. The arbitrary low halves supplied at hidden positions are therefore never returned by that route.

The existing public-opening lemmas derive the root, OTS frontiers and authentication paths from `known`. Thus there is no additional condition on hidden coordinates when forming these initial values. This proves the initial product-prior claim on paper. A later FTS disclosure must instead use the proved conditional disclosure kernel and update its candidate set to a singleton; it cannot be modeled as an independent new secret draw.

## A sampler is different from an observed history

The previous identity permits sampling the entire auxiliary first. It does not permit treating its entire residual seed as revealed when applying a fresh-query probability bound. If a uniform seed \(R\) is fixed and an input \(z\) is fixed, the conditional law of \(R(z)\) is a point mass. Its conditional probability of matching a specified public digest can be zero or one. The average over an unobserved uniform row has the desired probability \(1/N\).

This distinction determines the next implementation contract. The ambient probability space may retain the full seed, while the analytical execution history reveals only the rows inspected so far. Conditional encoding rows also remain subject to their first-success law and the rows actually inspected. A canonical counter block is not an unrestricted uniform block after conditioning on its selected result. Fresh structural and message rows are in separate domains from those blocks.

Use a partial residual table to record actual seed reads, an external reply cache to record answers available from external queries, and separate signing and coverage records. Their roles differ: a public canonical reply comes from \(G\), while a surviving noncanonical structural reply comes from \(R\). Private structural work has already been replaced by public results and original cost markers, so it must not populate an external cache or expose private prefix inputs. Private message attempts still inspect message rows and must participate in the message-table completion law.

For each supported live history, the desired induction invariant retains both the candidate-set law for \(L\) and the conditional completion law for the residual rows. All query choices and auxiliary transitions must be causal for that retained history. The required transition checks are:

1. A repeated external query returns its cached full answer, consumes its original hash cost, and creates no new residual-row constraint or probe. Cache cleanliness persists under later FTS disclosures.
2. A new public canonical query returns the reconstructed full graph reply. It makes no residual seed read and does not inspect a hidden coordinate.
3. A new noncanonical structural query uses a fresh full residual reply. On a surviving unary probe, the transcript imposes only \(L(c)\ne z\) and \(L(p)\ne\operatorname{low}(y)\), with \(c\ne p\); on an output-only probe, it imposes only the latter condition. These are exactly the existing candidate-set restrictions. The residual-row constraint records the full \(y\), including its high half.
4. A hidden canonical input causes the first-match stop. Its answer is not returned. The retained stop state must depend on the prior history and charged call, without exposing the hidden programmed reply. No product-posterior assertion on hidden labels conditioned on the stop is needed for the current erasure theorem.
5. A signing request runs the original finite message loop and forms its public plan. A successful plan discloses the selected FTS coordinates by the conditional disclosure kernel. A failed plan discloses none and retains its selected view if selection preceded failure. Both outcomes retain the original cost trace and the complete original signing log.
6. Budget guards and coverage updates use this same retained execution. An invocation that stops partway through must retain the work and records reached so far. The existing completed-signing equality does not by itself prove this partial-execution property.

The external cases in items 1 through 4 are now connected to the joint prior in [ResidualBytePrior.lean](../SphincsSecurity/Proof/ResidualBytePrior.lean), using the original programmed fixed table and an empty initial external cache. [ResidualByteRun.lean](../SphincsSecurity/Proof/ResidualByteRun.lean) proves the fixed-table correspondence through arbitrary randomized adaptive external computations with fixed reference and disclosure data and a finite envelope containing all their possible queries. Cache invariants ensure a residual structural probe cannot silently skip its test because of an earlier unrecorded external read. Public canonical and conditioned encoding replies use their separate lookups. The projected stopped law, surviving posterior and source hash bound all transfer to the lazy interface.

Items 5 and 6 remain to be composed with this external interface. The structural stopping rule also does not yet include nonreference equal-code encodings. Their probability estimate must hide unqueried encoding rows in its own history or extend the joint completion state to those rows. Conditioning on the full encoding auxiliary, as the structural posterior permits, would make a fixed encoding reply deterministic. None of these component correspondences establishes either original-game security interval.

## The next security endpoint

The new [prefix joint prior](../SphincsSecurity/Proof/ReferencePrefixGame.lean) resolves the encoding-tail sampling issue without exposing future oracle replies. Its auxiliary retains the conditioned prefix through the first valid counter, or the whole block on exhaustion. A proved row-swap bijection moves all unconditioned tails into the independent residual seed and preserves the complete oracle-table law. The prefix sampler inherits the original SUF probability and hash budget, and the [prefix signer correspondence](../SphincsSecurity/Proof/ReferencePrefixSigning.lean) preserves the original record. The byte interpreter still needs to use the new prefix lookup; its existing whole-block lookup and erasure theorem describe the earlier sampler. After that connection, unrestricted encoding tails share the residual history used for fresh structural and message rows.

Keep the next target as the original-game large-budget interval from the [closing contract](minimal-closing-contract.md). Establish the full interpreter correspondence above, the accepting-verifier classification, and coverage under its causal first-match stopping rule. Then derive, with \(x=q/2^{128}\),

\[
\Pr[\mathrm{SUF}]
\le 2x-x^2+\frac{11}{2^{16}}x+\epsilon(q),
\qquad 3/2^{14}\le x<1/2.
\]

This would be an original-game security result on a nontrivial interval. The small-budget endpoint would still require the concrete causal OTS comparison, shared witness charges and coverage in each forced-FTS law. Those remain sources of mathematical uncertainty when estimating completion, even after the large-budget correspondence is finished.
