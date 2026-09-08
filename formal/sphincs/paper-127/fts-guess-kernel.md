# The exact hidden-secret kernel and forced first guesses

This note spells out the conditional kernels used in fts-useful-witness.md. It applies to the exposed canonical graph of paid-probe-quadratic.md, with independently sampled FTS secrets and their public leaf hashes. It does not assume that a publicly recognizable output match reveals whether a candidate was the actual secret.

## Deferred sampling invariant

For each leaf that has neither been disclosed nor truly guessed, retain a set U of possible secrets and an external table T whose input domain is the complement of U. Conditional on the augmented history, the secret is uniform on U. Different active leaves have independent secrets. The canonical answer at that secret is its fixed public leaf hash Y; every other unobserved row is an independent uniform oracle answer. High output bits are sampled independently and cached at their rows.

Initially U is the full N-element set and T is empty. Honest internal reads of the planted graph do not enter this external table. Their outputs are the programmed graph labels, their intermediate inputs are not disclosed, and their original hash costs are still counted. Public graph labels, non-FTS-leaf rows, and message-oracle answers give no additional information about an unqueried FTS secret. Successful signing discloses selected coordinates only after the digest selects them; that selection and the failure mask do not inspect hidden FTS secret values.

A true-guess candidate is a correctly sized digest payload at that leaf's domain. Other byte strings cannot be its secret input; their rows remain independent and may still cause the separately charged noncanonical output match. A fresh external query at a candidate z in U has the following exact two-branch kernel, with u=|U|:

    probability 1/u:     secret=z, return Y, retire this leaf from true-guess counting;
    probability 1-1/u:   replace U by U\{z}, return an independent uniform answer,
                        and record that answer at z in T.

In the miss branch the answer may equal Y. Conditional on either answer, the remaining secret is still uniform on U\{z}. A repeated query z outside U returns its cached answer and cannot be a first true guess. When signing discloses an active leaf, sample its secret uniformly from U and retire that coordinate. Retired leaves retain their fixed secret and all prior rows for subsequent queries and disclosures.

These rules follow by conditioning the planted table H(S)=Y with S uniform. For a miss answer y, each s in U\{z} has joint mass 1/(uN), irrespective of whether y=Y. Thus the rules preserve the invariant by induction, including repeated queries, alternative preimages, adaptive query choices, and later disclosures. A true-guess flag belongs only to the augmented analysis; the original adversary sees the returned answer and the actual signing response.

The invariant does not permit arbitrary secret-dependent auxiliary leakage. Its application to the concrete scheme relies on the exact canonical graph exposure and on disclosure of coordinates chosen without inspecting their hidden values. It preserves every signing response, including Option failures, and the actual message-oracle transition law.

## Change only the local branch probabilities

Index original hash calls by t=1,...,q, including internal calls and final verification. Eligible calls are fresh external queries to active FTS leaves. At an eligible slot let p_t=1/|U_t|; otherwise put p_t=0. Since at most q candidates have been excluded from a leaf, p_t<=h=1/(N-q).

For a fixed j, define Q_j by replacing each eligible branch before j by the conditional miss kernel, and replacing the branch at j by the conditional hit kernel when that slot is eligible. After j use the original kernels. If execution stops early or j is ineligible, retain the ordinary killed execution and give that path weight zero below.

For a path of Q_j reaching an eligible slot j, put

    L_j = p_j * product_(t<j) (1-p_t).

All remaining transition factors, including original message queries, signing disclosures, cache updates, and auxiliary proposal bridges, are identical on the corresponding augmented path. Finite kernel multiplication therefore gives, for any nonnegative function F of the augmented transcript,

    E_real[1_{first true guess is j} F] = E_(Q_j)[L_j F] <= h E_(Q_j)[F].

Use zero weight for paths not reaching an eligible j. The equality includes terminal transcripts of varying lengths by padding with inert slots. q bounds hash slots, not the number of uniform-sampling operations; transitions between hash slots retain their original kernels. This comparison makes no independence assumption about F or whether its certificate was completed before j.

Every modified branch of positive mass has positive mass in the original augmented experiment: there is always a possible remaining secret, and before a forced miss there are at least two possibilities because j<=q<N. A final choice for every deferred secret, together with the retained rows and programmed graph, realizes the same concrete execution. Hence the whole-experiment syntactic bound q remains valid; no extra hash budget is introduced by a forced experiment.

## Compatibility with message coverage and exceptional stopping

The modified kernels inspect U, the query candidate, the public leaf hash, and already observed rows. They do not inspect an unqueried message cell. Subsequent message inputs may depend on the altered answers, but each fresh message answer still has its original uniform conditional law. The digest-selection algorithm, fixed public root, retry limit, and signing failure behavior are retained. Thus the uniform near-target estimate applies to Q_j.

Use the discrete proposal bridge of discrete-target-coupling.md with the same pre-state selected-index distribution p in both kernels on a shared augmented path. Its conditional law is identical; it cancels from L_j. Cache and deficit stopping, initial proposal-pool stopping, and proposal-prefix stopping are the same adapted rules in each game. Their indicators restrict the path comparison without conditioning either law on a future good event. Banked certificates remain counted if a later stop occurs.

Taking F to indicate a near-target certificate, and bounding this indicator by the banked certificate count, gives E_(Q_j)[F]<=557x. Summing the displayed comparison over j yields 557x^2/(1-x). It handles both chronological orders and certificates completed by later signatures. Separately, the uniform conditional hazard h for two different active leaves gives at most choose(q,2)h^2 for two distinct true guesses.

The script adaptive-kernel-checks.py exhaustively checks the local planted-table kernel at a small domain size and checks the exact rejection-bridge factorization. These finite checks support the algebra; the inductive arguments and the concrete-game interface remain necessary for formalization.
