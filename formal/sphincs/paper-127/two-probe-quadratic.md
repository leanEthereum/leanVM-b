# A quadratic bound for an adaptive two-probe experiment

This is an abstract paper lemma. It establishes the quantitative conclusion under explicit information-flow assumptions. It does not establish that the full SPHINCS primitive reduction satisfies those assumptions.

## Experiment

There is a family of independent hidden labels, each uniform on an N-element set. There are at most q rounds, with q < N. In a round the adversary can test at most one candidate value against each of at most two distinct, still-hidden labels. A matching test is a hit and stops the experiment. Choices can depend on all previous misses, independent randomness, and disclosed labels. Repeating a previously failed candidate does not count as a new test.

Between rounds, labels can be disclosed for free. The choice of which label to disclose may use the existing transcript, but may not inspect undisclosed values to select it. A disclosed label is never subsequently tested for a hit. Apart from equality tests and these coordinate disclosures, the adversary receives no information about the hidden labels.

Then

    P[at least one hit] <= 2q/N - (q/N)^2.

The distinct-label requirement matters. If a round could test two different values against the same label, a single hidden label would permit success probability 2q/N with no quadratic correction when 2q <= N.

## Proof

On a surviving history, write c_i for the number of distinct failed tests against label i. Retain this count even if the label is subsequently disclosed. Conditional on the history, each undisclosed label remains uniform on its N-c_i remaining values, independently of the other undisclosed labels.

Define the process

    M = 1_survival / product_i (1-c_i/N).

For a new test against label i, a miss has conditional probability (N-c_i-1)/(N-c_i). On a miss the denominator is multiplied by that same factor. On a hit M becomes zero. Therefore the conditional expectation of M does not change. A repeated failed test, independent random choice, or allowed disclosure also preserves its expectation. Applying the argument sequentially to the two tests in a round handles adaptive choice of the second test. Consequently E[M_final]=1.

There are only finitely many nonzero counts. At termination,

    0 <= c_i <= q,    sum_i c_i <= 2q.

These constraints imply

    product_i (1-c_i/N) >= (1-q/N)^2.

One elementary way to see this is to move mass between two counts until one is zero or q. If their normalized sum is at most q/N, merging them decreases the product, since (1-u)(1-v) >= 1-u-v. If their sum exceeds q/N, replacing them by q/N and their sum minus q/N also decreases the product: the difference is (q/N-u)(q/N-v) >= 0. Packing at most 2q total mass into counts bounded by q leaves at most two full counts, which gives the displayed lower bound.

Thus M_final <= 1_survival/(1-q/N)^2. Taking expectations gives P[survival] >= (1-q/N)^2, proving the result. For q <= N/2, the process is bounded, so no limiting optional-stopping issue is needed. Variable termination can be padded with empty rounds.

The bound is tight in this abstract experiment: repeatedly test new values against the same two labels, once per label per round. The two labels independently avoid their respective q-element candidate sets with probability (1-q/N)^2.

## Relevance and the missing simulation

An adversarial structural hash query can suggest two probes: guessing an unrevealed child value in its input, and matching the node's true value with its output. The child and parent are different graph positions. If several children are unknown, testing one chosen unknown child can upper-bound the event that the entire input is correct. A random output match to an already public value can instead be represented as a probe of fresh uniform randomness.

This observation is not yet a simulation proof. In the signature experiment, honest computations use hidden inputs legitimately, signature disclosures depend on other oracle operations, and encoding targets come from rejection sampling. A guessed internal value can remain unrecognized until later verification. The original cache and the planted graph are correlated. These details must be represented without granting the adversary an extra hit flag or treating a legitimate honest query as a successful guess.

The required simulation and a bound that also pays for message queries are supplied separately in paid-probe-quadratic.md. If one hash query produces two effective tests against the same hidden label, or a disclosure selects a label using undisclosed values, the lemma here does not apply. Equality of oracle marginals alone would not prove the needed relation.

The finite dynamic program in two-probe-arithmetic.py checks the exact optimum for small instances. Its role is to check the algebraic model, not to validate the separate cryptographic simulation.
