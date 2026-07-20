# logup* migration plan

## Goal

Replace offline memory checking for memory and bytecode with two indexed logup* lookups while retaining the existing pull/push grand product only for VM state `(pc, fp)`.

The migration removes every memory/bytecode read-counter column and the count-product argument. It does not change the local instruction semantics, the write-once memory model, the public bytecode encoding, or the single stacked commitment for the ordinary witness.

## Target protocol

### 1. Build two virtual lookup vectors

For each lookup family `f in {memory, bytecode}`, concatenate its access blocks largest-first, using the same aligned stacking rule as the witness:

- `I_f`: all index columns (`address` for memory, `pc` for bytecode);
- `V_f`: the corresponding looked-up values.

There is one block per access site, not one logup* instance per site. Thus three memory reads in one instruction table contribute three blocks to the same memory stack, and every instruction table contributes its fetch block to the same bytecode stack.

The stacks are virtual. In particular, the access-side memory-value and bytecode-operand columns are omitted from the ordinary PCS, not merely omitted from a second concatenated commitment. Each announced real prefix is decomposed into aligned dyadic slices, so padding rows are absent without introducing a committed activity mask.

Local sumchecks first bind the value/operand evaluations they consume. The verifier then samples the value RLC and per-access-site batching coefficients. These define a transparent numerator `X_f` as the corresponding weighted sum of local equality polynomials, lifted into the giant access stack. Unused tail slots have numerator zero.

The lookup target is the weighted claim

```text
e_f = sum_u X_f(u) * V_f(u).
```

This target is derived from the already-bound local evaluations. Logup* discharges it without opening `V_f` or any of its source columns.

### 2. Define the two indexed tables

Memory uses

```text
J_mem[j] = g^j
T_mem[j] = M_lo[j] + theta M_hi[j] + theta^2 M_top[j].
```

The table positions are the actual VM address representation `g^j`, rather than an integer embedding. Distinctness follows from the public memory bound `2^h < ord(g)`.

The RLC challenge `theta` is sampled after the uncommitted access-value evaluations are transcript-bound. Bytecode uses

```text
J_bc[j] = g^j
T_bc[j] = op[j] + theta o1[j] + ... + theta^5 o5[j].
```

Each instruction access constructs the same RLC from its hardcoded opcode and only the operand/flag columns that the opcode uses. Structurally-zero slots remain literal zero and require no committed column. The public program supplies `T_bc`; native verification evaluates it directly, while recursive verification keeps a deferred claim on the fixed stacked bytecode columns.

### 3. Commit both pushforwards together

For each family, the prover forms

```text
Y_f[j] = sum_{u : I_f[u] = J_f[j]} X_f(u).
```

The duality check is

```text
e_f = <T_f, Y_f>.
```

`Y_mem` and `Y_bc` are `E = GF(2^192)`-valued because the local points and batching coefficients live in `E`. Split each into three `K = GF(2^64)` limbs, stack the resulting regions largest-first, and make one additional PCS commitment. This is one pushforward-stack commitment for both lookup families, not one commitment per table or access site.

This commitment must be separate from the ordinary witness commitment: the value RLC and site-combining challenges are sampled only after the virtual evaluations are bound, while the logup denominator challenge `c_f` is sampled only after the pushforward stack is committed.

### 4. Prove the two logup* identities

For each family, prove

```text
sum_u X_f[u] / (c_f - I_f[u])
    =
sum_j Y_f[j] / (c_f - J_f[j]).
```

Add a fractional-addition GKR whose leaves are numerator/denominator pairs and whose internal gate adds two fractions. Follow the reference implementation's reduction shape:

1. compare the two root fractions;
2. reduce the access side to claims on the transparent numerator and virtual index stack;
3. reduce the table side and `<T_f, Y_f> = e_f` together to a common table point;
4. send the resulting claims to the appropriate opening pool: ordinary witness, pushforward stack, or public bytecode.

Implement memory and bytecode as two domain-separated instances. Share generic code and batch compatible GKR work only after the unbatched transcript and claim flow are tested.

### 5. Retain only state grand-product balance

Keep the current pull/push abstraction for state transitions:

```text
pull (pc, fp)
push (next_pc, next_fp).
```

The grand-product code then needs only the push and pull product trees. Remove memory/bytecode flushes from this bus, remove its count tree and nonzero-root check, and narrow leaf decomposition to state columns and public boundary states.

## Implementation sequence

1. **Introduce lookup descriptors and layouts.**
   - Split state flush declarations from memory/bytecode lookup declarations in `tables.rs`.
   - Describe each lookup access as an index expression plus an `E`-valued value expression.
   - Build deterministic memory and bytecode access-stack layouts in `cpu/layout.rs`, including aligned dyadic real-row slices.
   - Preserve routing of BLAKE3 value expressions to `q_pkd`.

2. **Remove offline counters.**
   - Delete per-row memory and bytecode counters from trace rows, table schemas, fills, padding, and execution.
   - Delete final memory/bytecode counter arrays and the `MFCNT`/`BFCNT` witness columns.
   - Remove count blocks, count-root transcript data, count-related caps, and count soundness errors.
   - Update column indices, placement derivation, recursion shape certification, statistics, and tests affected by the smaller witness.

3. **Add generic logup* machinery.**
   - Add fractional-addition GKR prover/verifier code and its final-layer reduction.
   - Add virtual-stack evaluation/decomposition helpers for indices, values, transparent `g^j` table indices, and pushforward construction.
   - Port the protocol structure from `binius64/crates/{ip,ip-prover,iop}/src/logup_star*`, adapting it to `F192`, generator-power indices, the existing transcript, and weighted stacked PCS claims.
   - Enforce transcript order and domain-separate memory, bytecode, RLC, pushforward commitment, and denominator challenges.

4. **Add the shared pushforward commitment.**
   - Stack the `K` limbs of `Y_mem` and `Y_bc` into one polynomial and commit once.
   - Extend PCS plumbing to collect and batch all claims for this second commitment into one opening.
   - Keep the existing ordinary-witness opening pool unchanged except for new weighted lookup claims and removed bus/count claims.

5. **Integrate the two lookups.**
   - Memory: connect every access block to the three-limb committed memory table.
   - Bytecode: sample `theta`, RLC the six public program coordinates, and create per-opcode access expressions containing only used columns and constants.
   - Run both logup* reductions and add their index, value, table, and pushforward claims to the correct pools.
   - Replace the old bus phase in `cpu::prove`/`verify` with state balance followed by the two lookup reductions.

6. **Update recursion and documentation.**
   - Replace the bus-derived bytecode claim with the public bytecode-table claim produced by logup* and update recursive aggregation/deferred evaluation handling.
   - Remove `count_root` and count inverse logic from verification summaries and guests.
   - Rewrite `misc/doc.tex`: M3/state bus, logup* construction, fraction GKR, stacking, transcript order, soundness, instruction-table column lists, padding, and the unrolled protocol.
   - Update stale module comments and README cost figures.

## Verification plan

- Unit-test pushforward duality and generator-power table indices for memory and bytecode.
- Test virtual stacking across unequal table sizes, multiple accesses per table, omitted bytecode slots, successor addresses, active-row masking, and empty opcode tables.
- Test honest and tampered logup* proofs: wrong index, wrong value, wrong RLC slot, wrong pushforward, wrong table, and transcript reordering.
- Check prover/verifier transcript parity and full stream consumption for both commitments.
- Run all existing VM, compiler, BLAKE3/flock, PCS, and recursive-aggregation tests.
- Add end-to-end cases covering every opcode, different numbers of memory accesses per row, non-power-of-two real row counts, no-BLAKE3 execution, and BLAKE3 virtual value routing.
- Compare committed witness size, pushforward commitment size, proof size, and prover/verifier time against the current offline-memory baseline.

## Completion criteria

- No memory or bytecode counter remains in the trace, witness, constraints, transcript, or documentation.
- No access-side memory-value or bytecode-operand column is included in the ordinary PCS.
- Exactly two indexed logup* relations cover all memory and bytecode access sites.
- Both pushforwards share one additional stacked commitment and one batched opening.
- The only grand-product balance argument is the state `(pc, fp)` pull/push chain.
- Native and recursive verification accept existing valid programs and reject lookup tampering.
