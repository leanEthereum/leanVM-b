import XmssSecurity.CappedUnifiedTwoLaneReduction
import XmssSecurity.CappedGlobalChainHighProbeBounds

open OracleComp OracleSpec

namespace XmssSecurity

def unifiedChainTable
    (table : UnifiedSecurityIndex → Digest) :
    CappedChain.GlobalChainValueIndex → Digest :=
  fun index => table (.chainValue index)

@[simp]
theorem unifiedChainTable_apply
    (table : UnifiedSecurityIndex → Digest)
    (index : CappedChain.GlobalChainValueIndex) :
    unifiedChainTable table index = table (.chainValue index) := rfl

def unifiedChainWorldImpl :
    QueryImpl
      (RevealProbeOracleSimulation.World
        CappedChain.GlobalChainValueIndex)
      (OracleComp
        (RevealProbeOracleSimulation.World UnifiedSecurityIndex)) :=
  fun input =>
    match input with
    | .uniform n => RevealProbeOracleSimulation.uniformQuery n
    | .probe index target =>
        RevealProbeOracleSimulation.probeQuery (.chainValue index) target
    | .reveal index =>
        RevealProbeOracleSimulation.revealQuery (.chainValue index)

noncomputable def liftGlobalChainComputation
    (computation : OracleComp
      (RevealProbeOracleSimulation.World
        CappedChain.GlobalChainValueIndex) α) :
    OracleComp (RevealProbeOracleSimulation.World UnifiedSecurityIndex) α :=
  simulateQ unifiedChainWorldImpl computation

theorem liftGlobalChainComputation_isProbeQueryBoundP
    (computation : OracleComp
      (RevealProbeOracleSimulation.World
        CappedChain.GlobalChainValueIndex) α)
    (q : Nat)
    (hbound : computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery q) :
    (liftGlobalChainComputation computation).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure result => simp [liftGlobalChainComputation]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [liftGlobalChainComputation, simulateQ_query_bind]
      cases input with
      | uniform n =>
          change (RevealProbeOracleSimulation.uniformQuery n >>= fun output =>
            liftGlobalChainComputation (next output)).IsQueryBoundP
              RevealProbeOracleSimulation.IsProbeQuery q
          rw [RevealProbeOracleSimulation.uniformQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [RevealProbeOracleSimulation.IsProbeQuery]
          · intro output
            apply ih output q
            simpa [RevealProbeOracleSimulation.IsProbeQuery] using
              hbound.2 output
      | probe index target =>
          change (RevealProbeOracleSimulation.probeQuery
            (.chainValue index) target >>= fun _ =>
              liftGlobalChainComputation (next ())).IsQueryBoundP
                RevealProbeOracleSimulation.IsProbeQuery q
          rw [RevealProbeOracleSimulation.probeQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simpa [RevealProbeOracleSimulation.IsProbeQuery] using hbound.1
          · intro _
            apply ih () (q - 1)
            simpa [RevealProbeOracleSimulation.IsProbeQuery] using
              hbound.2 ()
      | reveal index =>
          change (RevealProbeOracleSimulation.revealQuery
            (.chainValue index) >>= fun value =>
              liftGlobalChainComputation (next value)).IsQueryBoundP
                RevealProbeOracleSimulation.IsProbeQuery q
          rw [RevealProbeOracleSimulation.revealQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [RevealProbeOracleSimulation.IsProbeQuery]
          · intro value
            apply ih value q
            simpa [RevealProbeOracleSimulation.IsProbeQuery] using
              hbound.2 value

theorem liftGlobalChainComputation_isProbeQueryBoundP_mono
    (computation : OracleComp
      (RevealProbeOracleSimulation.World
        CappedChain.GlobalChainValueIndex) α)
    (q : Nat)
    (hbound : computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery q) :
    (liftGlobalChainComputation computation).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery (2 * q) :=
  (liftGlobalChainComputation_isProbeQueryBoundP computation q hbound).mono
    (by omega)

def liftGlobalChainAction :
    RevealProbeOracleSimulation.ObservedAction
      CappedChain.GlobalChainValueIndex →
    RevealProbeOracleSimulation.ObservedAction UnifiedSecurityIndex
  | .probe index target => .probe (.chainValue index) target
  | .reveal index value => .reveal (.chainValue index) value

def liftGlobalChainTrace
    (trace : RevealProbeOracleSimulation.ActionTrace
      CappedChain.GlobalChainValueIndex) :
    RevealProbeOracleSimulation.ActionTrace UnifiedSecurityIndex :=
  trace.map liftGlobalChainAction

def liftGlobalChainMonitor
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex) :
    AdaptiveRevealMonitor.State UnifiedSecurityIndex := {
  pending := fun index =>
    match index with
    | .chainValue chainIndex => state.pending chainIndex
    | _ => ∅
  revealed := fun index =>
    match index with
    | .chainValue chainIndex => state.revealed chainIndex
    | _ => none
}

theorem AdaptiveRevealMonitor.State.eq_of_fields
    {Index : Type} {left right : AdaptiveRevealMonitor.State Index}
    (hpending : left.pending = right.pending)
    (hrevealed : left.revealed = right.revealed) :
    left = right := by
  cases left
  cases right
  simp_all

@[simp]
theorem liftGlobalChainMonitor_pending_chainValue
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex)
    (index : CappedChain.GlobalChainValueIndex) :
    (liftGlobalChainMonitor state).pending (.chainValue index) =
      state.pending index := rfl

@[simp]
theorem liftGlobalChainMonitor_revealed_chainValue
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex)
    (index : CappedChain.GlobalChainValueIndex) :
    (liftGlobalChainMonitor state).revealed (.chainValue index) =
      state.revealed index := rfl

@[simp]
theorem liftGlobalChainMonitor_empty :
    liftGlobalChainMonitor
        (AdaptiveRevealMonitor.State.empty :
          AdaptiveRevealMonitor.State
            CappedChain.GlobalChainValueIndex) =
      (AdaptiveRevealMonitor.State.empty :
        AdaptiveRevealMonitor.State UnifiedSecurityIndex) := by
  apply AdaptiveRevealMonitor.State.eq_of_fields
  · funext index
    cases index <;>
      simp [liftGlobalChainMonitor, AdaptiveRevealMonitor.State.empty]
  · funext index
    cases index <;> rfl

theorem liftGlobalChainMonitor_addPending
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex)
    (index : CappedChain.GlobalChainValueIndex) (target : Digest) :
    liftGlobalChainMonitor (state.addPending index target) =
      (liftGlobalChainMonitor state).addPending (.chainValue index) target := by
  apply AdaptiveRevealMonitor.State.eq_of_fields
  · funext candidate
    cases candidate <;>
      simp [liftGlobalChainMonitor, AdaptiveRevealMonitor.State.addPending,
        Function.update_apply]
  · rfl

theorem liftGlobalChainMonitor_install
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex)
    (index : CappedChain.GlobalChainValueIndex) (value : Digest) :
    liftGlobalChainMonitor (state.install index value) =
      (liftGlobalChainMonitor state).install (.chainValue index) value := by
  apply AdaptiveRevealMonitor.State.eq_of_fields
  · funext candidate
    cases candidate <;>
      simp [liftGlobalChainMonitor, AdaptiveRevealMonitor.State.install,
        Function.update_apply]
  · funext candidate
    cases candidate <;>
      simp [liftGlobalChainMonitor, AdaptiveRevealMonitor.State.install,
        Function.update_apply]

theorem tableHits_liftGlobalChainMonitor
    (table : UnifiedSecurityIndex → Digest)
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex) :
    RevealProbeOracleSimulation.tableHits (liftGlobalChainMonitor state) table =
      RevealProbeOracleSimulation.tableHits state (unifiedChainTable table) := by
  unfold RevealProbeOracleSimulation.tableHits
  congr 1
  apply propext
  constructor
  · rintro ⟨index, hindex⟩
    cases index with
    | chainValue index => exact ⟨index, hindex⟩
    | signingRandomness index => simp [liftGlobalChainMonitor] at hindex
    | encodingDigest index => simp [liftGlobalChainMonitor] at hindex
    | leafDigest epoch => simp [liftGlobalChainMonitor] at hindex
    | merkleDigest index => simp [liftGlobalChainMonitor] at hindex
  · rintro ⟨index, hindex⟩
    exact ⟨.chainValue index, hindex⟩

theorem runObserved_liftGlobalChainTrace
    (table : UnifiedSecurityIndex → Digest)
    (state : AdaptiveRevealMonitor.State
      CappedChain.GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace
      CappedChain.GlobalChainValueIndex) :
    RevealProbeOracleSimulation.runObserved table
        (liftGlobalChainMonitor state) (liftGlobalChainTrace trace) =
      RevealProbeOracleSimulation.runObserved (unifiedChainTable table)
        state trace := by
  induction trace generalizing state with
  | nil => exact tableHits_liftGlobalChainMonitor table state
  | cons action trace ih =>
      cases action with
      | probe index target =>
          simp only [liftGlobalChainTrace, List.map_cons, liftGlobalChainAction,
            RevealProbeOracleSimulation.runObserved,
            liftGlobalChainMonitor_revealed_chainValue]
          cases hrevealed : state.revealed index
          · rw [← liftGlobalChainMonitor_addPending]
            simpa [liftGlobalChainTrace] using ih (state.addPending index target)
          · simpa [liftGlobalChainTrace] using ih state
      | reveal index value =>
          simp only [liftGlobalChainTrace, List.map_cons, liftGlobalChainAction,
            RevealProbeOracleSimulation.runObserved,
            liftGlobalChainMonitor_revealed_chainValue]
          cases hrevealed : state.revealed index
          · change (if unifiedChainTable table index ∈ state.pending index then
                true
              else
                RevealProbeOracleSimulation.runObserved table
                  ((liftGlobalChainMonitor state).install
                    (.chainValue index) (unifiedChainTable table index))
                  (liftGlobalChainTrace trace)) = _
            split
            · rfl
            · rw [← liftGlobalChainMonitor_install]
              simpa [liftGlobalChainTrace] using ih (state.install index
                (unifiedChainTable table index))
          · simpa [liftGlobalChainTrace] using ih state

end XmssSecurity
