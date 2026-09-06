import SphincsSecurity.Proof.FtsProbeNativeHistory

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure PublishedSignatureBody where
  randomness : Randomness
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  counter : Layer → Counter
  chainValue : Layer → ChainIndex → Digest
  authPath : PathIndex → Digest

def PublishedSignatureBody.complete (body : PublishedSignatureBody) (selected : FtsTree → Digest) : Signature :=
  ⟨body.randomness, selected, body.ftsPath, body.counter, body.chainValue, body.authPath⟩

noncomputable def publishSignatureBody (randomness : Randomness) (index : Index)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) (Option PublishedSignatureBody) :=
  match traverseOption layers with
  | none => pure none
  | some parts => do
      let published ← sequenceFin fun lay => revealLayerValues index lay (parts lay).encoding
      pure (some ⟨randomness, ftsPath, fun lay => (parts lay).counter,
        fun lay => (published lay).1, flattenPaths fun lay => (published lay).2⟩)

theorem publishChronologicalSignature_eq_body
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers =
      (Option.map fun body => body.complete (fun tree => ftsSecret index tree (leaves (ftsIndexOf tree)))) <$>
        publishSignatureBody randomness index ftsPath layers := by
  unfold publishChronologicalSignature publishSignatureBody
  cases traverseOption layers <;> simp [PublishedSignatureBody.complete]

def completePublicationEntry (selected : FtsTree → Digest)
    (entry : HistoryResolvedPrefix (Option PublishedSignatureBody × SplitHashCache)) :
    HistoryResolvedPrefix (Option Signature × SplitHashCache) :=
  ⟨entry.context, entry.remaining, (entry.value.1.map (fun body => body.complete selected), entry.value.2), entry.history⟩

theorem runHistory_publishChronologicalSignature_eq_body
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache) :
    runResolvedHistoryPrefix
      (eraseProbeQueries ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers).run cache))
      context fuel history =
      Option.map (completePublicationEntry (fun tree => ftsSecret index tree (leaves (ftsIndexOf tree)))) <$>
        runResolvedHistoryPrefix
          (eraseProbeQueries ((publishSignatureBody randomness index ftsPath layers).run cache)) context fuel history := by
  rw [publishChronologicalSignature_eq_body]
  simp only [StateT.run_map, eraseProbeQueries_map, runResolvedHistoryPrefix_map]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
