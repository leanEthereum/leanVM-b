import SphincsSecurity.Proof.EncodingExhaustionProbability

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def EncodingCacheExtends (before after : QueryCache HashSpec) : Prop :=
  ∀ parameter position message input, input ∈ encodingRetryInputs parameter position message →
    ∀ output, before input = some output → after input = some output

theorem EncodingCacheExtends.refl (cache : QueryCache HashSpec) : EncodingCacheExtends cache cache :=
  fun _ _ _ _ _ _ h => h

theorem EncodingCacheExtends.trans {before middle after : QueryCache HashSpec}
    (hleft : EncodingCacheExtends before middle) (hright : EncodingCacheExtends middle after) :
    EncodingCacheExtends before after :=
  fun parameter position message input hinput output hcached =>
    hright parameter position message input hinput output (hleft parameter position message input hinput output hcached)

theorem EncodingCacheExtends.of_le {before after : QueryCache HashSpec} (h : before ≤ after) :
    EncodingCacheExtends before after := fun _ _ _ _ _ _ hcached => h hcached

theorem EncodingCacheExtends.exhausted {before after : QueryCache HashSpec}
    (h : EncodingCacheExtends before after) (hexhausted : AnyEncodingInputsExhausted before) :
    AnyEncodingInputsExhausted after := by
  obtain ⟨parameter, position, message, hexhausted⟩ := hexhausted
  refine ⟨parameter, position, message, ?_⟩
  intro input hinput
  obtain ⟨output, hcached, hinvalid⟩ := hexhausted input hinput
  exact ⟨output, h parameter position message input hinput output hcached, hinvalid⟩

end SphincsSecurity.Concrete
