import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalResidualRouting
import SphincsSecurity.Proof.PublicResidualLookup

namespace SphincsSecurity.Concrete.ResidualByteAction

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

inductive Action (inputs : Finset HashInput) where
  | known (answer : HashOutput)
  | read (input : inputs)
  | probe (input : inputs) (test : Probe CanonicalCoordinate)

def Local {inputs : Finset HashInput} (input : inputs) : Action inputs → Prop
  | .known _ => True
  | .read row => row = input
  | .probe row _ => row = input

noncomputable def eval {inputs : Finset HashInput} (labels : Labels) (seed : inputs → HashOutput) : Action inputs → Option HashOutput
  | .known answer => some answer
  | .read input => some (seed input)
  | .probe input test => if test.keep labels (seed input) then some (seed input) else none

noncomputable def fresh (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows) (input : inputs) : Action inputs :=
  match route parameter words disclosed known input.val with
  | .outside => (knownEncodingRowAt parameter inputs hencoding known input).elim (.read input) (fun row => .known (rows row))
  | .canonical position => .known (publicReplies position)
  | .probe test => .probe input test

theorem fresh_local (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows) (input : inputs) :
    Local input (fresh parameter inputs hencoding words disclosed known publicReplies rows input) := by
  unfold fresh
  cases route parameter words disclosed known input.val with
  | outside => cases knownEncodingRowAt parameter inputs hencoding known input <;> trivial
  | canonical _ => trivial
  | probe _ => rfl

theorem fresh_eq_routed (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual) (publicReplies : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : inputs) :
    eval actual seed (fresh parameter inputs hencoding words disclosed known publicReplies rows input) =
      routedTableReply publicReplies actual
        (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding known rows seed)) input.val
        (route parameter words disclosed known input.val) := by
  have hspec := route_spec parameter words disclosed known actual hagrees input.val
  rw [fresh]
  cases hroute : route parameter words disclosed known input.val with
  | outside =>
      rw [routedTableReply, finiteHashAnswer_none ∅ inputs _ input.val input.property (by simp), knownReferenceResidual_lookup]
      cases knownEncodingRowAt parameter inputs hencoding known input <;> rfl
  | canonical position => rfl
  | probe test =>
      rw [hroute] at hspec
      have hat : ∃ position, AtPosition parameter input.val position := by
        cases test with
        | pair child parent hne candidate => exact ⟨hspec.choose, hspec.choose_spec.1⟩
        | output parent => exact ⟨hspec.choose, hspec.choose_spec.1⟩
      obtain ⟨position, hat⟩ := hat
      rw [routedTableReply, knownReferenceResidual_structural parameter inputs hencoding known rows seed input.val position hat,
        finiteHashAnswer_none ∅ inputs seed input.val input.property (by simp)]
      rfl

theorem fresh_eq_stopped (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual) (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = replies position)
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : inputs) :
    eval actual seed (fresh parameter inputs hencoding words disclosed known publicReplies rows input) =
      stoppedTableReply parameter words disclosed actual replies
        (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding known rows seed)) input.val := by
  rw [fresh_eq_routed parameter inputs hencoding words disclosed known actual hagrees publicReplies rows seed input]
  exact (stoppedTableReply_route parameter words disclosed known actual hagrees replies publicReplies hreplies _ input.val).symm

theorem fresh_eq_original (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (replies publicReplies : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret replies))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = replies position)
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : inputs) :
    let actual := CanonicalCoordinate.value otsSecret ftsSecret replies
    let answer := programmedHash parameter otsSecret ftsSecret replies
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding replies rows seed)) input.val
    eval actual seed (fresh parameter inputs hencoding words disclosed known publicReplies rows input) =
      if CanonicalProbeRouting.Bad parameter words disclosed actual input.val answer then none else some answer := by
  dsimp only
  rw [fresh_eq_stopped parameter inputs hencoding words disclosed known _ hagrees replies publicReplies hreplies rows seed input,
    stoppedTableReply, tableReply_programmed,
    canonicalReferenceResidual_eq_known parameter inputs hencoding words disclosed known otsSecret ftsSecret replies hagrees]

end SphincsSecurity.Concrete.ResidualByteAction
