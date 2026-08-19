import XmssSecurity.ConcreteScheme
import XmssSecurity.SecurityGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- The concrete XMSS scheme studied by this development. -/
noncomputable abbrev xmssScheme : Scheme := Concrete.scheme

/-- An adaptive adversary against the concrete XMSS scheme. -/
abbrev XmssAdversary := Adversary xmssScheme

/-- The complete XMSS forgery experiment, including final verification. -/
noncomputable abbrev xmssGame (adversary : XmssAdversary) :
  OracleComp OracleWorld Bool :=
  gameCore xmssScheme adversary

/-- The probability that the adversary wins the complete XMSS experiment. -/
noncomputable abbrev xmssForgeAdvantage (adversary : XmssAdversary) : ENNReal :=
  forgeAdvantage xmssScheme adversary

/-- The whole experiment makes at most `q` random-oracle queries. -/
abbrev XmssHasHashQueryBound (adversary : XmssAdversary) (q : Nat) : Prop :=
  HasHashQueryBound xmssScheme adversary q

/-- The best forgery probability among adversaries with query budget `q`. -/
noncomputable abbrev xmssForgeAtMost (q : Nat) : ENNReal :=
  forgeAtMost xmssScheme q

/-- The concrete XMSS scheme has `bits` bits of classical random-oracle security. -/
noncomputable abbrev XmssHasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → xmssForgeAtMost q ≤
    (q : ENNReal) / ((2 ^ bits : Nat) : ENNReal)

/-- The machine-checked security claim exported by this development. -/
abbrev XmssSecurityStatement : Prop := XmssHasClassicalSecurityBits 127

end XmssSecurity
