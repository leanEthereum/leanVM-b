import SphincsSecurity
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index.toNat]!
    if !moduleName.toString.startsWith "SphincsSecurity" then continue
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
    checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} local declarations."

#print axioms SphincsSecurity.sphincs_has_127_bits_of_classical_security
#print axioms SphincsSecurity.sphincs_has_126_bits_of_classical_security
