-- SPDX-License-Identifier: MPL-2.0
-- Prints the axioms every Lean-leg theorem rests on (PROOF-POLICY §8.4).
-- scripts/check-legs.sh requires each line to read "does not depend on any axioms".
import SecretTypes
#print axioms SecretTypes.eval_low
#print axioms SecretTypes.confine
#print axioms SecretTypes.tini
#print axioms SecretTypes.Two.eval_low_two
#print axioms SecretTypes.Two.confine_two
#print axioms SecretTypes.Two.tini_two
#print axioms SecretTypes.Two.termination_sensitive_fails
#print axioms SecretTypes.Countermodels.NoUpper₁.refutes
#print axioms SecretTypes.Countermodels.NoUpper₂.refutes
#print axioms SecretTypes.Countermodels.NoDownClosure.refutes
#print axioms SecretTypes.Countermodels.NoTrans.refutes
