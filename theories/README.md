# Coq Formalization
This directory contains a coq formalization of the program logics from the paper.

## Compilation Instructions
- Run `make` to build everything.
- Coq 8.15.2 is required; although other versions may work as well.

## Key Definitions and Theorems

-The syntax (Figure 2, page 3), semantics (Figure 8, page 21), and
overapproximate executions (Figure9, page 22) of FunImp can be found
in FunImp.v. The current semantics uses both an implementation and
universal specification context. The ECall_forall rules require that
no function definition is available in the implementation context.

- The Coq definition of compatibility (Definition 1, page 4) is named
  `compatible_env` and can be found in FunImp.v.

- The Coq proof of Theorem 1 (page 5) is named `compatible_Env_refine`
  and can be found in FunImp.v.

- The Coq definition of existential executions (Figure 4, page 7)
  is named `ceval_Ex` and can be found in Productive.v.

- The Coq definition of compatibility (Definition 2, page 5),
  `ex_compatible_env`, can be found in Productive.v.

- The Coq proof of Theorem 2 (page 6) is named `productive_refine` and
  can be found in Productive.v.

- The Coq definition of the universal Hoare proof rules (Figure 10, page 23)
  is named `hoare_proof` and can be found in Hoare.v.

- The Coq definition of the existential Hoare proof rules (Figure 11, page 24)
  is named `hle_proof` and can be found in HLE.v.

- The Coq definition of the Core RHLE proof rules (Figure 6, page 9)
  is named `rhle_proof` and can be found in RHLE.v.

- The Coq proof of soundness for the Core RHLE proof rules, page 11)
  is named `rhle_proof_refine` and can be found in RHLE.v.

- The Coq definition of the core + synchrnous RHLE proof rules (Figure
  6, page 9; SyncLoops rule, page 11 ) is named `rhle_proof` and can
  be found in RHLE2.v.

- The Coq proof of soundness for the core + synchronous RHLE proof
  rules (Theorem 3, page 11) is named `rhle_proof_refine` and can be
  found in RHLE2.v.
