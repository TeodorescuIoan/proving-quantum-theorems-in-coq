From QuantumLib Require Import Quantum.


Lemma phase_kickback_cnot : 
  (hadamard ⊗ hadamard) × cnot × (hadamard ⊗ hadamard) = notc.
Proof. 
  prep_matrix_equivalence.
  unfold kron, hadamard, cnot, notc, Mmult; simpl.
  assert (H: C2 * (/ C2 * / C2) + / C2 * / C2 + / C2 * / C2 = C1)
    by (rewrite !Cmult_assoc; lca). 
  by_cell; try lca; autorewrite with C_db; apply H.
Qed.

