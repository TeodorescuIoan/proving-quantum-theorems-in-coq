From QuantumLib Require Import Quantum.

(*
  A CNOT gate operates as follows:

   |Φ⟩ ---|--- |Φ⟩  
   |Ψ⟩ ---⊕--- |Ψ⟩ ⊕ |Φ⟩ 

  However, surrounding it by Hadamard
  gates will reverse the control bit:
*)
Lemma phase_kickback_cnot : 
  (hadamard ⊗ hadamard) × cnot × (hadamard ⊗ hadamard) = notc.
Proof. crunch_matrix; lca. Qed.

