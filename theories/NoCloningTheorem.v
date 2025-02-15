From QuantumLib Require Import VectorStates.
Require Import Psatz.

Section sec_no_cloning.

(* TODO: add strict version of theorem *)
Theorem No_Cloning_Theorem {n : nat} :
  ~ exists (U : Square (n*n)), forall (z x : Vector n),
      U × (x ⊗ z) = x ⊗ x.
Proof.
  apply Classical_Pred_Type.all_not_not_ex.
  intros U HClone.
  generalize HClone.
  apply Classical_Pred_Type.ex_not_not_all.
  eexists ?[zero].
  apply Classical_Pred_Type.ex_not_not_all.
  eexists (/ √ 2 .* (?[φ] .+ ?[ψ])).
  rewrite
    Mscale_kron_dist_l, Mscale_mult_dist_r, kron_plus_distr_r,
    Mmult_plus_distr_l, !HClone, Mscale_plus_distr_r.
  autounfold with U_db.
  intros [=Hfuneq%(f_equal2_inv 0%nat 0%nat)].
  generalize Hfuneq.
  rewrite Nat.Div0.div_0_l, Nat.Div0.mod_0_l.
  [φ]: exact (basis_vector n 0).
  [ψ]: exact (basis_vector n 0).
  [zero]: auto.
  autorewrite with C_db R_db. 
  rewrite
    Cmult_comm, Cinv_sqrt2_proper, Cdiv_unfold,
    <- Cmult_assoc, Cinv_l, Cmult_1_r, Csqrt2_sqrt
    by (intros [=]; lra).
  intros [=Hneq%(sqrt_lem_0 _ _)]; lra.
Qed.

End sec_no_cloning.

