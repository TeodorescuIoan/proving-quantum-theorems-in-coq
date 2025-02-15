From QuantumLib Require Import Quantum Complex Eigenvectors CauchySchwarz.

Section sec_heisenberg.

Local Open Scope R_scope.

(** Basic definitions *)

(* The expected value of observing A repeatedly on the same state x *)
Definition expectedval {n : nat} (x : Vector n) (A : Square n) : R := 
  fst ⟨x, A × x⟩.
   
(* Δ(x,A) = A - ⟨x, A × x⟩ * I *)
Definition deviation {n : nat} (x : Vector n) (A : Square n) : Square n := 
  A .+ -1 * ⟨x, A × x⟩ .* I n.

(* The expected value of the deviation squared *)
(* Var(x, A) = expectedval (Δ(x,A))² = ⟨x, (A - ⟨x, A × x⟩ * I)² × x⟩*)
Definition variance {n : nat} (x : Vector n) (A : Square n) : R := 
  expectedval x (Mmult_n 2 (deviation x A)).

Definition commutator {n : nat} (A B : Square n) : Square n :=
  A × B .+ - C1 .* B × A.

Definition anticommutator {n : nat} (A B : Square n) : Square n :=
  A × B .+ B × A.

(** Helper lemmas about complex numbers *)

Lemma Cmod_4_sqr_inv_2 : (/ 4) = ((Cmod (/ 2 ))^ 2).
Proof. now unfold Cmod; rewrite pow2_sqrt; simpl; lra. Qed.

(* Real numbers are equal to their complex conjugate *)
Lemma Cconj_complex_real : forall (r : C), snd r = 0 -> r ^* = r.
Proof. now intros [] [=]; lca. Qed.

(* Mathematical version of the complex modulus formula *)
Lemma Cmod_pow2_reals : 
  forall (x y : C), snd x = 0 -> snd y = 0 -> 
    Cmod (x + Ci * y) ^2 = (fst x)^2 + (fst y)^2.
Proof.
  intros [] [] [=->] [=->].
  unfold Cmod, Ci, snd in *.
  simpl.
  autorewrite with C_db R_db.
  rewrite sqrt_def, <- !Rsqr_def; [lra |].
  now apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(** Lemmas about hermitian operators, commutators and variances *)

Lemma hermitian_implies_real_inner_product : 
  forall {n : nat} (A : Square n) (x : Vector n),
    hermitian A -> snd ⟨x, A × x⟩ = 0.
Proof.
  intros * HHerm.
  apply Cconj_eq_implies_real.
  now rewrite <- inner_product_comm_conj, inner_product_adjoint_switch, HHerm.
Qed.

(* Mathematically equivalent to hermitian_implies_real_inner_product *)
Lemma hermitian_prod_complex_pair_eq :
  forall {n : nat} (A : Square n) (x : Vector n),
    hermitian A -> ⟨x, A × x⟩ = (fst ⟨x, A × x⟩, 0).
Proof.
  intros.
  now rewrite <- (hermitian_implies_real_inner_product A x), <- surjective_pairing.
Qed.

(* Multiplication by scalar preserves the hermitian property *)
Lemma scale_hermitian : forall {n : nat} (A : Square n) (r : C),
  snd r = 0 -> hermitian A -> hermitian (r .* A).
Proof.
  intros n A r Hreal HHerm.
  unfold hermitian.
  now rewrite Mscale_adj, HHerm, Cconj_complex_real.
Qed.

Lemma hermitian_deviation_generalized : 
  forall {n : nat} (A : Square n) (r : C), 
  snd r = 0 -> hermitian A -> hermitian (A .+ -1  * r .* I n).
Proof.
  intros.
  apply plus_hermitian.
  auto.
  now apply (scale_hermitian);
  [ simpl; lra 
  | apply I_hermitian
  ].
Qed.

(* Δx(A) * Δx(B) + Δx(B) * Δx(A) is hermitian *)
Lemma hermitian_deviation_anticommutator : 
  forall {n : nat} (x : Vector n) (A B : Square n), hermitian A -> hermitian B -> 
    hermitian (anticommutator (deviation x A) (deviation x B)).
Proof.
  intros * HAHerm HBHerm.
  unfold anticommutator, hermitian, deviation.
  rewrite !Mplus_adjoint, !Mmult_adjoint, !Mplus_adjoint.
  rewrite !Mscale_adj, id_adjoint_eq, Mplus_comm, !Cconj_mult_distr.
  now repeat f_equal; auto; try lca; rewrite hermitian_prod_complex_pair_eq; try lca.
Qed.

Lemma adjoint_commutator_neg : forall {n : nat} (A B : Square n),
  hermitian A -> hermitian B -> (commutator A B) † = -1 .* commutator A B.
Proof.
  intros *.
  unfold hermitian, commutator.
  rewrite 
    !Mplus_adjoint, !Mmult_adjoint,
    Mscale_plus_distr_r, Mscale_adj,
    Mscale_mult_dist_r, Mplus_comm.
  intros -> ->.
  autorewrite with C_db.
  rewrite Mscale_mult_dist_l, Mscale_assoc.
  prep_matrix_equality.
  now lca.
Qed.

Lemma hermitian_neg_i_commutator : 
  forall {n : nat} (A B : Square n),
    hermitian A -> hermitian B -> hermitian (-Ci .* commutator A B).
Proof.
  intros.
  unfold hermitian.
  rewrite Mscale_adj, adjoint_commutator_neg, Mscale_assoc; auto.
  f_equal.
  now lca.
Qed.

(* ⟨x, (A - ⟨x, A × x⟩ * I)² × x⟩ = || (A - ⟨x, A × x⟩ * I) × x ||² *)
Lemma variance_norm_sq_eq : forall {n : nat} (x : Vector n) (A : Square n),
  WF_Matrix A -> hermitian A -> 
    variance x A = fst ⟨deviation x A × x, deviation x A × x⟩.
Proof.
  intros.
  unfold variance, deviation, expectedval, Mmult_n.
  rewrite 
    Mmult_1_r, Mmult_assoc, inner_product_adjoint_switch,
    (hermitian_deviation_generalized A); auto;
  [ now apply hermitian_implies_real_inner_product
  | apply WF_plus; auto; repeat apply WF_scale; apply WF_I
  ].
Qed.

Lemma commutator_deviation_var_eq :
  forall {n : nat} (x : Vector n) (A B : Square n),
    WF_Matrix A -> WF_Matrix B ->
      commutator (deviation x A) (deviation x B) = commutator A B.
Proof.
  intros.
  unfold commutator, deviation.
  now rewrite 
    !Mmult_plus_distr_r, !Mmult_plus_distr_l,
    !Mscale_plus_distr_r, !Mmult_plus_distr_r, 
    !Mscale_assoc, !Mscale_mult_dist_r, 
    <- !Mplus_assoc, !Mscale_mult_dist_l, 
    !Mmult_1_r, !Mmult_1_l; auto;
  [ prep_matrix_equality; lca 
  | apply WF_I
  ].
Qed.

(** Proof of the hermitian version of Heisenberg's uncertainty principle *)

(* Intermediate equality *)
Lemma interm_Uncertainty_Principle : forall {n : nat} (x : Vector n) (A B : Square n),
  WF_Matrix A -> WF_Matrix B -> hermitian A -> hermitian B ->
    (Cmod ⟨deviation x A × x, deviation x B × x⟩)^2 = 
      ((/ 4) * (Cmod (⟨x, (anticommutator (deviation x A) (deviation x B)) × x⟩ 
        + Ci * ⟨x, (-Ci .* commutator A B × x)⟩))^2).
Proof.
  intros * WFA WFB HHermA HHermB.
  rewrite 
    <- inner_product_scale_r, <- Mscale_mult_dist_l, Mscale_assoc,
    <- Copp_mult_distr_r, Ci2, Copp_involutive, Mscale_1_l,
    <- (commutator_deviation_var_eq x) by auto.
  rewrite <- inner_product_plus_r. 
  rewrite <- Mmult_plus_distr_r.
  unfold commutator, anticommutator.
  rewrite <- (Mscale_1_l _ _ (_ B × _ _ A)), Mplus_comm, Mplus_assoc.
  rewrite 
    (Mplus_comm _ _ (_ × _) (C1 .* (_ × _))),
    <- (Mplus_assoc _ _ (- _ .* _ × _)  (C1 .* _)), (Mscale_mult_dist_l ).
  rewrite <- Mscale_plus_distr_l, Cplus_comm.
  rewrite <- (Cminus_unfold ), (Cminus_diag 1 C1), Mscale_0_l, Mplus_0_l by auto.
  rewrite <- (Mscale_1_l _ _ (_ _ A × _ _ B)), <- Mscale_plus_distr_l.
  autorewrite with C_db.
  rewrite Cmod_4_sqr_inv_2. 
  rewrite <- Rpow_mult_distr.
  rewrite <- Cmod_mult.
  rewrite <- inner_product_scale_r.
  rewrite <- Mscale_mult_dist_l, Mscale_assoc, Cinv_l, Mscale_1_l 
    by (intros [=]; lra).
  rewrite inner_product_adjoint_l.
  unfold deviation.
  now rewrite (hermitian_deviation_generalized A (⟨ x, A × x ⟩)); auto;
  [ rewrite <- Mmult_assoc
  | now apply hermitian_implies_real_inner_product
  ]; trivial.
Qed.

Theorem Heisenberg_Uncertainty_Principle : 
  forall {n : nat} (x : Vector n) (A B : Square n),
    WF_Matrix A -> WF_Matrix B -> hermitian A -> hermitian B ->
      (variance x A) * (variance x B) >= / 4 * fst (⟨x, -Ci .* commutator A B × x⟩)^2.
Proof.
  intros * WFA WFB HHermA HHermB.
  apply Rle_ge.
  rewrite !variance_norm_sq_eq; auto.
  generalize (Cauchy_Schwartz_ver1 (deviation x A × x) (deviation x B × x)).
  rewrite interm_Uncertainty_Principle; auto.
  apply Rle_trans, Rmult_le_compat_l; [lra | ].
  now rewrite Cmod_pow2_reals; try apply hermitian_implies_real_inner_product;
  [ rewrite <- Rplus_0_l at 1; apply Rplus_le_compat_r, pow2_ge_0
  | apply hermitian_deviation_anticommutator
  | apply hermitian_neg_i_commutator
  ]; trivial.
Qed.

Local Close Scope R_scope.

End sec_heisenberg.

