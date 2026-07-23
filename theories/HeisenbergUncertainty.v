From QuantumLib Require Import Quantum Complex Eigenvectors CauchySchwarz.

Section sec_heisenberg.

Local Open Scope R_scope.

(** Basic definitions *)

(* The expected value of observing A repeatedly on the same state x *)
Definition expectedval {n : nat} (x : Vector n) (A : Square n) : C := 
  ⟨x, A × x⟩.
   
(* Δ(x,A) = A - ⟨x, A × x⟩ * I *)
Definition deviation {n : nat} (x : Vector n) (A : Square n) : Square n := 
  A .+ -1 * ⟨x, A × x⟩ .* I n.

(* The expected value of the deviation squared *)
(* Var(x, A) = expectedval (Δ(x,A))² = ⟨x, (A - ⟨x, A × x⟩ * I)² × x⟩*)
Definition variance {n : nat} (x : Vector n) (A : Square n) : C := 
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

(* A number being equal to its complex conjugate implies it is purely imaginary *)
Theorem Cconj_eq_neg_implies_imaginary :
  forall (r : C), r ^* = Copp r -> fst r = 0.
Proof.
  intros [a b] HCconjneq.
  unfold Cconj in *.
  simpl in *.
  apply (f_equal fst) in HCconjneq.
  simpl in *.
  now lra.
Qed.

Theorem Cmult_real_fst_distributivity : forall (r q : C), snd r = 0 -> snd q = 0 -> fst r * fst q = fst (Cmult r q).
Proof.
  intros * Hrreal Hqreal.
  unfold Cmult.
  autorewrite with R_db.
  f_equal.
  simpl.
  nra.
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
  apply (scale_hermitian).
  - now simpl; lra.
  - now apply I_hermitian.
Qed.

(* The expected value of an antihermitian operator is purely imaginary *)
Theorem antihermitian_expectedval_imaginary :
  forall {n : nat} (x : Vector n) (A : Square n),
  A† = -C1 .* A -> fst ⟨x, A × x⟩ = 0.
Proof.
  intros * Hantiherm.
  apply Cconj_eq_neg_implies_imaginary.
  rewrite <- inner_product_conj_sym, inner_product_adjoint_l,
    Hantiherm, Mscale_mult_dist_l, inner_product_scale_r.
  ring.
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
    !Mplus_adjoint, !Mmult_adjoint, Mscale_plus_distr_r, Mscale_adj,
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
    variance x A = ⟨deviation x A × x, deviation x A × x⟩.
Proof.
  intros.
  unfold variance, deviation, expectedval, Mmult_n.
  rewrite Mmult_1_r, Mmult_assoc; auto with wf_db.
  rewrite inner_product_adjoint_switch.
  rewrite (hermitian_deviation_generalized A); try auto.
  now apply hermitian_implies_real_inner_product.
Qed.

Lemma commutator_deviation_var_eq :
  forall {n : nat} (x : Vector n) (A B : Square n),
    WF_Matrix A -> WF_Matrix B ->
      commutator (deviation x A) (deviation x B) = commutator A B.
Proof.
  intros.
  unfold commutator, deviation.
  rewrite 
    !Mmult_plus_distr_r, !Mmult_plus_distr_l,
    !Mscale_plus_distr_r, !Mmult_plus_distr_r, 
    !Mscale_assoc, !Mscale_mult_dist_r, 
    <- !Mplus_assoc, !Mscale_mult_dist_l, 
    !Mmult_1_r, !Mmult_1_l; auto with wf_db.
  prep_matrix_equality.
  now lca.
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
  rewrite <- Rpow_mult_distr, <- Cmod_mult, <- inner_product_scale_r.
  rewrite 
    <- Mscale_mult_dist_l, Mscale_assoc, Cinv_l, Mscale_1_l 
    by (intros [=]; lra).
  rewrite inner_product_adjoint_l.
  unfold deviation.
  rewrite (hermitian_deviation_generalized A (⟨ x, A × x ⟩)); auto.
  - now rewrite <- Mmult_assoc.
  - now apply hermitian_implies_real_inner_product.
Qed.

Theorem imaginary_commutator_expectedval_sq_eq_Cmod_expectedval_sq :
  forall {n : nat} (x : Vector n) (A B : Square n),
    WF_Matrix A -> WF_Matrix B -> hermitian A -> hermitian B ->
      fst ⟨x, -Ci .* commutator A B × x⟩^2 = Cmod ⟨x, commutator A B × x⟩^2.
Proof.
  intros * WFA WFB HHermA HHermB.
  unfold Cmod.
  assert (fst ⟨ x, commutator A B × x ⟩ = 0) as Himag.
  {
    rewrite antihermitian_expectedval_imaginary; try auto.
    unfold commutator.
    unfold hermitian in HHermA, HHermB.
    rewrite Mscale_plus_distr_r, Mplus_adjoint, <- !Mscale_mult_dist_l,
      !Mmult_adjoint, !HHermA, !HHermB, !Mscale_adj.
    autorewrite with C_db.
    rewrite !HHermB, Mscale_mult_dist_r, Mplus_comm.
    f_equal; [now rewrite Mscale_mult_dist_l |].
    rewrite Mscale_assoc.
    autorewrite with C_db.
    now rewrite Mscale_1_l.
  }
  rewrite Himag.
  simpl.
  rewrite Rmult_0_l, Rplus_0_l, !Rmult_1_r,
    Mscale_mult_dist_l, inner_product_scale_r.
  autorewrite with C_db.
  destruct (⟨ x, commutator A B × x ⟩).
  simpl in *.
  autorewrite with R_db.
  rewrite sqrt_sqrt; auto.
  now nra.
Qed.

Local Open Scope C_scope.

Theorem Heisenberg_Uncertainty_Principle : 
  forall {n : nat} (x : Vector n) (A B : Square n),
    WF_Matrix A -> WF_Matrix B -> hermitian A -> hermitian B ->
      fst ((variance x A) * (variance x B)) >= / 4 * (Cmod ⟨x, commutator A B × x⟩)^2.
Proof.
  intros * WFA WFB HHermA HHermB.
  apply Rle_ge.
  rewrite !variance_norm_sq_eq; auto.
  generalize (Cauchy_Schwartz_ver1 (deviation x A × x) (deviation x B × x)).
  rewrite interm_Uncertainty_Principle; auto.
  rewrite Cmult_real_fst_distributivity; try now rewrite norm_real.
  apply Rle_trans, Rmult_le_compat_l; [lra | ].
  unfold Cmod at 2.
  simpl snd.
  rewrite hermitian_implies_real_inner_product by 
    now apply hermitian_deviation_anticommutator.
  rewrite hermitian_implies_real_inner_product by
    now apply hermitian_neg_i_commutator.
  autorewrite with R_db.
  rewrite <- imaginary_commutator_expectedval_sq_eq_Cmod_expectedval_sq
    by auto.
  rewrite <- Rplus_0_l at 1. 
  rewrite pow2_sqrt.
  apply Rplus_le_compat_r, pow2_ge_0.
  apply Rplus_le_le_0_compat; rewrite <- Rsqr_pow2; apply Rle_0_sqr.
Qed.

Local Close Scope C_scope.

Local Close Scope R_scope.

End sec_heisenberg.

