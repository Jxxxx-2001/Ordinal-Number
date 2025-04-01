Require Export MK_Theorems1.

(**********************************************************************)
(* 序数相关性质定理 *)

Lemma Less_eq_E : ∀ a b, Ensemble b -> Rrelation a E b <-> a ≺ b.
Proof.
  split; intros.
  - red in H0. appA2H H0. destruct H1,H1,H1.
    apply MKT55 in H1; ope. destruct H1. subst; auto.
  - red. appA2G.
Qed.

Lemma trans_Ord_Num : ∀a b, Ordinal_Number a -> b ≺ a -> Ordinal_Number b.
Proof.
  intros. red in H. New MKT113a. destruct H1 as [_ H3].
  apply H3 in H. apply H in H0. auto.
Qed.

(* transitivity *)
Theorem Ord_Num_trans : ∀a b c, Ordinal_Number c
  -> a ≺ b -> b ≺ c -> a ≺ c.
Proof.
  intros. New MKT113a. apply @ MKT107 in H2. apply MKT88b in H2.
  red in H2. specialize H2 with a b c. New H1.
  eapply trans_Ord_Num in H3; eauto. New H0. eapply trans_Ord_Num in H4; eauto.
  eapply (Less_eq_E a c); eauto; eapply H2; eauto;
  try eapply Less_eq_E; eauto.
Qed.

(* antisymmetry *)
Theorem Ord_Num_antisym : ∀ a b, Ordinal_Number a -> Ordinal_Number b
  -> a ≺ b -> ~ (b ≺ a).
Proof.
  intros. red in H1. red. unfold Less. eapply MKT102; eauto.
Qed.

(* trichotomy *)
Theorem Ord_Num_tri : ∀ a b, Ordinal_Number a -> Ordinal_Number b
  -> a ≺ b \/ a = b \/ b ≺ a.
Proof.
  intros. unfold Less. New H. appA2H H. appA2H H0.
  eapply (Lemma113 a b) in H; eauto.
  repeat destruct H; auto. eapply (Less_eq_E a b) in H; eauto.
  eapply (Less_eq_E b a) in H; eauto.
Qed.

(* non-density *)
Theorem Ord_Num_not_dense : ∀ a b, Ordinal_Number a -> Ordinal_Number b ->
  a ≺ b -> ~ (b ≺ PlusOne a).
Proof.
  intros. New H. apply MKT123 in H2. destruct H2.
  specialize H3 with b. red. intros. elim H3. appA2G. red. appA2G.
  eapply MKT49a. red in H0. appA2H H0. auto. appA2H H2; auto.
Qed.

(**********************************************************************)

(* 定义 后继序数 *)
Definition Suc_Ord a: Prop :=∃ x, Ordinal_Number x /\ a = PlusOne x.

(* 定义 极限序数 *)
Definition Lim_Ord a: Prop := Ordinal_Number a /\ ~(Suc_Ord a).


(**********************************************************************)
(* 序数定义相关Fact *)

Lemma uni_Suc_Lim : ∀a, Ordinal_Number a -> Suc_Ord a <-> ~ Lim_Ord a.
Proof.
  split; intros. red. intros. destruct H1. auto.
  unfold Lim_Ord in H0. apply notandor in H0. destruct H0.
  contradiction. apply NNPP. auto.
Qed.

Lemma OrdNum_classic : ∀a, Ordinal_Number a -> Suc_Ord a \/ Lim_Ord a.
Proof.
  intros. TF (Suc_Ord a). left. auto. right. red. auto.
Qed.

Ltac Suc_not_Lim :=
  match goal with
    H1: Lim_Ord ?x,
    H2: Suc_Ord ?x
    |- _ => eapply uni_Suc_Lim in H2; eauto; contradiction
  end.

(* Φ *)
Lemma Φ_is_Ord : Ordinal_Number Φ.
Proof.
  red. appA2G.
  split; red; intros. New (@ MKT16 u). contradiction. emf.
Qed.

Lemma Φ_is_Lim_Ord : Lim_Ord Φ.
Proof.
  split. apply Φ_is_Ord. red. intros. red in H. destruct H,H.
  assert( x ∈ PlusOne x ). { appA2G. } rewrite <- H0 in H1.
  New @ MKT16. specialize H2 with x. contradiction.
Qed.

Lemma Φ_is_First_Ord : ∀ a, Ordinal_Number a -> a <> Φ -> Φ ≺ a.
Proof.
  intros. New Φ_is_Ord. New H. eapply (Ord_Num_tri a Φ) in H2; eauto.
  try repeat (destruct H2; auto). eapply MKT16 in H2. destruct H2.
  elim H0. auto.
Qed.

(* Suc_Ord *)
Lemma Suc_is_Ord : ∀a, Suc_Ord a -> Ordinal_Number a.
Proof.
  intros. destruct H,H. red in H. apply Lem123 in H. red. subst. auto.
Qed.

(* Lim_Ord *)
Lemma Lim_Ord_1 : ∀a, Ordinal_Number a -> Lim_Ord a
  <-> (∀ b, b ≺ a -> PlusOne b ≺ a).
Proof.
  split; intros.
  - New H1. apply trans_Ord_Num in H2; auto. New H2.
    eapply Lem123 in H3; eauto. New H3.
    eapply (Ord_Num_tri (PlusOne b) a) in H3; eauto.
    destruct H3; auto. destruct H3. destruct H0. elim H5.
    red. exists b; split; auto.
    eapply Ord_Num_not_dense in H1; eauto. contradiction.
  - red. split; auto. red. intros. destruct H1,H1.
    assert( x ≺ a ). rewrite H2; appA2G.
    apply H0 in H3. rewrite H2 in H3. eapply MKT101; eauto.
Qed.

(**********************************************************************)
(* 关于序数的超限归纳法 *)

Theorem R_Transfinite_Induction : ∀ (P :Class -> Prop) ,
  ( ∀ a, a ∈ R -> ( ∀ b, b ∈ a -> P b ) -> P a )
  -> ( ∀ x, x ∈ R -> P x ).
Proof.
  intros. apply NNPP. red. intros.
  set ( B := \{ λ b, b ∈ R /\ ~ P b \} ).
  assert( B ⊂ R ). { red. intros. appA2H H2. apply H3. }
  TF ( B = Φ ). assert( x ∈ B ). appA2G.
  rewrite H3 in H4. emf.
  eapply Lemma121 in H2 as []; eauto.
  appA2H H2. destruct H5. eapply H in H5; eauto.
  intros. TF ( b ∈ B ). apply H4 in H8.
  unfold Rrelation in H8. elim H8. appA2G.
  apply NNPP. red. intros. elim H8. appA2G.
  split; auto. New MKT113a. destruct H10 as [_ H10].
  apply H10 in H5; auto.
Qed.

Theorem The_Second_R_Transfinite_Induction : ∀ (P: Class -> Prop), P Φ
  -> (∀ a, Suc_Ord (PlusOne a) -> P a -> P (PlusOne a))
  -> (∀ a, Lim_Ord a -> a ≠ Φ -> (∀ b, b ≺ a -> P b) -> P a)
  -> (∀ x, x ∈ R -> P x).
Proof.
  intros. eapply (R_Transfinite_Induction P); eauto. intros.
  TF(a = Φ). subst; auto.
  New H3. apply OrdNum_classic in H6 as [].
  - destruct H6,H6. rewrite H7. eapply H0; eauto. exists x0; eauto.
    eapply H4; eauto. rewrite H7; appA2G.
  - eapply H1; eauto.
Qed.

Theorem The_Second_R_Transfinite_Induction' : ∀ (P: Class -> Prop), P Φ
  -> (∀ a, a ∈ R -> P a -> P (PlusOne a))
  -> (∀ a, Lim_Ord a -> (∀ b, b ≺ a -> P b) -> P a)
  -> (∀ a, a ∈ R -> P a).
Proof.
  intros. eapply (R_Transfinite_Induction P); eauto. intros.
  TF(a0 = Φ). subst; auto.
  New H3. apply OrdNum_classic in H6 as [].
  - destruct H6,H6. apply H0 in H6. rewrite H7; auto.
    apply H4. rewrite H7. appA2G.
  - eapply H1; eauto.
Qed.

(* 关于自然数的超限归纳法 *)
Theorem ω_Transfinite_Induction : ∀ (P :Class -> Prop) ,
  ( ∀ a, a ∈ ω -> ( ∀ x, x ∈ a -> P x ) -> P a )
  -> ( ∀ y, y ∈ ω -> P y ).
Proof.
  intros. apply NNPP. red. intros.
  set ( B := \{ λ x, x ∈ ω /\ ~ P x \} ).
  assert( B ⊂ ω ). { red. intros. appA2H H2. apply H3. }
  TF ( B = Φ ). assert( y ∈ B ). appA2G.
  rewrite H3 in H4. emf. New MKT138. appA2H H4. New H5.
  apply MKT107 in H6. New H6. destruct H7 as [_ H7].
  eapply H7 in H2 as []; eauto. destruct H2.
  appA2H H2. destruct H9. eapply H in H9; eauto.
  intros. TF ( x0 ∈ B ). apply H8 in H12.
  unfold Rrelation in H12. elim H12. appA2G.
  apply NNPP. red. intros. elim H12. appA2G.
  split; auto. destruct H5 as [_ H5]. apply H5 in H9; auto.
Qed.

Check Mathematical_Induction.
(* ∀ (P :Class -> Prop), P Φ
  -> (∀ k, k ∈ ω -> P k -> P (PlusOne k))
  -> (∀ n, n ∈ ω -> P n).
Proof. *)


(**********************************************************************)

(* ω *)
Lemma ω_Num_is_Suc_Ord : ∀ a, a ∈ ω -> a <> Φ -> Suc_Ord a.
Proof.
  intros. assert(∀ x, x ∈ ω -> x = Φ \/ ∃ v, v ∈ ω /\ x = PlusOne v).
  apply Mathematical_Induction; eauto.
  eapply H1 in H; eauto. destruct H. contradiction.
  destruct H,H. red. exists x. split; eauto. New MKT138.
  eapply (trans_Ord_Num ω x) in H3; eauto.
Qed.

Lemma ω_is_Lim_Ord : Lim_Ord ω.
Proof.
  red. split. eapply MKT138. red. intros. destruct H.
  destruct H. assert( x ∈ ω ). rewrite H0; appA2G.
  eapply MKT134 in H1. rewrite H0 in H1. eapply MKT101; eauto.
Qed.

Lemma ω_is_first_Lim_Ord : ∀ a, a <> Φ -> a ≺ ω -> ~ Lim_Ord a.
Proof.
  intros. assert(∀ x, x ∈ ω -> x = Φ \/ ∃ v, v ∈ ω /\ x = PlusOne v).
  apply Mathematical_Induction; eauto.
  eapply H1 in H0. destruct H0. contradiction.
  red. intros. destruct H2. elim H3. destruct H0,H0. exists x.
  split; auto. eapply trans_Ord_Num; eauto. rewrite H4; appA2G.
Qed.

