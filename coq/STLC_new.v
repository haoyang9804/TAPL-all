Inductive type : Type :=
  | B (*boolean*)
  | N (*nat*)
  .

Inductive term : Type :=
  | boolean (b : bool)
  | if_then_else (t1 t2 t3 : term) (* if t1 then t2 else t3 *)
  | zero
  | succ (t: term) 
  | iszero (t : term)
  | pred (t : term).

(* number value *)
Inductive nvalue : term -> Prop :=
  | NZero : nvalue zero
  | NSucc : forall (t:term), nvalue t -> nvalue (succ t).

Inductive value : term -> Prop :=
  | BValue : forall (t : term) (b : bool), t = boolean b -> value t
  | NValue : forall (t : term), nvalue t -> value t.

Inductive evaluate : term -> term -> Prop :=
  | E_SUCC :
    forall (t1 t2 : term),
    evaluate t1 t2 ->
    evaluate (succ t1) (succ t2)
  | E_PREDZERO :
    evaluate (pred zero) zero
  | E_PREDSUCC :
    forall (t : term),
    nvalue t ->
    evaluate (pred (succ t)) t
  | E_PRED :
    forall (t1 t2 : term),
    evaluate t1 t2 ->
    evaluate (pred t1) (pred t2)
  | E_ISZEROZERO :
    evaluate (iszero zero) (boolean true)
  | E_ISZEROSUCC :
    forall (t : term),
    nvalue t ->
    evaluate (iszero (succ t)) (boolean false)
  | E_ISZERO :
    forall (t1 t2 : term),
    evaluate t1 t2 ->
    evaluate (iszero t1) (iszero t2)
  | E_IFTRUE :
    forall (t2 t3 : term),
    evaluate (if_then_else (boolean true) t2 t3) t2
  | E_IFFALSE :
    forall (t2 t3 : term),
    evaluate (if_then_else (boolean false) t2 t3) t3
  | E_IF :
    forall (t1 t2 t3 t1' : term),
    evaluate t1 t1' ->
    evaluate (if_then_else t1 t2 t3) (if_then_else t1' t2 t3).

Inductive typeCheck : term -> type -> Prop :=
  | CheckTrue : typeCheck (boolean true) B
  | CheckFalse : typeCheck (boolean false) B
  | CheckIf (T:type) (t1 t2 t3 : term):
    typeCheck t1 B ->
    typeCheck t2 T ->
    typeCheck t3 T ->
    typeCheck (if_then_else t1 t2 t3) T
  | CheckZero : typeCheck zero N
  | CheckSucc :
    forall (t:term) t,
    typeCheck t N ->
    typeCheck (succ t) N
  | CheckPred :
    forall (t:term),
    typeCheck t N ->
    typeCheck (pred t) N
  | CheckIszero :
    forall (t:term),
    typeCheck t N ->
    typeCheck (iszero t) B.

(* A trick here *)
Lemma typeCheck_number_is_not_B:
forall t, nvalue t -> typeCheck t B -> False.
Proof.
  intros. 
  induction H; inversion H0. 
Qed.

(** [Canonical Form (Page 127) (1)] If [v] is a value of type [Bool],
then [v] is either [true] or [false]*)
Lemma boolvalue_only_contains_true_or_false :
forall (t:term), value t -> typeCheck t B -> t = boolean true \/ t = boolean false.
Proof.
  intros. remember t as t'. remember B as T. induction H0.
  - left. reflexivity.
  - right. reflexivity.
  - inversion H. discriminate. inversion H0.
  - discriminate.
  - discriminate.
  - discriminate.
  - inversion H.
    + discriminate.
    + inversion H1. 
Qed.

(* (** [Canonical Form (Page 128) (2)] If [v] is a value of type [Nat],
then [v] is a [number]*)
Lemma numvalue_only_contains_zero_or_succ :
forall (t:term), nvalue t -> t = zero \/ exists (t' : term), nvalue t' -> 
Proof.
  intros. remember N as type_. induction H0; try discriminate.
  - remember (if_then_else t1 t2 t3) as ifH. destruct H; rewrite HeqifH in H;
    discriminate.
  - exists zero; reflexivity.
  - exists (succ n); reflexivity.
  - remember (pred t) as predn.
    destruct H eqn:E.
    + rewrite e in Heqpredn; discriminate.
    + rewrite e. exists n; reflexivity. 
Qed. *)


(* [exists (tp : type), typeCheck t tp] means term [t] is well-typed *)
Theorem Progress : forall (t:term), (exists (tp : type), typeCheck t tp) -> 
  value t \/ (exists (t':term), evaluate t t').
Proof. 
  intros. destruct H. 
  induction H.
  - left. apply BValue with (b:=true). reflexivity.
  - left. apply BValue with (b:=false). reflexivity.
  - right.  
    destruct IHtypeCheck1.
    + inversion H2.
      -- destruct b; rewrite H3.
         ++ exists t2. apply E_IFTRUE.
         ++ exists t3. apply E_IFFALSE.
      -- inversion H3; inversion H.
         ++ rewrite <- H5 in H6; discriminate.
         ++ rewrite <- H5 in H6; discriminate.
         ++ rewrite <- H5 in H9; discriminate.
         ++ rewrite <- H5 in H7; discriminate.
         ++ rewrite <- H6 in H7; discriminate.
         ++ rewrite <- H6 in H7; discriminate.
         ++ rewrite <- H6 in H10; discriminate.
         ++ rewrite <- H6 in H8; discriminate.
    + destruct H2.
      exists (if_then_else x t2 t3).
      apply E_IF.
      apply H2.
  - left. apply NValue. apply NZero.
  - destruct IHtypeCheck.
    + left. apply NValue. inversion H0.
      -- rewrite H1 in H. inversion H.
      -- apply NSucc. apply H1.
    + destruct H0.
      right. exists (succ x).
      apply E_SUCC. apply H0.
  - right.
    destruct IHtypeCheck.
    + inversion H0.
      -- rewrite H1 in H. inversion H.
      -- destruct H1.
         ++ exists zero. apply E_PREDZERO.
         ++ exists t. apply E_PREDSUCC. apply H1.
    + destruct H0.
      exists (pred x).
      apply E_PRED.
      apply H0.
  - right. destruct IHtypeCheck.
    + inversion H0.
      -- rewrite H1 in H. inversion H.
      -- destruct H1.
         ++ exists (boolean true). apply E_ISZEROZERO.
         ++ exists (boolean false). apply E_ISZEROSUCC. apply H1.
    + destruct H0.
      exists (iszero x).
      apply E_ISZERO.
      apply H0.
Qed. 

(* Lemma evaluate_B_is_B :
forall (t1 t2 : term), typeCheck t1 B -> evaluate t1 t2 -> typeCheck t2 B.
Proof.
  intros. remember B as B'. induction H.
  - inversion H0.
  - inversion H0.
  - inversion H0. 
    + rewrite <- H3. apply H1.
    + rewrite <- H3. apply H2.
    + apply IHtypeCheck2 IN
  
  inversion H.
  - rewrite <- H1 in H0. inversion H0.
  - rewrite <- H1 in H0. inversion H0.
  -   
Qed. *)

(* Lemma if_B_evaluate_B :
forall (t1 t2 t3 t':term), typeCheck t1 B -> typeCheck t2 B -> typeCheck t3 B -> evaluate (if_then_else t1 t2 t3) t' -> typeCheck t' B.
Proof.
  intros. 
  inversion H2.
  - rewrite <- H3. apply H0.
  - rewrite <- H3. apply H1.
  - 
  
  remember (if_then_else t1 t2 t3) as if_. induction H2; try discriminate.
  - injection Heqif_; intros. rewrite H3. apply H0.
  - injection Heqif_; intros. rewrite H2. apply H1.
  - injection Heqif_; intros. rewrite H3. rewrite H4. rewrite H5 in H2. rewrite H5 in IHevaluate.
    clear H3. clear H4. clear H5. clear Heqif_.

Qed. *)


(** If [t] : [T] and [t] -> [t'], then [t'] : [T]*)
Theorem Preservation :
forall (t t':term) (T:type), typeCheck t T -> evaluate t t' -> typeCheck t' T.
Proof. (* induction on type system , could also do induction on evaluation*)
  intros. generalize dependent t'.
  induction H; intros.
  - inversion H0. (* cannot evaluate (boolean true)*)
  - inversion H0. (* cannot evaluate (boolean false)*)
  - remember B as B'. destruct H.
    + inversion H2.
      -- rewrite <- H5. apply H0.
      -- inversion H6.
    + inversion H2.
      -- rewrite <- H5. apply H1.
      -- inversion H6.
    + rewrite HeqB' in H3;
      rewrite HeqB' in H4;
      clear HeqB'.
      inversion H2.
      apply CheckIf.
      -- inversion H9.
         ++ rewrite <- H11 in H9. inversion_clear H9. 
            --- rewrite <- H10. apply H3.
            --- inversion H14.
         ++ rewrite <- H11 in H9. inversion_clear H9.
            --- rewrite <- H10. apply H4.
            --- inversion H14.
         ++ assert (H__: typeCheck (if_then_else t1'0 t0 t4) B) by admit. apply H__.
      --  
            
Qed.
