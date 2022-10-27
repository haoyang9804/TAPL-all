Inductive type : Type :=
  | B (*boolean*)
  | N (*nat*)
  .

Inductive num : Type :=
  | zero
  | succ (n : num).

Inductive term : Type :=
  | boolean (b : bool)
  | if_then_else (t1 t2 t3 : term) (* if t1 then t2 else t3 *)
  | number (n : num)
  | iszero (t : term)
  | pred (t : term).

Inductive evaluate : term -> term -> Prop :=
  (** do not require [E_SUCC]: if t->t', then succ t -> succ t' here
    since succ only accepts num value and no evaluation rule for
    num exists. In other words, our language does not support
    [succ (if_then_else true zero (succ zero))]*)
  | E_PREDZERO :
    evaluate (pred (number zero)) (number zero)
  | E_PREDSUCC :
    forall (n : num),
    evaluate (pred (number (succ n))) (number n)
  | E_PRED :
    forall (t1 t2 : term),
    evaluate t1 t2 ->
    evaluate (pred t1) (pred t2)
  | E_ISZEROZERO :
    evaluate (iszero (number zero)) (boolean true)
  | E_ISZEROSUCC :
    forall (n:num),
    evaluate (iszero (number (succ n))) (boolean false)
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

Inductive value : term -> Prop :=
  | BValue : forall (t : term) (b : bool), t = boolean b -> value t
  | NValue : forall (t : term) (n : num), t = number n -> value t.

Inductive typeCheck : term -> type -> Prop :=
  | CheckTrue : typeCheck (boolean true) B
  | CheckFalse : typeCheck (boolean false) B
  | CheckIf (T:type) (t1 t2 t3 : term):
    typeCheck t1 B ->
    typeCheck t2 T ->
    typeCheck t3 T ->
    typeCheck (if_then_else t1 t2 t3) T
  | CheckZero : typeCheck (number zero) N
  | CheckSucc :
    forall (t:term) (n:num),
    typeCheck t N ->
    t = number n ->
    typeCheck (number (succ n)) N
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
forall (n : num), typeCheck (number n) B -> False.
Proof.
  intros. 
  remember (number n) as t.
  (*I need to remember B. Otherwise B will disappear*)
  remember B as type_.
  induction H; try discriminate. 
Qed.

(** [Canonical Form (Page 127) (1)] If [v] is a value of type [Bool],
then [v] is either [true] or [false]*)
Lemma boolvalue_only_contains_true_or_false :
forall (t:term), value t -> typeCheck t B -> t = boolean true \/ t = boolean false.
Proof.
  intros. induction t eqn:E.
  - destruct b. left; reflexivity. right; reflexivity.
  - rewrite <- E in H. destruct H eqn:E'; rewrite e in E; discriminate.
  - rewrite <- E in H0. rewrite E in H0. apply typeCheck_number_is_not_B in H0.
    contradiction.
  - destruct H eqn:E'. destruct b eqn:E''. left. apply e. right. apply e. 
    rewrite e in H0. apply typeCheck_number_is_not_B in H0. contradiction.
  - remember (pred t0) as predn.
    destruct H eqn:E'. destruct b; rewrite e. left; reflexivity. right; reflexivity.
    rewrite e in Heqpredn. discriminate.
Qed.

(** [Canonical Form (Page 128) (2)] If [v] is a value of type [Nat],
then [v] is a [number]*)
Lemma numvalue_only_contains_zero_of_succ :
forall (t:term),  value t -> typeCheck t N -> exists (n:num), t = number n.
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
Qed.

(* [exists (tp : type), typeCheck t tp] means term [t] is well-typed *)
Theorem Progress : forall (t:term), (exists (tp : type), typeCheck t tp) -> 
  value t \/ (exists (t':term), evaluate t t').
Proof. 
  intros. destruct H. induction H.
  - left. apply BValue with (b:=true); reflexivity.
  - left. apply BValue with (b:=false); reflexivity.
  - right. destruct IHtypeCheck1.
    + apply boolvalue_only_contains_true_or_false in H2.
      destruct H2. 
      -- exists t2. rewrite H2. apply E_IFTRUE.
      -- exists t3. rewrite H2. apply E_IFFALSE.
      -- apply H.
    + destruct H2. apply E_IF with (t2:=t2) (t3:=t3) in H2.
      exists (if_then_else x t2 t3). apply H2.
  - left. apply NValue with (n:=zero). reflexivity.
  - left. apply NValue with (n:=succ n). reflexivity.
  - right.
    destruct IHtypeCheck.
    + apply numvalue_only_contains_zero_of_succ in H.
      -- destruct H. destruct x eqn:Ex.
         ++ rewrite H. exists (number zero).
            apply E_PREDZERO.
         ++ rewrite H. exists (number n).
            apply E_PREDSUCC.
      -- apply H0.
    + destruct H0. exists (pred x).
      apply E_PRED. apply H0.
  - destruct IHtypeCheck.
    + destruct H0.
      -- apply numvalue_only_contains_zero_of_succ in H.
         destruct H. rewrite H in H0. discriminate.
         rewrite H0. apply BValue with (b:=b). reflexivity.
      -- destruct n eqn:En.
         ++ right. rewrite H0. exists (boolean true).
            apply E_ISZEROZERO.
         ++ right. rewrite H0. exists (boolean false).
            apply E_ISZEROSUCC.
    + destruct H0. right. exists (iszero x). apply E_ISZERO.
      apply H0.
Qed.

Axiom pred_succ_is_itself:
forall (n:num), pred (number (succ n)) = number n.

(** If [t] : [T] and [t] -> [t'], then [t'] : [T]*)
Theorem Preservation :
forall (t t':term) (T:type), typeCheck t T -> evaluate t t' -> typeCheck t' T.
Proof. (* induction on type system , could also do induction on evaluation*)
  intros. generalize dependent t'. induction H.
  - remember (boolean true) as btrue. intros.
    induction H0; try discriminate.
  - remember (boolean false) as bfalse. intros.
    induction H0; try discriminate.
  - remember (if_then_else t1 t2 t3) as ifH. 
    intros. destruct H2; try discriminate.
    + injection HeqifH; intros. rewrite H3. apply H0.
    + injection HeqifH; intros. rewrite H2. apply H1.
    + injection HeqifH; intros. rewrite H3. rewrite H4. 
      clear HeqifH. clear H3. clear H4. rewrite H5 in H2. clear H5.
      apply CheckIf.
      apply IHtypeCheck1 in H2. apply H2.
      apply H0.
      apply H1.
  - intros. remember (number zero) as Hzero. destruct H0; try discriminate.
  - intros. remember (number (succ n)) as Hsucc.
    destruct H1; try discriminate. 
  - intros. remember (pred t) as Hpredt.
    destruct H0; try discriminate.
    + apply CheckZero.
    + injection HeqHpredt; intros; clear HeqHpredt; rewrite <- H0 in IHtypeCheck;
      rewrite <- H0 in H. rewrite <- pred_succ_is_itself.
      apply CheckPred. apply H.
    + injection HeqHpredt; intros. rewrite H1 in H0. clear H1. clear HeqHpredt.
      apply IHtypeCheck in H0. apply CheckPred. apply H0.
  - intros. remember (iszero t) as Hiszero.
    destruct H0; try discriminate.
    + apply CheckTrue.
    + apply CheckFalse.
    + injection HeqHiszero; intros. rewrite H1 in H0. clear HeqHiszero. clear H1.
      apply IHtypeCheck in H0. apply CheckIszero. apply H0.
Qed.


