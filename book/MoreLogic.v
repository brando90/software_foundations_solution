(** * MoreLogic: More on Logic in Coq *)

Require Export "Prop".

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists)  *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* FILL IN HERE *)
(* SKIPPED *)

(*
*)
(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros X P Hforall.
  unfold not.
  intros Hexists.
  inversion Hexists as [x Hx].
  apply Hx. apply Hforall.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros Hexcluded_middle.
  intros X P HexistsFF x.
  remember (Hexcluded_middle (P x)) as HPxTF. clear HeqHPxTF.
  inversion HPxTF as [ HPxT | HPxF].
  Case "True". apply HPxT.
  Case "False". apply ex_falso_quodlibet. apply HexistsFF. 
  exists x. apply HPxF.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  Case "->". intros HePQ. inversion HePQ as [x HPQ].
  inversion HPQ as [ HP | HQ].
  SCase "HP". left. exists x. apply HP.
  SCase "HQ". right. exists x. apply HQ.
  Case "<-". intros HePeQ. inversion HePeQ as [ HeP | HeQ].
  SCase "HeP". inversion HeP as [x HP]. exists x. left. apply HP.
  SCase "HeQ". inversion HeQ as [x HQ]. exists x. right. apply HQ.
Qed.
(** [] *)

(* ###################################################### *)
(** * Evidence-Carrying Booleans *)

(** So far we've seen two different forms of equality predicates:
    [eq], which produces a [Prop], and the type-specific forms, like
    [beq_nat], that produce [boolean] values.  The former are more
    convenient to reason about, but we've relied on the latter to let
    us use equality tests in _computations_.  While it is
    straightforward to write lemmas (e.g. [beq_nat_true] and
    [beq_nat_false]) that connect the two forms, using these lemmas
    quickly gets tedious. *)

(** *** *)
(** It turns out that we can get the benefits of both forms at once by
    using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
    of its values being just [true] and [false], they carry _evidence_
    of truth or falsity. This means that when we [destruct] them, we
    are left with the relevant evidence as a hypothesis -- just as
    with [or].  (In fact, the definition of [sumbool] is almost the
    same as for [or].  The only difference is that values of [sumbool]
    are declared to be in [Set] rather than in [Prop]; this is a
    technical distinction that allows us to compute with them.) *)

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined.

(** Read as a theorem, this says that equality on [nat]s is decidable:
    that is, given two [nat] values, we can always produce either
    evidence that they are equal or evidence that they are not.  Read
    computationally, [eq_nat_dec] takes two [nat] values and returns a
    [sumbool] constructed with [left] if they are equal and [right] if
    they are not; this result can be tested with a [match] or, better,
    with an [if-then-else], just like a regular [boolean].  (Notice
    that we ended this proof with [Defined] rather than [Qed].  The
    only difference this makes is that the proof becomes
    _transparent_, meaning that its definition is available when Coq
    tries to do reductions, which is important for the computational
    interpretation.) *) 

(** *** *)
(** Here's a simple example illustrating the advantages of the
   [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the
    version of [override] defined using [beq_nat], where we had to use
    the auxiliary lemma [beq_nat_true] to convert a fact about
    booleans to a Prop. *)

(** **** Exercise: 1 star (override_shadow')  *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "left". reflexivity.
  Case "right". reflexivity.
(** [] *)





(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
| allnil : all P []
| allcons : forall h t, P h -> all P t -> all P (h::t)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem all_forallb_true : forall X (f : X -> bool) (l : list X),
    all (fun x => f x = true) l <-> forallb f l = true.
Proof.
  intros X f l. split.
  Case "->". intros Hall. induction l as [| h t].
  SCase "l = []". reflexivity.
  SCase "l = h::t". inversion Hall. simpl. rewrite H1. simpl. apply IHt. apply H2.
  Case "<-". intros Hforallbt. induction l as [| h t].
  SCase "l = []". apply allnil.
  SCase "l = h::t". inversion Hforallbt. destruct (f h) eqn:Hfh.
  SSCase "true". rewrite H0. apply allcons. apply Hfh. apply IHt. apply H0.
  SSCase "false". inversion H0.
Qed.

Theorem not_all_forallb_false : forall X (f : X -> bool) (l : list X),
    ~ (all (fun x => f x = true) l) <-> forallb f l = false.
Proof.
  intros X f l. split.
  Case "->". intros Hnotall. induction l as [| h t].
  SCase "l = []". apply ex_falso_quodlibet. apply Hnotall. apply allnil.
  SCase "l = h::t". simpl. destruct (f h) eqn:Hfh.
  SSCase "true".
  assert (~ all (fun x => f x = true) (h::t) -> ~ all (fun x => f x = true) t) as Hnotall2notall.
  SSSCase "Proof of assertion". apply contrapositive. apply allcons. apply Hfh.
  apply Hnotall2notall in Hnotall. apply IHt. apply Hnotall.
  SSCase "false". reflexivity.
  Case "<-". intros Hforallbf. induction l as [| h t].
  SCase "l = []". inversion Hforallbf.
  SCase "l = h::t". inversion Hforallbf. destruct (f h) eqn:Hfh.
  SSCase "true". unfold not. intros Hall. inversion Hall. apply IHt. apply H0. apply H3.
  SSCase "false". unfold not. intros. inversion H. rewrite Hfh in H3. inversion H3.
Qed.
  
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive inorderMerged {X : Type} : list X -> list X -> list X -> Prop :=
| ioMnil : inorderMerged [] [] []
| ioMcons1 : forall x l l1 l2, inorderMerged l l1 l2 -> inorderMerged (x::l) (x::l1) l2
| ioMcons2 : forall x l l1 l2, inorderMerged l l1 l2 -> inorderMerged (x::l) l1 (x::l2)
.

Theorem filter_spec : forall X (f : X -> bool) l l1 l2,
    inorderMerged l l1 l2 /\ all (fun x => f x = true) l1 /\ all (fun x => f x = false) l2 ->
    filter f l = l1.
Proof.
  intros X f l.
  induction l as [| h t].
  Case "l = []". intros l1 l2 Hspec.
  inversion Hspec as [HioM [Hall1 Hall2]]. inversion HioM. reflexivity.
  Case "l = h::t". intros l1 l2 Hspec.
  inversion Hspec as [HioM [Hall1 Hall2]]. simpl. destruct (f h) eqn:Hfh.
  SCase "true". inversion HioM.
  SSCase "ioMcons1". rewrite IHt with l0 l2. reflexivity. split.
  SSSCase "left". apply H3.
  SSSCase "right". split.
  SSSSCase "left". rewrite <- H0 in Hall1. inversion Hall1.
  SSSSSCase "allcons". apply H7.
  SSSSCase "right". apply Hall2.
  SSCase "ioMcons2". rewrite <- H2 in Hall2. inversion Hall2.
  SSSCase "allcons". rewrite H6 in Hfh. inversion Hfh.
  SCase "false". inversion HioM.
  SSCase "ioMcons1". rewrite <- H0 in Hall1. inversion Hall1.
  SSSCase "allcons". rewrite H6 in Hfh. inversion Hfh.
  SSCase "ioMcons2". rewrite IHt with l1 l3. reflexivity. split.
  SSSCase "left". apply H3.
  SSSCase "right". split.
  SSSSCase "left". apply Hall1.
  SSSSCase "right". rewrite <- H2 in Hall2. inversion Hall2.
  SSSSSCase "allcons". apply H7.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

Theorem filter_spec' : forall X (f : X -> bool) (l l0 : list X),
    subseq (filter f l) l /\ all (fun x => f x = true) (filter f l) /\
    (subseq l0 l /\ all (fun x => f x = true) l0 ->
     length l0 <= length (filter f l)).
Proof.
  intros X f l.
  induction l as [| h t].
  Case "l = []". intros l0. split.
  SCase "left". apply subnil.
  SCase "right". split.
  SSCase "left". apply allnil.
  SSCase "right". intros Hl0. inversion Hl0 as [Hl0sub Hl0all].
  destruct l0 as [| h0 t0].
  SSSCase "l0 = []". apply le_n.
  SSSCase "l0 = h0::t0". inversion Hl0sub.
  Case "l = h::t". intros l0. split.
  SCase "left". simpl. destruct (f h) eqn:Hfh.
  SSCase "true". apply subele. apply IHt. apply l0.
  SSCase "false". apply subskip. apply IHt. apply l0.
  SCase "right". split.
  SSCase "left". simpl. destruct (f h) eqn:Hfh.
  SSSCase "true". apply allcons. apply Hfh. apply IHt. apply l0.
  SSSCase "false". apply IHt. apply l0.
  SSCase "right". intros Hl0. inversion Hl0 as [Hl0sub Hl0all].
  destruct l0 as [| h0 t0].
  SSSCase "l0 = []". apply O_le_n.
  SSSCase "l0 = h::t". inversion Hl0sub.
  SSSSCase "subele". rewrite H2 in Hl0all. inversion Hl0all.
  SSSSSCase "allcons". simpl. rewrite H6. simpl.
  apply n_le_m__Sn_le_Sm. apply IHt. split.
  SSSSSSCase "left". apply H0.
  SSSSSSCase "right". apply H7.
  SSSSCase "subskip". apply le_trans with (length (filter f t)). apply IHt. split.
  SSSSSCase "left". apply H1.
  SSSSSCase "right". apply Hl0all.
  simpl. destruct (f h) eqn:Hfh.
  SSSSSCase "true". simpl. apply le_S. apply le_n.
  SSSSSCase "false". apply le_n.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs.
  induction xs as [| hx tx].
  Case "xs = []". intros ys x Happ. simpl in Happ. right. apply Happ.
  Case "xs = hx::tx". intros ys x Happ. simpl in Happ.
  inversion Happ.
  SCase "ai_here". left. apply ai_here.
  SCase "ai_later". apply IHtx in H0. inversion H0.
  SSCase "left". left. apply ai_later. apply H2.
  SSCase "right". right. apply H2.
Qed.
  
Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs.
  induction xs as [| hx tx].
  Case "xs = []". intros ys x Happor.
  inversion Happor.
  SCase "left". inversion H.
  SCase "right". apply H.
  Case "xs = hx::tx". intros ys x Happor.
  inversion Happor.
  SCase "left". inversion H.
  SSCase "ai_here". apply ai_here.
  SSCase "ai_later". simpl. apply ai_later. apply IHtx. left. apply H1.
  SCase "right". simpl. apply ai_later. apply IHtx. right. apply H.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
| disnil : disjoint nil nil
| discons1 : forall x l1 l2, ~ appears_in x l2 -> disjoint l1 l2 -> disjoint (x::l1) l2
| discons2 : forall x l1 l2, ~ appears_in x l1 -> disjoint l1 l2 -> disjoint l1 (x::l2)
.

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats {X : Type} : list X -> Prop :=
| nornil : no_repeats []
| norcons : forall x l, ~ appears_in x l -> no_repeats (x::l)
.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Lemma not_appears_in_app__not_appears_in : forall X (x : X) (l1 l2 : list X),
    ~ appears_in x l1 ->
    ~ appears_in x l2 ->
    ~ appears_in x (l1 ++ l2).
Proof.
  intros X x l1 l2 Hnotapp1 Hnotapp2.
  generalize dependent l2.
  induction l1 as [| h1 t1].
  Case "l1 = []". intros. apply Hnotapp2.
  Case "l1 = h1::t1". intros. unfold not. intros Happ. inversion Happ.
  SCase "ai_here". apply Hnotapp1. rewrite H0. apply ai_here.
  SCase "ai_later". revert H0. apply IHt1.
  unfold not. intros Happ1. apply Hnotapp1. apply ai_later. apply Happ1.
  apply Hnotapp2.
Qed.

Theorem no_repeats_disjoint_app__no_repeats : forall X (l1 l2 : list X),
    no_repeats l1 ->
    no_repeats l2 ->
    disjoint l1 l2 ->
    no_repeats (l1 ++ l2).
Proof.
  intros X l1 l2 Hnor1 Hnor2 Hdis.
  generalize dependent l2.
  induction l1 as [| h1 t1].
  Case "l1 = []". intros. apply Hnor2.
  Case "l1 = h1::t1". intros. inversion Hnor1.
  SCase "norcons". simpl. apply norcons.
  assert (forall (h : X) (t l0 : list X), disjoint (h::t) l0 -> ~ appears_in h l0).
  SSCase "Proof of assertion". intros h t l0 Hdis0. induction l0.
  SSSCase "l0 = []". unfold not. intros Happ. inversion Happ.
  SSSCase "l0 = h0::t0". unfold not. intros Happ. inversion Hdis0.
  SSSSCase "discons1". apply H4. apply Happ.
  SSSSCase "discons2". inversion Happ.
  SSSSSCase "ai_here". apply H5. rewrite H8. apply ai_here.
  SSSSSCase "ai_later". apply IHl0. apply H6. apply H8.
  apply H2 in Hdis. apply not_appears_in_app__not_appears_in. apply H0. apply Hdis.
Qed.
(** [] *)

(** **** Exercise: 3 stars (nostutter)  *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1;4;1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
| nostnil : nostutter []
| nostone : forall x, nostutter [x]
| nostcons : forall x y l, beq_nat x y = false -> nostutter (y::l) -> nostutter (x::y::l)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.


Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  inversion H1.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros X l1. induction l1 as [| h1 t1].
  Case "l1 = []". intros l2. reflexivity.
  Case "l1 = h1::t1". intros l2. simpl. rewrite IHt1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l Happ.
  induction l as [| h t].
  Case "l = []". inversion Happ.
  Case "l = h::t". inversion Happ.
  SCase "ai_here". exists []. exists t. reflexivity.
  SCase "ai_later". apply IHt in H0. inversion H0 as [l1 H2].
  inversion H2 as [l2 H3].
  exists (h::l1). exists l2. rewrite H3. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| repcons1 : forall x l, appears_in x l -> repeats (x::l)
| repcons2 : forall x l, repeats l -> repeats (x::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
   Case "l1 = []". intros l2 Hexcluded_middle HappTrans HLt.
   inversion HLt.
   Case "l1 = x::l1'". intros l2 Hexcluded_middle Happtrans HLt.
   assert (appears_in x l1' \/ ~ appears_in x l1') as Happl1'.
   SCase "Proof of assertion". apply Hexcluded_middle.
   inversion Happl1'.
   SCase "True". apply repcons1. apply H.
   SCase "False". apply repcons2.
   assert (appears_in x (x::l1')) as Happx.
   SSCase "Proof of assertion". apply ai_here.
   apply Happtrans in Happx. apply appears_in_app_split in Happx.
   inversion Happx as [l21 Happx0]. inversion Happx0 as [l22 Happx1].
   apply IHl1' with (l21 ++ l22).
   apply Hexcluded_middle.
   intros.
   assert ( x = x0 \/ ~ x = x0).
   SSCase "Proof of assertion". apply Hexcluded_middle.
   inversion H1.
   SSCase "=". rewrite H2 in H. apply ex_falso_quodlibet. apply H. apply H0.
   SSCase "<>". apply ai_later with (b:=x) in H0. apply Happtrans in H0.
   rewrite Happx1 in H0. apply appears_in_app in H0. apply app_appears_in.
   inversion H0.
   SSSCase "left". left. apply H3.
   SSSCase "right". inversion H3.
   SSSSCase "ai_here". apply ex_falso_quodlibet. apply H2. rewrite H5. reflexivity.
   SSSSCase "ai_later". right. apply H5.
   rewrite Happx1 in HLt. rewrite -> app_length in HLt. rewrite -> app_length.
   simpl in HLt. rewrite plus_comm in HLt. simpl in HLt. rewrite plus_comm.
   apply Sn_le_Sm__n_le_m. apply HLt.
Qed.
(** [] *)

Theorem pigeonhole_principle': forall (X:Type) (l1  l2:list X), 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
Abort.

(** $Date: 2014-12-31 16:01:37 -0500 (Wed, 31 Dec 2014) $ *)
