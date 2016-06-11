(** * Prop: Propositions and Evidence *)

Require Export Logic.

(* ####################################################### *)
(** * Inductively Defined Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** The first line declares that [ev] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    even" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  

    The last two lines declare the two ways to give evidence that a
    number [m] is even.  First, [0] is even, and [ev_0] is evidence
    for this.  Second, if [m = S (S n)] for some [n] and we can give
    evidence [e] that [n] is even, then [m] is also even, and [ev_SS n
    e] is the evidence.
*)


(** **** Exercise: 1 star (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros n.
  induction n as [| n0].
  Case "n = 0". simpl. apply ev_0.
  Case "n = S n0". simpl. apply ev_SS. apply IHn0.
Qed.
(** [] *)



(* ##################################################### *)

(** For [ev], we had already defined [even] as a function (returning a
   boolean), and then defined an inductive relation that agreed with
   it. However, we don't necessarily need to think about propositions
   first as boolean functions, we can start off with the inductive
   definition.
*)

(** As another example of an inductively defined proposition, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)
(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion holds unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty)  *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(** Infinitely many, because there is 0, who is the identity of addtion. *)
(** [] *)

(* ####################################################### *)
(** ** Constructing Evidence *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(** 
    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercise: 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n Hb. simpl.
  rewrite plus_0_r.
  apply b_sum with (n:=n) (m:=n).
  apply Hb. apply Hb.
Qed.
(** [] *)

(** **** Exercise: 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m Hb.
  induction m as [| m0].
  Case "m = 0". apply b_0.
  Case "m = S m0". apply b_sum with (n:=n) (m:=m0*n).
  apply Hb. apply IHm0.
Qed.
(** [] *)


(* ####################################################### *)
(** * Using Evidence in Proofs *)
(** ** Induction over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)

(** *** *)    
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree)  *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(* FILL IN HERE *)
[]
(* SKIPPED *)
*)


(** **** Exercise: 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n Hg.
  apply g_plus3. apply g_plus5. apply g_plus5.
  apply Hg.
Qed.
(** [] *)

(** *** *)
(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)


Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)


(** *** *)

(** Let's see what happens if we try to prove this by induction on the evidence [H]
   instead of on [n]. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.


(* These exercises also require the use of induction on the evidence. *)

(** **** Exercise: 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Hg1 Hg2.
  generalize dependent m.
  induction Hg1.
  Case "g_0". intros. simpl. apply Hg2.
  Case "g_plus3". intros. rewrite <- plus_assoc. apply g_plus3. apply IHHg1. apply Hg2.
  Case "g_plus5". intros. rewrite <- plus_assoc. apply g_plus5. apply IHHg1. apply Hg2.
Qed.
 (** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros.
  induction H.
  Case "b_0". apply g_0.
  Case "b_3". apply g_plus3. apply g_0.
  Case "b_5". apply g_plus5. apply g_0.
  Case "b_sum". apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
(** [] *)




(** **** Exercise: 3 stars, optional (g_times2)  *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
  intros.
  rewrite plus_assoc.
  replace (x + z) with (z + x). reflexivity.
  apply plus_comm.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   Case "g_0". apply g_0.
   Case "g_plus3". rewrite <- plus_assoc. apply g_plus3. rewrite helper_g_times2.
   rewrite <- plus_assoc. rewrite <- plus_assoc. apply g_plus3. apply IHgorgeous.
   Case "g_plus5". rewrite <- plus_assoc. apply g_plus5. rewrite helper_g_times2.
   rewrite <- plus_assoc. rewrite <- plus_assoc. apply g_plus5. apply IHgorgeous.
Qed.
(** [] *)



(** Here is a proof that the inductive definition of evenness implies
the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(** **** Exercise: 1 star (ev__even)  *) 
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* Cannot *)

(** [] *)

(** Intuitively, the induction principle [ev n] evidence [ev n] is
    similar to induction on [n], but restricts our attention to only
    those numbers for which evidence [ev n] could be generated. *)

(** **** Exercise: 1 star (l_fails)  *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* FILL IN HERE *)
*)
(** [] *)

(** Here's another exercise requiring induction on evidence. *)
(** **** Exercise: 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros.
  induction H.
  Case "ev_0". apply H0.
  Case "ev_SS". simpl. apply ev_SS. apply IHev.
Qed.
(** [] *)



(* ####################################################### *)
(** ** Inversion on Evidence *)


(** Having evidence for a proposition is useful while proving, because we 
   can _look_ at that evidence for more information. For example, consider 
    proving that, if [n] is even, then [pred (pred n)] is
    too.  In this case, we don't need to do an inductive proof.  Instead 
    the [inversion] tactic provides all of the information that we need.

 *)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n)  *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* Cannot prove *)
(** [] *)

(** *** *)
(** Here is another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** The Inversion Tactic Revisited *)

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H. inversion H1. apply H3.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H. inversion H1. inversion H3.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0.
  Case "ev_0". simpl in H. apply H.
  Case "ev_SS". simpl in H. inversion H. apply IHev. apply H2.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros. apply ev_ev__ev with (n + n).
  rewrite <- plus_assoc.
  replace (n + (m + p)) with (m + (n + p)).
  rewrite plus_assoc.
  apply ev_sum. apply H. apply H0.
  rewrite plus_assoc. rewrite helper_g_times2. reflexivity.
  assert (forall n0, ev (n0 + n0)).
  intros. induction n0 as [| n1].
  Case "n0 = 0". apply ev_0.
  Case "n0 = S n1". simpl. rewrite plus_comm.
  simpl. apply ev_SS. apply IHn1.
  apply H1.
Qed.
(** [] *)


(* ####################################################### *)
(** * Discussion and Variations *)
(** ** Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(* ####################################################### *)
(** ** Parameterized Data Structures *)

(** So far, we have only looked at propositions about natural numbers. However, 
   we can define inductive predicates about any type of data. For example, 
   suppose we would like to characterize lists of _even_ length. We can 
   do that with the following definition.  *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** Of course, this proposition is equivalent to just saying that the
length of the list is even. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** However, because evidence for [ev] contains less information than
evidence for [ev_list], the converse direction must be stated very
carefully. *)

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  Case "ev_0". intros l H. destruct l.
    SCase "[]". apply el_nil. 
    SCase "x::l". inversion H.
  Case "ev_SS". intros l H2. destruct l. 
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "x :: x0 :: l". apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.
    

(** **** Exercise: 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
 *)

Inductive pal {X : Type} : list X -> Prop :=
| pal_0 : pal []
| pal_e : forall x, pal [x]
| pal_aa : forall x l, pal l -> pal (x::snoc l x)
.

Theorem pal_app_rev : forall X (l : list X),
    pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [| h t].
  Case "l = []". apply pal_0.
  Case "l = h::t". simpl.
  rewrite <- snoc_with_append. apply pal_aa. apply IHt.
Qed.

Theorem pal_rev : forall X (l : list X),
    pal l -> l = rev l.
Proof.
  intros.
  induction H.
  Case "pal_0". reflexivity.
  Case "pal_e". reflexivity.
  Case "pal_aa". simpl. rewrite rev_snoc. simpl. rewrite <- IHpal. reflexivity.
Qed.
(** [] *)

(* Again, the converse direction is much more difficult, due to the
lack of evidence. *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
 *)


(* This proof use le. TODO: change the proof to one not using le.*)
Lemma rev_pal_length : forall X (l : list X) n,
    length l <= n -> l = rev l -> pal l.
Proof.
  intros X l n.
  generalize dependent l.
  induction n as [| n0].
  Case "n = 0". intros. inversion H.
  destruct l as [| h t].
  SCase "l = []". apply pal_0.
  SCase "l = h::t". inversion H2.
  Case "n = S n0". intros.
  inversion H.
  SCase "=". destruct l as [| h t] eqn:Hl1.
  SSCase "l = []". apply pal_0.
  SSCase "l = h::t". simpl in H0.
  destruct (rev t) as [| th tt] eqn:Hl2.
  SSSCase "rev t = []". inversion H0. apply pal_e.
  SSSCase "rev t = th::tt". inversion H0. apply pal_aa. rewrite H4 in Hl2.
  rewrite rev_snoc in Hl2. apply IHn0. inversion H2.
  assert (forall X (l2: list X) x, length l2 + 1 = length (snoc l2 x)).
  SSSSCase "Proof of assertion". intros.
  induction l2 as [| h2 t2].
  SSSSSCase "l2 = []". reflexivity.
  SSSSSCase "l2 = h2::t2". simpl. rewrite IHt2. reflexivity.
  rewrite H4. rewrite <- H1. rewrite plus_comm. apply le_S. apply le_n.
  inversion Hl2. rewrite H5. rewrite H5. reflexivity.
  apply IHn0. apply H2. apply H0.
Qed.

Theorem rev_pal : forall X (l : list X),
    l = rev l -> pal l.
Proof.
  intros.
  apply rev_pal_length with (length l).
  apply le_n.
  apply H.
Qed.

Lemma length_0__nil : forall X (l : list X),
    length l = 0 -> l = [].
Proof.
  intros. destruct l as [| h t].
  Case "l = []". reflexivity.
  Case "l = h::t". inversion H.
Qed.

Fixpoint list_init {X : Type} (l : list X) : list X :=
  match l with
  | [] => []
  | h::[] => []
  | h::t => h::list_init t
  end
.

Fixpoint list_tail {X : Type} (x : X) (l : list X) : X :=
  match l with
  | [] => x
  | h::[] => h
  | _::t => list_tail x t
  end
.

Theorem pal_cons : forall X (l : list X) x y z,
    x::y::l = x::(snoc (list_init (y::l)) (list_tail z (y::l))).
Proof.
  intros X l.
  induction l as [| h t].
  Case "l = []". reflexivity.
  Case "l = h::t". intros. simpl. rewrite IHt with y h z. reflexivity.
Qed.

Theorem pal_induction : forall X (P : list X -> Prop),
    P [] ->
    (forall x, P [x]) ->
    (forall x y l, P l -> P (x::(snoc l y))) ->
    (forall l, P l).
Proof.
  intros X P H0 H1 Hpal l.
  assert ((forall n l', length l' = n -> P l') -> P l) as HLenInd.
  Case "Proof of assertion". intros. apply H with (length l). reflexivity.
  apply HLenInd.
  assert (forall l', length l' = 0 -> P l') as HInd0.
  Case "n = 0". intros. apply length_0__nil in H. rewrite H. apply H0.
  assert (forall l', length l' = 1 -> P l') as HInd1.
  Case "n = 1". intros. destruct l' as [| h' t'].
  SCase "l' = []". inversion H.
  SCase "l' = h'::t'". inversion H. apply length_0__nil in H3. rewrite H3. apply H1.
  assert (forall n, (forall l', length l' = n -> P l')
                    -> (forall l', length l' = S n -> P l')
                    -> (forall l', length l' = S (S n) -> P l')) as HInd01Ind.
  Case "Double Induction". intros.
  destruct l' as [| h' t'].
  SCase "l' = []". inversion H3.
  SCase "l' = h'::t'".
  destruct t' as [| th' tt'].
  SSCase "t' = []". inversion H3.
  SSCase "t' = th'::tt'".
  remember (pal_cons X tt' h' th' h') as HP.
  rewrite HP. apply Hpal.
  assert (forall X v (ls : list X), length (list_init (v :: ls)) = length ls).
  SSSCase "Proof of assertion".
  induction ls as [| lh lt].
  SSSSCase "ls = []". reflexivity.
  SSSSCase "ls = lh::lt". simpl. rewrite <- IHlt. simpl.
  destruct lt as [| lth ltt].
  SSSSSCase "lt = []". reflexivity.
  SSSSSCase "lt = lth::ltt". reflexivity.
  apply H. inversion H3. apply H4.
  intros n. 
  assert ((forall l', length l' = n -> P l') /\ (forall l', length l' = S n -> P l') -> (forall l', length l' = n -> P l')) as StrongP.
  Case "Proof of assertion". intros. inversion H. apply H3. apply H2.
  apply StrongP. clear StrongP.
  induction n as [| n0].
  Case "n = 0". split.
  SCase "left". apply HInd0.
  SCase "right". apply HInd1.
  Case "n = S n0". inversion IHn0. split.
  SCase "left". apply H2.
  SCase "right". apply HInd01Ind. apply H. apply H2.
Qed.

Lemma snoc_eq : forall X (l1 l2 : list X) v1 v2,
    snoc l1 v1 = snoc l2 v2 ->
    l1 = l2 /\ v1 = v2.
Proof.
  intros X l1.
  induction l1 as [| h1 t1].
  Case "l1 = []". destruct l2 as [| h2 t2].
  SCase "l2 = []". intros. inversion H. split.
  SSCase "left". reflexivity.
  SSCase "right". reflexivity.
  SCase "l2 = h2::t2". intros. inversion H.
  destruct t2 as [| t2h t2t].
  SSCase "t2 = []". inversion H2.
  SSCase "t2 = t2h::t2t". inversion H2.
  Case "l1 = h1::t1". intros. destruct l2 as [| h2 t2].
  SCase "l2 = []". inversion H. destruct t1 as [| t1h t1t].
  SSCase "t1 = []". inversion H2.
  SSCase "t1 = t1h::t1t". inversion H2.
  SCase "l2 = h2::t2". inversion H. apply IHt1 in H2.
  inversion H2.
  split.
  SSCase "left". rewrite H0. reflexivity.
  SSCase "right". apply H3.
Qed.

Theorem rev_pal' : forall X (l : list X),
    l = rev l -> pal l.
Proof.
  intros X l.
  (* We can repeat the pal induction in this proof, but it is too tidious. *)
  pattern l. apply pal_induction.
  Case "l = []". intros. apply pal_0.
  Case "l = [x]". intros. apply pal_e.
  Case "l = x::snoc l0 y". intros.
  simpl in H0. rewrite rev_snoc in H0.
  inversion H0. apply pal_aa. apply H.
  apply snoc_eq in H3. inversion H3. apply H1.
Qed.
(** [] *)



(* ####################################################### *)
(** ** Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** *** *)
(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
| tr : forall n m, total_relation n m.
(** [] *)

(** **** Exercise: 2 stars (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation {X : Type} : X -> X -> Prop :=
.
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  Case "le_n". apply H.
  Case "le_S". apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n0].
  Case "n = 0". apply le_n.
  Case "n = S n0". apply le_S. apply IHn0.
Qed.
  
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  intros n m.
  generalize dependent n.
  induction m as [| m0].
  Case "m = 0". intros. inversion H. apply le_n.
  Case "m = S m0". intros. inversion H.
  SCase "le_n". apply le_n.
  SCase "le_S". apply le_S. apply IHm0. apply H1.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.
  generalize dependent n.
  induction m as [| m0].
  Case "m = 0". intros. inversion H.
  SCase "le_n". apply le_n.
  SCase "le_S". inversion H1.
  Case "m = S m0". intros. inversion H.
  SCase "le_n". apply le_n.
  SCase "le_S". apply le_S. apply IHm0. apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros. induction b as [| b0].
  Case "b = 0". rewrite plus_comm. apply le_n.
  Case "b = S b0". rewrite plus_comm. simpl. rewrite plus_comm. apply le_S. apply IHb0.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 intros n1. induction n1 as [| n10].
 Case "n1 = 0". intros. simpl in H.
 inversion H.
 SCase "le_n". split.
 SSCase "left". apply n_le_m__Sn_le_Sm. apply O_le_n.
 SSCase "right". apply le_n.
 SCase "le_S". split.
 SSCase "left". apply n_le_m__Sn_le_Sm. apply O_le_n.
 SSCase "right". apply le_S. apply H0.
 Case "n1 = S n10". intros. simpl in H.
 destruct m as [| m0].
 SCase "m = 0". inversion H.
 SCase "m = S m0". apply Sn_le_Sm__n_le_m in H. apply IHn10 in H.
 inversion H. split.
 SSCase "left". apply n_le_m__Sn_le_Sm. apply H0.
 SSCase "right". apply le_S. apply H1.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S in H. apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  intros.
  generalize dependent n.
  induction m as [| m0].
  Case "m = 0". intros. destruct n as [| n0].
  SCase "n = 0". apply le_n.
  SCase "n = S n0". inversion H.
  Case "m = S m0". intros. destruct n as [| n0].
  SCase "n = 0". apply O_le_n.
  SCase "n = S n0". simpl in H. apply n_le_m__Sn_le_Sm. apply IHm0. apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m as [| m0].
  Case "m = 0". intros. inversion H.
  SCase "le_n". reflexivity.
  Case "m = S m0". intros. inversion H.
  SCase "le_n". simpl. apply IHm0. apply le_n.
  SCase "le_S". destruct n as [| n0].
  SSCase "n = 0". reflexivity.
  SSCase "n = S n0". simpl. apply IHm0. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  intros. apply le_ble_nat.
  apply le_trans with m.
  apply ble_nat_true. apply H.
  apply ble_nat_true. apply H0.
Qed.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not.
  intros.
  apply le_ble_nat in H0. rewrite H0 in H.
  inversion H.
Qed.
(** [] *)


(** **** Exercise: 3 stars (R_provability2)  *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

  Only First one is provable one.
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)  
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

Theorem R_fact_l : forall m n o,
    R m n o -> m + n = o.
Proof.
  intros. induction H.
  Case "c1". reflexivity.
  Case "c2". simpl. rewrite IHR. reflexivity.
  Case "c3". rewrite plus_comm. simpl. rewrite plus_comm. rewrite IHR. reflexivity.
  Case "c4". simpl in IHR. rewrite plus_comm in IHR.
  simpl in IHR. rewrite plus_comm in IHR. inversion IHR. reflexivity.
  Case "c5". rewrite plus_comm. apply IHR.
Qed.

Theorem R_fact_r : forall m n o,
    m + n = o -> R m n o.
Proof.
  intros m.
  induction m as [| m0].
  Case "m = 0". intros n. induction n as [| n0].
  SCase "n = 0". intros. inversion H. apply c1.
  SCase "n = S n0". intros. destruct o as [| o0].
  SSCase "o = 0". inversion H.
  SSCase "o = S o0". inversion H. apply c3. rewrite <- H1. apply IHn0. reflexivity.
  Case "m = S m0". intros. destruct o as [| o0].
  SCase "o = 0". inversion H.
  SCase "o = S o0". inversion H. apply c2. apply IHm0. reflexivity.
Qed.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is, 
      any list is a subsequence of itself.  

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3], 
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is 
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2] 
      is a subsequence of [l3], then [l1] is a subsequence of [l3].  
      Hint: choose your induction carefully!
 *)

Inductive subseq {X : Type} : list X -> list X -> Prop :=
| subnil : forall l, subseq [] l
| subele : forall v sl l, subseq sl l -> subseq (v::sl) (v::l)
| subskip : forall v sl l, subseq sl l -> subseq sl (v::l)
.

Theorem subseq_refl : forall X (l : list X),
    subseq l l.
Proof.
  intros. induction l as [| h t].
  Case "l = []". apply subnil.
  Case "l = h::t". apply subele. apply IHt.
Qed.

Theorem subseq_app : forall X (l1 l2 l3 : list X),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros X l1. induction l1 as [| h1 t1].
  Case "l1 = []". intros. apply subnil.
  Case "l1 = h1::t1". intros. destruct l2 as [| h2 t2].
  SCase "l2 = []". inversion H.
  SCase "l2 = h2::t2". induction H.
  SSCase "subnil". apply subnil.
  SSCase "subele". simpl. apply subele. apply IHsubseq.
  SSCase "subskip". simpl. apply subskip. apply IHsubseq.
Qed.

Theorem subseq_trans : forall X (l1 l2 l3 : list X),
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  generalize dependent l3. generalize dependent l2.
  induction l1 as [| h1 t1].
  Case "l1 = []". intros. apply subnil.
  Case "l1 = h1::t1". intros l2 Hl2. induction Hl2.
  SCase "subnil". intros. apply subnil.
  SCase "subele". intros l3 Hl3. induction l3 as [| h3 t3].
  SSCase "l3 = []". inversion Hl3.
  SSCase "l3 = h3::t3". inversion Hl3.
  SSSCase "subele". apply subele. apply IHHl2. apply H0.
  SSSCase "subskip". apply subskip. apply IHt3. apply H1.
  SCase "subskip". intros l3 Hl3. apply IHHl2.
  assert (forall eX ev (el1 el2 : list eX), subseq (ev::el1) el2 -> subseq el1 el2).
  SSCase "Proof of assertion". intros eX ev. intros el1 el2.
  generalize dependent el1. induction el2 as [| el2h el2t].
  SSSCase "el1 = []". intros. inversion H.
  SSSCase "el1 = el2h::el2t". intros. inversion H.
  SSSSCase "subele".  apply subskip. apply H1.
  SSSSCase "subskip". apply subskip. apply IHel2t. apply H2.
  apply H with v. apply Hl3.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)
(* [R 2 [1, 0]] and [R 1 [1,2,1,0]] are provable *)
(** [] *)


(* ##################################################### *)
(** * Programming with Propositions *)

(** As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun x : nat => if oddb x then Podd x else Peven x
.

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  unfold combine_odd_even. 
  intros.
  destruct (oddb n). apply H. reflexivity.
  apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  unfold combine_odd_even. 
  intros.
  rewrite H0 in H. apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  unfold combine_odd_even.
  intros.
  rewrite H0 in H. apply H.
Qed.
(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere)  *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

Fixpoint true_upto_n__true_everywhere (n : nat) (f : nat -> Prop) : Prop :=
  match n with
  | O => forall m : nat, f m
  | S n0 => f n -> true_upto_n__true_everywhere n0 f
  end
.

         
Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.

(** [] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)


