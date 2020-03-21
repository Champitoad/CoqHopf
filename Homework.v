Require Import HoTT Join UnivalenceAxiom.

(** remove printing * *)

(** _Note_: we will use the [Admitted] command whenever we do not
    give the term for a certain type. We then associate the
    following meanings to assertion commands:

    - [Fact] denotes a fact proven in the course or the HoTT book
    - [Proposition] denotes either a proposition assumed to be true
      in the subject, or a partially answered optional question
    - [Lemma]/[Theorem] denote a partially answered mandatory question

    We also follow the convention to name [q_i_j] the answer to
    question j of exercise i.

    Whenever we use a lemma implemented in the HoTT library,
    we will be careful to state which lemma of the course/HoTT book
    it corresponds to.
*)

(** * Prelude *)

(** Notations to match more closely those of the course/subject. *)

Notation "'ua'" := equiv_path.
Notation "'ua^-1'" := path_universe.

Notation "2" := Bool.
Notation "'Σ' A" := (Susp A) (format "'Σ' A", at level 10).
Notation "'S^' n" := (Sphere n) (format "'S^' n", at level 10).
Notation "'S*^' n" := (psphere n) (format "'S*^' n", at level 10).
Infix "×" := prod (at level 30).
Infix "∗" := Join (at level 30).
Infix "≃" := Equiv (at level 50).
Infix "≃*" := pEquiv (at level 50).
Notation "| A |" := (merely A) (format "| A |", at level 70).

(** *** Spans *)

Inductive Span :=
| span {A B C : Type} (f : B -> A) (g : B -> C).

Record EqSpan'
  {A B C : Type} (f : B -> A) (g : B -> C) 
  {A' B' C' : Type} (f' : B' -> A') (g' : B' -> C')
:= {
  equiv_left : A ≃ A';
  equiv_apex : B ≃ B';
  equiv_right : C ≃ C';
  coherence_left : equiv_left o f == f' o equiv_apex;
  coherence_right : equiv_right o g == g' o equiv_apex;
}.

Definition EqSpan '(span _ _ _ f g) '(span _ _ _ f' g') :=
  EqSpan' f g f' g'.

Proposition path_span {s s'} :
  EqSpan s s' ≃ (s = s').
Proof.
Admitted.

(** * Exercise 1 *)

Section Exercise_1.

(** ** Question 1 *)

Section Question_1.

Context (A : Type).

Let φ : 2 ∗ A -> Σ A.
Proof.
  (* By recursion on joins, that is on pushouts *)
  srapply Join_rec; simpl.
  (* φ(left(b)) :≡ … *)
  * exact (
      fun b => match b with
      | false => North
      | true => South
      end).
  (* φ(right(a)) :≡ … *)
  * exact (fun _ => South).
  (* ap_φ(quo(b,a)) :≡ … *)
  * intros b a. simpl.
    (* By recursion/case on b *)
    destruct b.
    - exact idpath. (* [idpath] is refl *)
    - exact (merid a).
Defined.

Let ψ : Σ A -> 2 ∗ A.
Proof.
  (* By recursion on suspensions *)
  srapply Susp_rec.
  (* ψ(N) :≡ … *)
  * exact (joinl false).
  (* ψ(S) :≡ … *)
  * exact (joinl true).
  (* ψ(merid_a) :≡ … *)
  * (* [jglue b a] is quo(b,a) *)
    intros a. exact ((jglue false a) @ (jglue true a)^).
Defined.

(** For this first proof, we will comment every step in order to
    document how "informal" reasoning translates into tactics and lemmas
    of the HoTT library. In subsequent proofs, we will only document
    parts that use new tactics/lemmas. *)

Lemma q_1_1 :
  2 ∗ A ≃ Σ A.
Proof.
  unshelve econstructor.
  (* We choose φ as the underlying map of the equivalence *)
  * exact φ.
  (* We show that φ is indeed an equivalence, with ψ as inverse *)
  * apply isequiv_adjointify with ψ.
    (* φ ○ ψ ~ id *)
    - unfold Sect.
      (* By induction on suspensions *)
      srapply Susp_ind; simpl.
      (* φ(ψ(N) = N *)
      + exact idpath.
      (* φ(ψ(S) = S *)
      + exact idpath.
      (* tr_{merid x}(refl) = refl *)
      + intros a.
        (* We use an instance of theorem 2.11.3 of the HoTT book *)
        rewrite transport_paths_FFlr.
        (* Compute with the definition of ψ *)
        unfold ψ. rewrite Susp_rec_beta_merid.
        (* Lemma 7 and 8 of the course *)
        rewrite ap_pp, ap_V.
        (* Compute with the definition of φ *)
        unfold φ. rewrite 2 Join_rec_beta_jglue.
        (* The [hott_simpl] tactic tries to simplify paths using
           basic homotopies, such as composition with identity and
           inverse paths *)
        hott_simpl.
    (* ψ ○ φ ~ id *)
    - unfold Sect.
      (* By induction on joins *)
      srapply Join_ind; simpl.
      (* ψ(φ(left(b))) = left(b) *)
      + intros b.
        (* By case on b *)
        destruct b; simpl.
        ** exact idpath.
        ** exact idpath.
      (* ψ(φ(right(a))) = right(a) *)
      + intros a. exact (jglue true a).
      (* tr_{quo(b,a)}(refl) = quo(1,a) *)
      + intros b a. apply dp_path_transport.
        (* Again, same instance of theorem 2.11.3 of the HoTT book *)
        rewrite transport_paths_FFlr.
        (* Compute with the definition of φ *)
        unfold φ. rewrite Join_rec_beta_jglue.
        (* By case on b *)
        destruct b.
        (* tr_{quo(1,a)}(refl) = quo(1,a) *)
        ** hott_simpl.
        (* tr_{quo(0,a)}(refl) = quo(1,a) *)
        ** (* Compute with the definition of ψ *)
           unfold ψ. rewrite Susp_rec_beta_merid.
           (* Unwhiskering on the right with quo(1,a), that is
              post-composing with quo(1,a) on both sides *)
           apply (cancelR _ _ (jglue true a)^).
           hott_simpl.
           (* Associativity of composition *)
           rewrite concat_pp_p.
           hott_simpl.
Defined.

End Question_1.

(** ** Question 2 *)

Section Question_2.

Proposition q_1_2 : forall A B C,
  (A ∗ B) ∗ C ≃ A ∗ (B ∗ C).
Proof.
Admitted.

End Question_2.

(** ** Question 3 *)

Section Question_3.

Fact Bool_Sphere_0 :
  2 ≃ S^0.
Proof.
Admitted.

(** We need functoriality of type formers with respect to equivalence,
    in order to apply equivalences to their arguments. We could prove
    it individually for each type former of interest, but we choose
    instead to use univalence to prove it once and forall. *)

Definition ae {X Y} (T : Type -> Type) :
  X ≃ Y -> T X ≃ T Y.
Proof.
  intros e.
  (* [path_universe_uncurried] is the map given by univalence *)
  apply path_universe_uncurried in e.
  (* The [path_induction] tactic applies path induction to every
     path found in the context *)
  path_induction.
  (* [equiv_idmap] is the identity equivalence *)
  exact equiv_idmap.
Defined.

(** The [rewrite] tactic of the HoTT library is quite weak since
    it does not support equivalences, and does not allow selecting
    the occurrences of the term we want to rewrite. Thus we will
    compose equivalences manually using the [refine] tactic and
    the [oE] composition operator. *)

Open Scope equiv_scope.

Lemma q_1_3 :
  S^1 ∗ S^1 ≃ S^3.
Proof.
  (* Rewrite on the left of ∗ using functoriality *)
  refine (_ oE ae (fun X => X ∗ _) _).
  2: { (* Rewrite under Σ using functoriality (since S^n is the
          definition of the sphere based on iterated suspensions) *)
       refine (ae Susp _).
       (* Rewrite S^0 into 2 *)
       exact Bool_Sphere_0^-1. }
  (* Rewrite on the left of ∗ using functoriality *)
  refine (_ oE ae (fun X => X ∗ _) _).
  2: { (* Rewrite Σ2 into 2 ∗ 2 using [q_1_1] *)
       exact (q_1_1 _)^-1. }
  (* Associativity of ∗ *)
  refine (_ oE q_1_2 _ _ _).
  (* Rewrite on the right of ∗ using functoriality *)
  refine (_ oE ae (fun X => _ ∗ X) _).
  2: { (* Rewrite 2 ∗ S^1 into ΣS^1 using [q_1_1] *)
       exact (q_1_1 _). }
  (* Rewrite 2 ∗ S^1 into ΣΣS^1 using [q_1_1] *)
  refine (_ oE q_1_1 _).
  exact equiv_idmap.
Defined.

Close Scope equiv_scope.

End Question_3.

End Exercise_1.

(** * Exercise 2 *)

Section Exercise_2.

Context (A : Type) (P : Σ A -> Type).

(** ** Question 1 *)

Section Question_1.

Let ψ '(q, a) := transport P (merid a) q.

Proposition q_2_1 :
  {x : Σ A & P x} ≃ Pushout fst ψ.
Proof.
Admitted.

End Question_1.

End Exercise_2.

(** * Exercise 3 *)

Section Exercise_3.

Context (A : Type) (μ : A × A -> A).

Notation "'μ'" := μ.
Notation "'μ' ( a , b )" := (μ (pair a b)) (format "'μ' ( a , b )").
Notation "'μ' ( a , '_' )" := (fun x => μ(a,x)) (format "'μ' ( a , _ )").
Notation "'μ' ( '_' , a )" := (fun x => μ(x,a)) (format "'μ' ( _ , a )").

Context `(forall a, IsEquiv μ(a,_)).
Context `(forall a, IsEquiv μ(_,a)).

Definition P : Σ A -> Type.
Proof.
  srapply Susp_rec; simpl.
  * exact A.
  * exact A.
  * intros a. exact (ua^-1 μ(_,a)).
Defined.

(** ** Question 1 *)

Section Question_1.

Fact hottbook_lemma_2_10_5 :
  forall (A : Type) (B : A -> Type) (x y : A) (p : x = y) (u : B x),
  transport B p u = ua _ _ (ap B p) u.
Proof.
Admitted.

Lemma q_3_1 : forall a b : A,
  transport P (merid b) a = μ(a,b).
Proof.
  intros a b.
  rewrite hottbook_lemma_2_10_5. simpl.
  rewrite Susp_rec_beta_merid.
  (* [transport_path_universe] is the propositional computation
     rule of univalence (see section 2.10 of the HoTT book) *)
  rewrite transport_path_universe.
  exact idpath.
Defined.

End Question_1.

(** ** Question 2 *)

Section Question_2.

Let ψ '(q, a) := transport P (merid a) q.

Lemma path_ψ_μ :
  ψ = μ.
Proof.
  (* [equiv_path_arrow] is function extensionality *)
  apply equiv_path_arrow.
  intros p. destruct p as (a, b).
  unfold ψ. apply q_3_1.
Defined.

Lemma q_3_2 :
  {x : Σ A & P x} ≃ Pushout fst μ.
Proof.
  refine (_ oE (q_2_1 _ _)).
  rewrite <- path_ψ_μ.
  exact equiv_idmap.
Defined.

End Question_2.

(** ** Question 3 *)

Let s := @span A (A × A) A fst μ.
Let s' := @span A (A × A) A fst snd.

Section Question_3.

Let ε : A × A -> A × A := fun '(a, b) => (a, μ(a,_) b).
Let ε_inv : A × A -> A × A := fun '(a, b) => (a, μ(a,_)^-1 b).

Lemma q_3_3 :
  s = s'.
Proof.
  (* We use the analysis of equality between spans *)
  apply path_span. unshelve econstructor.
  (* Left equivalence *)
  * exact equiv_idmap.
  (* Apex equivalence *)
  * unshelve econstructor.
    - exact ε.
    - apply isequiv_adjointify with ε_inv.
      + unfold Sect. intros [a b]. unfold ε, ε_inv.
        (* μ(a,_) is an equivalence *)
        rewrite (eisretr μ(a,_)).
        exact idpath.
      + unfold Sect. intros [a b]. unfold ε, ε_inv.
        (* μ(a,_) is an equivalence *)
        rewrite (eissect μ(a,_)).
        exact idpath.
  (* Right equivalence *)
  * exact equiv_idmap.
  (* Left coherence *)
  * simpl. apply equiv_path_arrow. exact idpath.
  (* Right coherence *)
  * simpl. apply equiv_path_arrow. exact idpath.
Defined.

End Question_3.

(** ** Question 4 *)

Section Question_4.

Lemma q_3_4 :
  {x : Σ A & P x} ≃ A ∗ A.
Proof.
  refine (_ oE q_3_2).
  (* [equiv_pushout] gives an analysis of equivalence between pushouts
     as defined in the HoTT library, which will allow us to reduce it
     to the analysis of equality between spans of [q_3_3] *)
  refine (_ oE equiv_pushout _ _ _ _ _).
  * exact equiv_idmap.
  (* Left coherence... *)
  * eapply coherence_left.
  (* ...and right coherence... *)
  * eapply coherence_right.
  Unshelve.
  (* ...that we get from [q_3_3] *)
  apply (path_span^-1 q_3_3).
Defined.

End Question_4.

End Exercise_3.

(** * Exercise 4 *)

Section Exercise_4.

Open Scope pointed_scope.

Class IsHType (carrier : pType) := {
  mult : carrier × carrier -> carrier;
  unit_left : forall x, mult (point carrier, x) = x;
  unit_right : forall x, mult (x, point carrier) = x;
}.

Class IsConnected A := connected : forall x y : A, |x = y|.

Context (A : pType) `{IsHType A} `{IsConnected A}.

Notation e := (point A).
Notation "'μ'" := mult.
Notation "'μ' ( a , b )" := (μ (pair a b)) (format "'μ' ( a , b )").
Notation "'μ' ( a , '_' )" := (fun x => μ(a,x)) (format "'μ' ( a , _ )").
Notation "'μ' ( '_' , a )" := (fun x => μ(x,a)) (format "'μ' ( _ , a )").

(** ** Question 1 *)

Section Question_1.

(** I could not find a proper induction principle for the
    propositional truncation in the HoTT library, thus we
    assume the one seen in course. *)

Fact merely_ind :
  forall (A : Type) (P : |A| -> Type),
  (forall x : A, P (tr x)) ->
  forall x : |A|, P x.
Proof.
Admitted.

(** A consequence of the induction principle is that
    for any type B, assuming |B| amounts to assuming B. *)

Lemma destruct_merely : forall B,
  |B| -> B.
Proof.
  intros B. apply (merely_ind B). exact idmap.
Defined.

Lemma q_4_1 : forall x : A,
  |μ(x,_) = idmap| × |μ(_,x) = idmap|.
Proof.
  intros x. split.
  * apply tr.
    apply equiv_path_arrow.
    unfold "==". intros a.
    pose proof (connected μ(x,a) a).
    now apply destruct_merely.
  * apply tr.
    apply equiv_path_arrow.
    unfold "==". intros a.
    pose proof (connected μ(a,x) a).
    now apply destruct_merely.
Defined.

End Question_1.

(** ** Question 2 *)

Instance isequiv_μ_left :
  forall x, IsEquiv μ(x,_).
Proof.
  intros x. destruct (q_4_1 x) as [Hl Hr].
  apply (destruct_merely _) in Hl.
  rewrite Hl. apply isequiv_idmap.
Defined.

Instance isequiv_μ_right :
  forall x, IsEquiv μ(_,x).
Proof.
  intros x. destruct (q_4_1 x) as [Hl Hr].
  apply (destruct_merely _) in Hr.
  rewrite Hr. apply isequiv_idmap.
Defined.

(** ** Question 3 *)

Section Question_3.

(** Short name for the equivalence obtained in q_3_4,
    instanciated to our H-type [A]. *)

Let ε := (q_3_4 A μ _ _).

(** First, we need a few definitions to make our operations
    live in the pointed universe. *)

(** *** Pointed Σ-types *)

Definition psig {X : pType}
  (P : X -> Type) `{pointP : IsPointed (P (point X))} : pType.
Proof.
  unshelve econstructor.
  * exact (sig P).
  * apply ispointed_sigma.
Defined.

(** *** Pointed joins *)

(** Note that we do not use a general definition for pointed joins:
    instead we only define the pointed [A ∗ A], so that we can choose
    a specific basepoint (this will allow us to prove ε to be a
    pointed equivalence, and not just a "mere" equivalence. *)

Definition pjoin : pType.
Proof.
  unshelve econstructor.
  * exact (A ∗ A).
  * exact (ε (North; e)).
Defined.

(** *** Fiber sequences *)

(** We also need to define fiber sequences, since they are
    not implemented in the HoTT library. *)

Definition fib {X Y : pType} (f : X ->* Y) : pType.
Proof.
  unshelve econstructor.
  * exact (hfiber f (point Y)).
  * exact (point X; point_eq f).
Defined.

Definition fib_proj {X Y : pType} (f : X ->* Y) : fib f ->* X.
Proof.
  unshelve econstructor.
  * intros x. destruct x as [x _]. exact x.
  * simpl. exact idpath.
Defined.

Definition IsFiberSeq {X Y Z : pType} (f : X ->* Y) (g : Y ->* Z) :=
  {p : X = fib g & transport (fun B => B ->* Y) p f = fib_proj g}.

Record FiberSeq (X Y Z : pType) := {
  fiberseq_proj : X ->* Y;
  fiberseq_map : Y ->* Z;
  isfiberseq : IsFiberSeq fiberseq_proj fiberseq_map;
}.

(** One can make a fiber sequence from a fibration, i.e.
    a type family [C : X -> Type], whenever [X] is pointed
    by [∗] and [C(∗)] is pointed as well. *)

Proposition fibration_fiberseq {X : pType}
  (C : X -> Type) `{ispointed_C : IsPointed (C (point X))} :
  @FiberSeq {| pointed_type := C (point X);
               ispointed_type := ispointed_C |}
            (psig C) X.
Proof.
Admitted.

(** The trick then is to define the fibration [C] so that
    it coincides with the [P] from exercise 3. *)

Definition C : psusp A -> Type.
Proof.
  srapply Susp_rec; simpl.
  * exact A.
  * exact A.
  * intros a. exact (ua^-1 μ(_,a)).
Defined.

Instance ispointed_C : IsPointed (C (point (psusp A))) := e.

(** We use C to get a fiber sequence

      [A →∗ (x : ΣA) × C(x) →∗ ΣA] *)

Let σ := fibration_fiberseq C.

(** Intuitively, it only remains to "rewrite" [(x : ΣA) × C(x)]
    into [A ∗ A] using ε to conclude. But we cannot do this
    directly because we only have an equivalence of non-pointed
    types, but sequences are defined on pointed types. *)

(** So we start by building a pointed equivalence from ε. *)

Definition ε_pointed :
  psig C ≃* pjoin.
Proof.
  unshelve econstructor.
  * exact (pmap_from_point ε (North; e)).
  * apply isequiv_adjointify with ε^-1.
    - apply eisretr.
    - apply eissect.
Defined.

(** Then we rewrite, and that's it!

    In fact we have to cheat a little bit: we use the lemma [path_ptype]
    to turn the pointed equivalence into a path in the universe of
    pointed types, which follows from univalence with a bit of work. *)

Lemma q_4_3 :
  @FiberSeq A (pjoin) (psusp A).
Proof.
  rewrite <- (path_ptype ε_pointed).
  exact σ.
Defined.

End Question_3.

End Exercise_4.

(** * Exercise 5 *)

Section Exercise_5.

(** ** Question 1 *)

Section Question_1.

(* [S1] is the inductive definition of the circle, not to be confused
   with [S^1] which is the definition based on iterated suspension
   (though the two definitions are equivalent). *)

Definition ψ' : forall x : S1, x = x.
Proof.
  srapply S1_ind; simpl.
  * exact loop.
  * (* Lemma 2.11.2 of the HoTT book *)
    rewrite transport_paths_lr.
    hott_simpl.
Defined.

End Question_1.

(** ** Question 2 *)

Section Question_2.

Let ψ := path_forall _ _ ψ'.

Definition μ : S1 -> S1 -> S1.
Proof.
  srapply S1_rec.
  * exact idmap.
  * exact ψ.
Defined.

Proposition q_5_2 : forall x : S1,
  (μ x base = x) × (μ base x = x).
Proof.
Admitted.

End Question_2.

(** ** Question 3 *)

Section Question_3.

(** Pointed circle, built from the easy to manipulate
    inductive definition. *)

Definition pcircle : pType := Build_pType S1 base.

Notation "'S1*'" := pcircle.

(** With the previous question, we can prove that
    the (pointed) circle is an HType. *)

Instance ishtype_pcircle : IsHType S1*.
Proof.
  unshelve econstructor.
  * intros [x y]. exact (μ x y).
  * simpl. intros. exact idpath.
  * simpl. intros. exact (fst (q_5_2 _)).
Defined.

(** The circle is connected. *)

Instance isconnected_pcircle : IsConnected S1*.
Proof.
Admitted.

(** First we adapt the equivalence from [q_1_3] to the inductive
    definition of the circle. *)

Let ε : S1 ∗ S1 ≃ S^3.
Proof.
  pose proof q_1_3 as ε.
  rewrite (ua^-1 Sph1_to_S1) in ε.
  exact ε.
Qed.

(** Then we define a 3-sphere with a custom basepoint, so that we can
    build the pointed equivalence with the same trick of [q_4_3]. *)

Definition psphere3 := Build_pType (S^3) (ε (point (pjoin S1*))).

(** Now we can build the pointed equivalence. *)

Lemma q_1_3_pointed :
  pjoin (S1*) ≃* psphere3.
Proof.
  unshelve econstructor.
  * exact (pmap_from_point ε (point (pjoin S1*))).
  * apply isequiv_adjointify with ε^-1.
    - apply eisretr.
    - apply eissect.
Defined.

(** Finally, we put everything together to get the Hopf fibration! *)

Theorem q_5_3 :
  @FiberSeq (S1*) (psphere3) (S*^2).
Proof.
  (* Build the fiber sequence of [q_4_3] *)
  pose proof (q_4_3 S1*) as σ.
  (* Rewrite using the equivalence of [q_1_3] *)
  rewrite <- (path_ptype q_1_3_pointed).
  (* Turn the inductive pointed circle inside the 2-sphere
     into its iterated pointed suspension version *)
  unfold pcircle in σ at 3.
  rewrite <- (path_ptype pequiv_pSph1_to_S1) in σ.
  (* That's it! *)
  exact σ.
Defined.

End Question_3.

(** ** Question 4 *)

Section Question_4.

Lemma q_5_4 : forall n,
  Pi n (S*^3) = Pi n (S*^2).
Proof.
  (* By the argument given in the course to illustrate lemma 29,
     which uses the Hopf fibration built in [q_5_3]. *)
Admitted.

End Question_4.

End Exercise_5.
