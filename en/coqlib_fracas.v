Parameter Entity : Type.

Parameter Rel : Entity -> Entity -> Prop.
Parameter Prog : Prop -> Prop.
Parameter two : Entity -> Prop.
Parameter Top : Entity -> Entity.
Parameter Most : (Entity -> Prop) -> (Entity -> Prop) -> Prop.

(* Notation and axioms for proportional determiners *)
Notation "'most' x ; P , Q" := (Most (fun x => P) (fun x => Q))
   (at level 30, x ident, right associativity) : type_scope.

Axiom most_ex_import :
  forall (F G: Entity -> Prop),
   (Most F G -> exists x, F x /\ G x).

Axiom most_consv :
  forall (F G: Entity -> Prop),
   (Most F G -> Most F (fun x => (F x /\ G x))).

Axiom most_rightup :
  forall (F G H: Entity -> Prop),
   ((Most F G) ->
   (forall x, G x -> H x) -> (Most F H)).

Hint Resolve most_ex_import most_consv most_rightup.

(* veridical predicates *)
Parameter _true : Prop -> Prop.

Axiom veridical_true : forall P, (_true P -> P).

Ltac solve_veridical_true :=
  match goal with
    H : _true _ |- _
    => try apply veridical_true in H
  end.

(* anti-veridical predicates *)
Parameter _false : Prop -> Prop.

Axiom antiveridical_false : forall P, (_false P -> ~P).

Hint Resolve antiveridical_false.

Ltac solve_antiveridical_false :=
  match goal with
    H : _false _ |- _
    => try apply antiveridical_false in H
  end.

(* implicative verbs *)
Parameter _manage : Entity -> Prop -> Prop.

Axiom implicative_manage : forall x P, (_manage x P -> P).

Ltac solve_implicative_manage :=
  match goal with
    H : _manage _ _ |- _
    => try apply implicative_manage in H
  end.

Parameter _fail : Entity -> Prop -> Prop.

Axiom implicative_fail : forall x P, (_fail x P -> ~ P).

Ltac solve_implicative_fail :=
  match goal with
    H : _fail _ _ |- _
    => try apply implicative_fail in H
  end.

(* factive verbs *)
Parameter _know : Entity -> Prop -> Prop.

Axiom factive_know : forall x P, (_know x P -> P).

Ltac solve_factive :=
  match goal with
    H : _know _ _ |- _
    => try apply factive_know in H
  end.

(* privative adjectives *)
Parameter _former : Prop -> Prop.

Axiom privative_former : forall P, (_former P -> ~P).

Hint Resolve privative_former.

Ltac solve_privative_former :=
  match goal with
    H : _former _ |- _
    => try apply privative_former in H
  end.

(* before and after *)
Parameter _before : Prop -> Prop -> Prop.
Parameter _after : Prop -> Prop -> Prop.

Axiom transitivity_before : forall P1 P2 P3 : Prop,
  _before P1 P2 -> _before P2 P3 -> _before P1 P3.

Axiom transitivity_after : forall P1 P2 P3 : Prop,
  _after P1 P2 -> _after P2 P3 -> _after P1 P3.

Axiom before_after : forall P Q : Prop,
  _before P Q -> _after Q P.

Axiom after_before : forall P Q : Prop,
  _after P Q -> _before Q P.

Hint Resolve transitivity_before transitivity_after before_after after_before.

(* tactics for resolving modality and equality *)

Ltac apply_ent :=
  match goal with
    | [x : Entity, H : forall x : Entity, _ |- _]
     => apply H
  end.

Ltac eqlem1 :=
  match goal with
    | [x : Entity, H0 : ?A ?x, H : forall x, ?A x -> _ -> @?C x |- _]
     => match type of H with context[_ = _]
        => assert(C x)
     end
  end.

Ltac eqlem2 :=
  match goal with
    | [x : Entity, H0 : ?A ?x, H : forall x, ?A x /\ ?B x -> _ -> @?C x |- _]
     => match type of H with context[_ = _]
        => assert(C x)
     end
  end.

Ltac eqlem3 :=
  match goal with
    | [x : Entity, H0 : ?A ?x, H : forall x, _ /\ ?A x -> @?C x |- _]
     => match type of H with context[_ = _]
        => assert(C x)
     end
  end.

Ltac solve_false :=
  match goal with
    | [H : _ -> False |- False]
     => apply H
  end.

Ltac nltac_init :=
  try(intuition;try solve_false;firstorder;subst;firstorder).

Ltac nltac_base := 
  try(nltac_init);
  try(firstorder;intuition;firstorder;eauto;eexists;firstorder;eauto);
  try(subst;eauto;firstorder);
  try(eauto;firstorder).

Ltac nltac_axiom :=
  try first
    [solve_veridical_true |
     solve_antiveridical_false |
     solve_implicative_manage |
     solve_implicative_fail |
     solve_factive |
     solve_privative_former
    ].

Ltac nltac_eq :=
  try solve
    [nltac_init |
     repeat nltac_base |
     nltac_init;nltac_axiom;nltac_base |
     nltac_init;eqlem1;nltac_base |
     nltac_init;eqlem2;nltac_base |
     nltac_init;eqlem3;nltac_base
    ].

Ltac nltac_ent := nltac_base; apply_ent; nltac_eq.

Ltac solve_gq :=
  match goal with
    H : Most _ _ |- _
    => let H0 := fresh in
       try solve [         
          pose (H0 := H); eapply most_ex_import in H0;
            try nltac_ent; try nltac_eq |
          pose (H0 := H); eapply most_consv in H0;
            eapply most_rightup in H0;
            try nltac_ent; try nltac_eq |
          pose (H0 := H); eapply most_consv in H0;
            try nltac_ent; try nltac_eq |
          pose (H0 := H); eapply most_rightup in H0;
            try nltac_ent; try nltac_eq ]
  end.

Ltac nltac :=
  try solve
    [nltac_eq |
     nltac_base;apply_ent;nltac_eq |
     nltac_init; solve_gq
    ].
