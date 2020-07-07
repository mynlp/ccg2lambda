(* Basic types *)
Parameter Entity : Type.
Parameter Event : Type.

Parameter Rel : Entity -> Entity -> Prop.
Parameter Mod : Entity -> Event -> Prop.
Parameter Prog : Prop -> Prop.
Parameter this : (Entity -> Prop) -> Entity.
Parameter that : (Entity -> Prop) -> Entity.

(* Temporal operators *)
Parameter Hold : Event -> Prop.
Parameter Cul : Event -> Prop.
Parameter Past : Event -> Prop.
Parameter Future : Event -> Prop.

(* Modal operators *)
Parameter Poss : Event -> Prop.
Parameter NonPoss : Event -> Prop.

(* Proposition marker and question marker *)
Parameter Content : Entity -> (((Event -> Prop) -> Event -> Prop) -> Prop) -> Prop.
Parameter WH : Prop -> Prop.

(* Thematic roles *)
Parameter Subj : Event -> Entity.
Parameter Top : Event -> Entity.
Parameter Nom : Event -> Entity.
Parameter Acc : Event -> Entity.
Parameter AccI : Event -> Prop -> Prop.
Parameter AccE : Event -> Event.
Parameter Dat : Event -> Entity.
Parameter Attr : Event -> Entity.
Parameter Deg : Event -> Entity.

(* Binary quantifiers *)
Parameter Most : (Entity -> Prop) -> (Entity -> Prop) -> Prop.

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

(* Unary quantifiers *)
Parameter Few : (Entity -> Prop) -> Prop.

Axiom few_down : 
  forall (F G: Entity -> Prop),
   Few F -> (forall x, G x -> F x) -> Few G.

(* Veridical predicates *)
Parameter _たしか : Event -> Prop.
Axiom factive_たしか1 : forall (v : Event) (P : ((Event -> Prop) -> Event -> Prop) -> Prop),
  _たしか v -> Content (Nom v) P -> P (fun I => I).
Axiom factive_たしか2 : forall v : Event, forall P : Prop,
  _たしか v -> AccI v P ->  P.
Ltac solve_たしか :=
 match goal with
   | [H1 : _たしか ?e, H2 : Content (Nom ?e) _ |- _] => try apply factive_たしか1 with (v:=e) in H2
   | [H1 : _たしか ?e, H2 : AccI ?e _ |- _] => try apply factive_たしか2 with (v := e) in H2
 end.

Parameter _本当 : Entity -> Prop.
Axiom factive_本当 : forall v : Event, forall P : Prop,
  _本当 (Nom v) -> AccI v P -> P.
Ltac solve_本当 :=
 match goal with
   H1 : _本当 (Nom ?e), H2 : AccI ?e _ |- _
     => try apply factive_本当 with (v := e) in H2
 end.

(* Anti-veridical predicates *)
Parameter _嘘 : Entity -> Prop.
Axiom factive_嘘 : forall v : Event, forall P : Prop,
  _嘘 (Nom v) -> AccI v P -> ~P.

Ltac solve_嘘 :=
 match goal with
   H1 : _嘘 (Nom ?e), H2 : AccI ?e _ |- _
     => try apply factive_嘘 with (v := e) in H2
 end.

Axiom anti_factive_NonPoss1 : forall (v : Event) (P : ((Event -> Prop) -> Event -> Prop) -> Prop),
  NonPoss v -> Content (Nom v) P -> ~ (P (fun I => I)).
Axiom anti_factive_NonPoss2 : forall v : Event, forall P : Prop,
  NonPoss v -> AccI v P -> ~P.

Ltac solve_Poss :=
 match goal with
   | [H1 : NonPoss ?e, H2 : Content (Nom ?e) _ |- _] => try apply anti_factive_NonPoss1 with (v:=e) in H2
   | [H1 : NonPoss ?e, H2 : AccI ?e _ |- _] => try apply anti_factive_NonPoss2 with (v := e) in H2
 end.

(* Attitude verbs *)
Parameter _疑う : Event -> Prop.
Parameter _思う : Event -> Prop.
Axiom pos_疑う_思う : forall (v : Event) (P : Prop), (_疑う v -> AccI v P -> _思う v /\ AccI v P).
Axiom neg_prop_疑う_思う : forall (v : Event) (P : ((Event -> Prop) -> Event -> Prop) -> Prop),
  _疑う v -> Content (Acc v) P -> _思う v /\ AccI v (~ (P (fun I => I))).
Axiom neg_wh_疑う_思う : forall v P, (_疑う v -> AccI v (WH (~P)) -> _思う v /\ AccI v P).

Ltac solve_疑う_思う :=
 match goal with
   | [H1 : _疑う ?e, H2 : AccI ?e (WH _) |- _] => try apply neg_wh_疑う_思う with (v := e) in H2
   | [H1 : _疑う ?e, H2 : Content (Acc ?e) _ |- _] => try apply neg_prop_疑う_思う with (v:=e) in H2
   | [H1 : _疑う ?e, H2 : AccI ?e _ |- _] => try apply pos_疑う_思う with (v := e) in H2
 end.

(* Implicative verbs *)
Parameter _成功 : Event -> Prop.
Axiom implicative_成功 : forall (v : Event) (x : Entity) (P : ((Event -> Prop) -> Event -> Prop) -> Prop),
  _成功 v -> Nom v = x -> Past v -> Content (Dat v) P -> P (fun J : Event -> Prop => fun e : Event => J e /\ Nom e = x /\ Past e).
Ltac solve_成功 :=
 match goal with
   | [H1 : _成功 ?e, H2 : Nom ?e = ?t, H3 : Past ?e, H4 : Content (Dat ?e) _ |- _]
     => apply implicative_成功 with (v:=e)(x:=t) in H4
 end.

(* Perceptual verbs *)
Parameter _見る : Event -> Prop.
Axiom factive_見る : forall (v : Event) (P : ((Event -> Prop) -> Event -> Prop) -> Prop),
  _見る v -> Past v -> Content (Acc v) P -> P (fun J : Event -> Prop => fun e : Event => J e /\ Past e).
Ltac solve_factive_見る :=
 match goal with
   | [H1 : _見る ?e, H2 : Past ?e, H3 : Content (Acc ?e) _ |- _]
     => apply factive_見る with (v:=e) in H3
 end.

Axiom closure_見る : forall (v: Event) (P P': ((Event -> Prop) -> Event -> Prop) -> Prop),
  _見る v -> Content (Acc v) P -> (P (fun I => I) -> P' (fun I => I)) -> Content (Acc v) P'.
Ltac solve_closure_見る :=
 match goal with
   | [H1 : _見る ?e, H2 : Content (Acc ?e) ?A |- Content (Acc ?e) ?B ]
     => apply closure_見る with (v:=e)(P:=A)(P':=B)
 end.

Parameter _聞く : Event -> Prop.
Axiom factive_聞く : forall (v : Event) (P : ((Event -> Prop) -> Event -> Prop) -> Prop),
  _聞く v -> Past v -> Content (Acc v) P -> P (fun J : Event -> Prop => fun e : Event => J e /\ Past e).
Ltac solve_factive_聞く :=
 match goal with
   | [H1 : _聞く ?e, H2 : Past ?e, H3 : Content (Acc ?e) _ |- _]
     => apply factive_聞く with (v:=e) in H3
 end.

Axiom closure_聞く : forall (v: Event) (P P': ((Event -> Prop) -> Event -> Prop) -> Prop),
  _聞く v -> Content (Acc v) P -> (P (fun I => I) -> P' (fun I => I)) -> Content (Acc v) P'.
Ltac solve_closure_聞く :=
 match goal with
   | [H1 : _聞く ?e, H2 : Content (Acc ?e) ?A |- Content (Acc ?e) ?B ]
     => apply closure_聞く with (v:=e)(P:=A)(P':=B)
 end.

(* privative adjectives *)
Parameter _former : (Entity -> Prop) -> Entity -> Prop.
Axiom privative_former : forall F : Entity -> Prop, forall x : Entity, (_former F x -> ~ (F x)).
Ltac solve_privative_former :=
  match goal with
    H : _former ?A ?t |- _
    => try apply privative_former with (F:= A)(x:= t) in H
  end.

Parameter _fake : (Entity -> Prop) -> Entity -> Prop.
Axiom privative_fake : forall F : Entity -> Prop, forall x : Entity, (_fake F x -> ~ (F x)).
Ltac solve_privative_fake :=
  match goal with
    H : _fake ?A ?t |- _
    => try apply privative_fake with (F:= A)(x:= t) in H
  end.

Parameter _一流 : (Entity -> Prop) -> Entity -> Prop.

Parameter _自称 : (Entity -> Prop) -> Entity -> Prop.
Axiom wouldbe : forall F G: Entity -> Prop, forall x : Entity, _自称 F x -> (F x -> G x) -> _自称 G x.
Ltac solve_closure_wouldbe :=
  match goal with
    H : _自称 ?A ?t |- _自称 _ _
    => try apply wouldbe with (F:= A); try apply H
  end.

(* intensional verbal modifiers *)
Parameter _ほぼ : (Event -> Prop) -> Event -> Prop.
Axiom anti_veridical_ほぼ : forall F : Event -> Prop, forall v : Event, (_ほぼ F v -> ~ (F v)).
Ltac solve_anti_veridical_ほぼ :=
  match goal with
    H : _ほぼ ?A ?t |- _
    => try apply anti_veridical_ほぼ with (F:= A)(v:= t) in H
  end.

Parameter _損ねる : (Event -> Prop) -> Event -> Prop.
Axiom anti_veridical_損ねる : forall F : Event -> Prop, forall v : Event, (_損ねる F v -> ~ (F v)).
Ltac solve_anti_veridical_損ねる :=
  match goal with
    H : _損ねる ?A ?t |- _
    => try apply anti_veridical_損ねる with (F:= A)(v:= t) in H
  end.

(* antonyms *)
Parameter _大きな : Entity -> Prop.
Parameter _小さな : Entity -> Prop.
Axiom antonym_大きな_小さな : forall x : Entity, _大きな x -> _小さな x -> False.
Ltac solve_antonym_大きな_小さな :=
  match goal with
    H1 : _大きな _, H2 : _小さな ?t |- False
  => try apply antonym_大きな_小さな with (x := t)
  end.

Parameter _おいしい : Event -> Prop.
Parameter _まずい : Event -> Prop.
Axiom antonym_おいしい_まずい : forall v : Event, _おいしい v -> _まずい v -> False.
Ltac solve_antonym_おいしい_まずい :=
  match goal with
    H1 : _おいしい _, H2 : _まずい ?e |- False
  => try apply antonym_おいしい_まずい with (v := e)
  end.

Parameter _開く : Event -> Prop.
Parameter _閉まる : Event -> Prop.
Axiom antonym_開く_閉まる : forall v : Event, _開く v -> _閉まる v -> False.
Ltac solve_antonym_開く_閉まる :=
  match goal with
    H1 : _開く ?e, H2 : _閉まる ?e |- _ 
  => try apply antonym_開く_閉まる with (v := e) in H1
  end.

(* causatives and benefactives *)
Parameter _せる : Event -> Prop.
Parameter _もらう : Event -> Prop.

Axiom causative1 : forall v : Event, forall x : Entity,
  _せる v -> Dat v = x -> Nom v = x.
Axiom causative2 : forall v : Event, forall x : Entity,
  _せる v -> Acc v = x -> Nom v = x.
Hint Resolve causative1 causative2.

Axiom benefactive : forall v : Event, forall x : Entity,
  _もらう v -> Dat v = x -> Nom v = x.
Hint Resolve benefactive.


(* Causative alternation *)
Parameter _破く : Event -> Prop.
Parameter _破れる : Event -> Prop.
Axiom causative_破く_破れる : forall v : Event,
  _破く v -> _破れる v /\ Nom v = Acc v.

Ltac solve_causative_破く_破れる :=
  match goal with
    | [ H1 : _破く ?e |- _ ]
     => apply causative_破く_破れる with (v := e) in H1
  end.

Parameter _閉める : Event -> Prop.
Axiom causative_閉める_閉まる : forall v : Event,
  _閉める v -> _閉まる v /\ Nom v = Acc v.

Ltac solve_causative_閉める_閉まる :=
  match goal with
    | [ H1 : _閉める ?e |- _ ]
     => apply causative_閉める_閉まる with (v := e) in H1
  end.


(* Preliminary tactics *)

Ltac apply_ent :=
  match goal with
    | [x : Entity, H : forall x : Entity, _ |- _]
     => apply H; clear H
  end.

Ltac eqlem_sub :=
  match goal with
    | [ H1: ?A ?t, H2: forall x, @?D x -> @?C x |- _ ]
     => match D with context[ A ]
         => assert(C t); try (apply H2 with (x:= t)); clear H2
    end
  end.

Axiom unique_role : forall v1 v2 : Event, Nom v1 = Nom v2 -> v1 = v2.
Ltac resolve_unique_role :=
  match goal with 
    H : Nom ?v1 = Nom ?v2 |- _
    => repeat apply unique_role in H
  end.

Ltac substitution :=
  match goal with
    | [H1 : _ = ?t |- _ ]
      => try repeat resolve_unique_role; try rewrite <- H1 in *; subst
    | [H1 : ?t = _ |- _ ]
      => try resolve_unique_role; try rewrite H1 in *; subst
  end.

Ltac exchange :=
  match goal with
    | [H1 : forall x, _, H2 : forall x, _ |- _]
     => generalize dependent H2
  end.

Ltac exchange_equality :=
  match goal with
    | [H1 : _ = _, H2: _ =  _ |- _]
     => generalize dependent H2
  end.

Ltac clear_pred :=
  match goal with
    | [H1 : ?F ?t, H2 : ?F ?u |- _ ]
     => clear H2
  end.

Ltac solve_false :=
  match goal with
    | [H : _ -> False |- False]
     => apply H
  end.

(* Main tactics *)

Ltac nltac_init :=
  try(intuition;
      try solve_false;
      firstorder;
      repeat subst;
      firstorder).

Ltac nltac_base := 
  try nltac_init;
  try (eauto; eexists; firstorder);
  try (subst; eauto; firstorder; try congruence).

Ltac nltac_axiom :=
 try first
   [solve_たしか |
    solve_本当 |
    solve_嘘 |
    solve_Poss |
    solve_疑う_思う |
    solve_成功 |
    solve_factive_見る |
    solve_factive_聞く |
    solve_privative_former |
    solve_privative_fake |
    solve_anti_veridical_ほぼ |
    solve_anti_veridical_損ねる |
    solve_causative_破く_破れる |
    solve_causative_閉める_閉まる |
    solve_antonym_大きな_小さな |
    solve_antonym_おいしい_まずい |
    solve_antonym_開く_閉まる
   ].

Ltac nltac_closure_axiom :=
 try first
   [solve_closure_見る |
    solve_closure_聞く |
    solve_closure_wouldbe
   ].

Ltac nltac_set :=
  repeat (nltac_init;
          try repeat substitution;
          try exchange_equality;
          try repeat substitution;  
          (* try apply_ent; *)
          try eqlem_sub).

Ltac nltac_set_exch :=
  repeat (nltac_init;
          try repeat substitution;
          try apply_ent;
          try exchange;
          try eqlem_sub).

Ltac nltac_final :=
  try solve [repeat nltac_base | clear_pred; repeat nltac_base].

Ltac nltac_prove :=
  try solve [nltac_set; nltac_final | nltac_set_exch; nltac_final].

Ltac solve_gq1 :=
  match goal with
    H : Most _ _ |- _
    => let H0 := fresh in
       try solve [         
          pose (H0 := H); eapply most_ex_import in H0; nltac_prove |
          pose (H0 := H); eapply most_consv in H0; eapply most_rightup; nltac_prove |
          pose (H0 := H); eapply most_consv in H0; nltac_prove |
          pose (H0 := H); eapply most_rightup in H0; nltac_prove ]
  end.

Ltac solve_gq2 :=
  match goal with
    H : Few _ |- _
    => let H0 := fresh in
       try solve [
          pose (H0 := H); eapply few_down in H0; nltac_prove ]
  end.

Ltac nltac :=
  try solve
    [nltac_prove |
     nltac_init; (solve_gq1 || solve_gq2) |
     nltac_set; try nltac_axiom; solve [nltac_final | nltac_prove] |
     nltac_set; nltac_base; try nltac_closure_axiom; solve [nltac_final | nltac_prove]
    ].
