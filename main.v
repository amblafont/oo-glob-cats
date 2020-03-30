Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require  Coq.Vectors.Fin.
Declare Scope GSet_scope.
Delimit Scope GSet_scope with G.

CoInductive GSet := { ob :> Type ; hom : ob -> ob -> GSet }.

CoFixpoint empty_GSet : GSet := {| ob := False ; hom := fun x y => empty_GSet |} .
Definition point : GSet := {| ob := unit ; hom := fun x y => empty_GSet |}.

(* Definition GSet_if_true (prop : Type)(G : GSet) : GSet := *)
(*   {| ob := (prop * G) ; hom := fun x y => hom (snd x)(snd y)|}. *)

(* Let us make S1 *)
CoFixpoint make_S1 (prop : Type)(availables : Type) : GSet :=
 {| ob := (prop * (availables -> nat))%type ;
           hom := fun x y =>
                    make_S1 (forall a,  snd x a = snd y a) {a : availables & Fin.t (snd x a)} |} .

CoInductive give_me_gsets (G : GSet) := { obg : G -> GSet ;
                                           homg : forall (x y : G), give_me_gsets (hom x y)}.

Fixpoint make_list (A : Type)(n : nat)(a : A) : list A :=
  match n with
    0 => nil
  | S n => a :: make_list n a
  end.

CoFixpoint make_S1_to_GSet (prop : Type)(availables : Type)
           (mk_gsets :  (availables -> list GSet) -> GSet)
   : give_me_gsets (make_S1 prop availables).
refine {| obg := fun x => mk_gsets (fun a => make_list (snd (x : make_S1 prop availables) a) point) ;
          homg := fun x y => _ |}.
cbn.
apply make_S1_to_GSet.
cbn in x,y.
intros gs.
(* en fait, je devrais avoir un truc du genre list^n GSet -> GSetm en fait il suffit d'avoir list GSet -> list GSet *)
apply (mk_gsets ).
intro a.
(*
apply (mk_gsets (snd x)).
intros a p.
            mk_gsets (fun _ => point) |}.
*)
Abort.

Definition S1_plus := make_S1 unit unit.

(* GSet indexed on another *)

CoInductive GSet_on (G : GSet) :=
  { ob_on :> G -> Type ; hom_on : forall a b, ob_on a -> ob_on b -> GSet_on (hom a b) }.

Definition collection := GSet_on S1.

Definition prod_coll (a b : collection) : collection.

CoInductive GSet_Mor (G H : GSet) :=
  { ob_mor :> G -> H ;
    hom_mor : forall a b, GSet_Mor (hom a b) (hom (ob_mor a)(ob_mor b)) }.

Infix "⇒" := GSet_Mor (at level 10) : GSet_scope .

CoFixpoint comp_Mor {G H T : GSet}(f : (G ⇒ H)%G) (g : (H ⇒ T)%G) : (G ⇒ T)%G :=
  {| ob_mor := fun x => g (f x) ;
     hom_mor := fun a b => comp_Mor (hom_mor f a b)(hom_mor g (f a) (f b))
  |}.

Infix "∘" := comp_Mor (at level 10) : GSet_scope .

CoFixpoint id_Mor (G : GSet) : (G ⇒ G)%G :=
  {| ob_mor := fun x => x ;
     hom_mor := fun a b => id_Mor _ |}.

CoFixpoint  GSet_prod (G H : GSet) : GSet :=
  {| ob := G * H ; hom := fun a b => GSet_prod (hom (fst a)(fst b)) (hom (snd a)(snd b)) |}.

Infix "*" := GSet_prod : GSet_scope.

CoFixpoint prod_on_mor {A B A' B' : GSet}(f : (A ⇒ A')%G)(g : (B ⇒ B')%G) :
  ((A * B) ⇒ (A' * B'))%G :=
  {| ob_mor := fun (x : ob (A * B)%G) => (f (fst x), g (snd x)) : ob (A' * B')%G ;
     hom_mor := fun a b => prod_on_mor (hom_mor f (fst a) (fst b))(hom_mor g (snd a) (snd b))
    |}.

Infix "*#" := prod_on_mor (at level 10) : GSet_scope .

CoInductive has_comp (G : GSet) :=
  { comp0 : forall (a b c : G),  ((hom a b * hom b c) ⇒ (hom a c))%G ;
    compS : forall (g g' : G), has_comp (hom g g')
  }.

Existing Class has_comp.
Existing Instance compS.

Arguments comp0 [G] {_} [a] [b] [c].

CoInductive has_id (G : GSet) :=
  { id0 : forall (g : G) , hom g g ;
    idS : forall (g g' : G), has_id (hom g g') }.

Arguments id0 [G] {_} g.

Existing Class has_id.
Existing Instance idS.


CoInductive id_comp (G : GSet) {compG : has_comp G} {idG : has_id G} :=
  { idl_comp0 : forall (g g' : G)(f : hom (g := G) g g') , comp0 (f , (id0 g')) = f ;
    idr_comp0 : forall (g g' : G)(f : hom (g := G) g g') , comp0 ((id0 g) , f ) = f ;
    id_compS : forall (g g' : G) , id_comp (G := hom g g')(compG := _)(idG := _)
  }.

Arguments id_comp G {compG} {idG}.

Existing Class id_comp.
Existing Instance id_compS.




CoInductive GSet_on_Mor {G1 : GSet}{G2 : GSet}
            (ff : GSet_Mor G1 G2)
            (A : GSet_on G1)(B : GSet_on G2) :=
  { ob_on_mor :> forall g, A g -> B (ff g) ;
    hom_on_mor : forall (g g' : G1) (a : A g) (b : A g'),
        (* ob_on_mor a -> ob_on_mor b -> *)
        GSet_on_Mor (G1 := hom g g')(G2 := hom (ff g)(ff g'))
                    (hom_mor ff g g' )
                    (hom_on a b)
                    (hom_on (ob_on_mor a)(ob_on_mor b))}.

(* CoInductive GSet_on_Mor {G : GSet}(A B : GSet_on G) := *)
(*   { ob_on_mor :> forall g, A g -> B g ; hom_on_mor : forall (g g' : G) (a : A g) (b : A g'), *)
(*         (* ob_on_mor a -> ob_on_mor b -> *) *)
(*                                                             GSet_on_Mor (G := (hom g g')) *)
(*                                                                         (hom_on a b) *)
(*                                                                         (hom_on (ob_on_mor a)(ob_on_mor b))}. *)

CoFixpoint  GSet_on_prod {B1 B2 : GSet} (G : GSet_on B1)(H : GSet_on B2)
  : GSet_on ((B1 * B2)%G) :=
  {| ob_on := fun (g:(B1 * B2)%G) => (G (fst g) * H (snd g))%type ;
     hom_on := fun g g' a b => GSet_on_prod (hom_on (fst a)(fst b))(hom_on (snd a)(snd b)) |}.

(* CoFixpoint  GSet_on_prod {B : GSet} (G H : GSet_on B) : GSet_on B := *)
(*   {| ob_on := fun g => (G g * H g)%type ; *)
(*      hom_on := fun g g' a b => GSet_on_prod (hom_on (fst a)(fst b))(hom_on (snd a)(snd b)) |}. *)


Infix "*" := GSet_on_prod : GSet_on_scope.
Notation "X ⇒[ f ] Y" := (GSet_on_Mor f X Y) (at level 10) : GSet_on_scope .
Delimit Scope GSet_on_scope with GO.

(* bizarre que je n'ai pas besoin de composition en dessous... *)
CoInductive has_comp_on {B : GSet}{compB : has_comp B} (G : GSet_on B) :=
  { comp0_on :
      forall (b1 b2 b3 : B) (g1 : G b1)(g2 : G b2)(g3 : G b3),  ((hom_on g1 g2 * hom_on g2 g3) ⇒[ comp0 ] (hom_on g1 g3))%GO ;
    compS_on : forall (g g' : B)(a : G g)(b : G g'),
        has_comp_on (B := hom g g')(compB := _) (hom_on a b)
  }.
(* CoInductive has_comp_on {B : GSet}(G : GSet_on B) := *)
(*   { comp0_on : forall g (a b c : G g),  ((hom_on a b * hom_on b c) ⇒ (hom_on a c))%GO ; *)
(*     compS_on : forall (g g' : B)(a : G g)(b : G g'), has_comp_on (B := hom g g') (hom_on a b) *)
(*   }. *)


Existing Class has_comp_on.
Existing Instance compS_on.

CoInductive has_id_on {B : GSet}{idB : has_id B}(G : GSet_on B) :=
  { id0_on : forall b (g : G b),  hom_on g g (id0 b) ;
    idS_on : forall b b' (g : G b)(g' : G b'), has_id_on (B := hom b b')(idB := _)(hom_on g g') 
  }.

Existing Class has_id_on.
Existing Instance idS_on.


CoInductive has_coh {B : GSet}{idB : has_id B}(G : GSet_on B) :=
  { coh0 : forall (b : B)(g g' : G b), hom_on g g' (id0 b) ;
    cohS : forall (b b' : B)(g : G b)(g' : G b'), has_coh (B := hom b b')(idB := _)(hom_on g g' );
  }.

Arguments coh0 [B] {idB}[G]{_}[_].

Existing Class has_coh.
Existing Instance cohS.


CoFixpoint has_coh_has_id {B : GSet}{idB : has_id B}(G : GSet_on B)(cohG : has_coh G) : has_id_on G :=
  {| id0_on := fun b g => coh0 g g ;
     idS_on := fun b b' g g' => has_coh_has_id (G := (hom_on g g')) _
  |}.
Existing Instance has_coh_has_id.




(* Is it contractible *)
(*
CoInductive is_contractible {B : GSet}(G : GSet_on B) :=
 {
    contr0 :     forall  (b1 : B)(b2 : B)(g1 : G b1)(g2 : G b2)
                    (b12 : hom b1 b2) , hom_on g1 g2 b12 ;
    contrS : forall (b1 b2 : B) (g1 : G b1)(g2 : G b2),
      is_contractible (B := hom b1 b2)(hom_on g1 g2)
 }.
*)


(*
CoFixpoint section_is_contractible {B : GSet}(G : GSet_on B) (sec : section G) :
  is_contractible G.
Proof.
  split.
  - intros.
    assert (h := homs sec).
    apply (obs (h _ _ _ _)).
  - intros.
    apply section_is_contractible.
    apply (homs sec).
Defined.


(* Alternative definition of contractibility *)
Definition is_contractible_alt {B : GSet}(G : GSet_on B) :=
  forall (b1 b2 : B)(g1 : G b1)(g2 : G b2), section (hom_on (g := G) g1 g2).
(* a stronger statement *)
Definition fully_contractible {B : GSet}(G : GSet_on B) :=
  section G.
*)


(*
CoFixpoint is_contractible_alt_implies_contractible {B : GSet}
           (b1 b2 : B)(G : GSet_on B)
           (g1 : G b1)(g2 : G b2)
           (* Apparently, I only need it at the next level... (not for ob) *)
           (sec : section (is_contractible'  g1 g2)) :
  (* is_contractible G. *)
is_contractible (hom_on g1 g2).
Proof.
  split.
  - intros c1 c2 h1 h2 d.
    assert (H := homs sec).
    specialize (H c1 c2 h1 h2).
    apply (obs H).
  - intros c1 c2 h1 h2.
    apply is_contractible'_implies_contractible.
    apply (homs sec).
Defined.
*)

(* Hypothèses nécessaires pour montrer la contractibilité *)
Class has_all_necessary_hyp {B : GSet}(G : GSet_on B) :=
{ has_idB :> has_id B ;
  has_compB :> has_comp B ;
  has_compG :> has_comp_on G ;
  has_cohG :> has_coh G ;
  (* + une hypothèse (manquante) qui dit que les morphismes sont des compositions
     de flèches.
   *)
}.

Instance passer_au_niveau_sup
        {B : GSet}(G : GSet_on B) (is_nice : has_all_necessary_hyp G) 
        (b1 b2 : B) (g1 : G b1)(g2 : G b2):
           has_all_necessary_hyp (B := hom b1 b2) (hom_on g1 g2).
Proof.
  unshelve esplit; eauto with typeclass_instances.
Qed.


(* Universal property of the free strict omega groupoid
 any morphism X -> Y over TX has a section
 *)
(* TODO: définir les équations d'associativité

Associativité: facile
Neutralité de id: facile
mais interchange??
 *)

Section interchange.
  Context (B : GSet) {has_compB : has_comp B}.
  Context {x y z : B}
           (a b c : hom x y) 
           (a' b' c' : hom y z).

  Definition interchange_type :=
        (((hom a b * hom b c) * (hom a'  b' * hom b' c'))
          ⇒ (hom (comp0 (a , a'))(comp0 (c , c'))))%G.

  Definition interchange_mor1 :
        (((hom a b * hom b c) * (hom a'  b' * hom b' c'))
          ⇒ (hom (comp0 (a , a'))(comp0 (c , c'))))%G :=
     ((comp0 *# comp0)
        ∘ (hom_mor
             (comp0 (G := B) (a := x)(b := y)(c := z))
             (a , a') (c , c')))%G.
  Definition interchange_mor2 : 
        (((hom a b * hom a' b') * (hom b  c * hom b' c'))
          ⇒ (hom (comp0 (a , a'))(comp0 (c , c'))))%G.
    refine (((
                (hom_mor
             (comp0 (G := B) (a := x)(b := y)(c := z))
             (a , a') (b , b'))
                  *#
                (hom_mor
             (comp0 (G := B) (a := x)(b := y)(c := z))
             (b , b') (c , c'))
              ) ∘ _
            )%G).
    eapply compS.
    exact has_compB.
    Defined.

  End interchange.


(* TODO: squasher *)
CoInductive contractible {B : GSet}(G : GSet_on B) :=
  { obc :> forall b, G b ;
    homc : forall (b b' : B)
             (g : G b)(g' : G b'),
         contractible (B := hom b b')(hom_on g g')
  }.


(* CoFixpoint is_contractible' {B : GSet} *)
(*            (b1 b2 : B) *)
(*            (* (G : GSet_on B) *) *)
(*            (* (g1 : G b1)(g2 : G b2) *) *)
(*   : GSet_on (hom b1 b2) :=  (* hom_on G g1 g2 *) *)
(*   {| *)
(*     ob_on := fun (z : hom b1 b2) =>  *)
(*                  forall (G : GSet_on B) *)
(*                  (g1 : G b1) (g2 : G b2) , *)
(*                  has_comp_on G -> has_coh G -> *)
(*                                    (ob_on (hom_on g1 g2) z); *)
(*     hom_on := fun (z1 z2 : hom b1 b2) h1 h2 => *)
(*                  is_contractible' h1 h2 *)
(*   |}. *)

(* A generalization of binary product *)
CoFixpoint prods_GSet_on {B : GSet }{I : Type}(Gs : I -> GSet_on B) : GSet_on B :=
  {| ob_on := fun b => forall i, Gs i b ;
     hom_on := fun b b' p p' =>
                 prods_GSet_on
                   (fun i => hom_on  (p i) (p' i))
  |}.

CoInductive section {B : GSet}(G : GSet_on B) :=
  { obs :> forall b, G b ;
    homs : forall (b b' : B)
             (g := obs b)(g' := obs b'),
         section (B := hom b b')(hom_on g g')
  }.

CoInductive fami_on {B : GSet} (G : GSet_on B) :=
  { obfa:> B -> Type ;
     (* If : B -> Type ; *)
     homfa : forall (b1 b2 : B) (g1 : G b1)  (g2 : G b2) ,
                            @fami_on (hom b1 b2) (hom_on g1 g2)
  }.
CoInductive fami_section {B : GSet} (H : GSet_on B)(G : fami_on H) :=
  { obfas : forall b, G b;
    homfas : forall b1 b2  i1 i2 ,
        @fami_section
          (hom b1 b2)
          (hom_on (g := H) i1 i2)
          (homfa G i1 i2)
  }.

CoFixpoint contractible_fami (B : GSet) (G : GSet_on B) : fami_on G
  :=
   {| obfa := fun (z : B) => (ob_on G z);
      homfa := fun b b' i1 i2 =>
                contractible_fami (B := hom (g := B) b b')
                                    (hom_on (g := G) i1 i2)
         |}.

CoFixpoint contractible_fami_contr (B : GSet)(G : GSet_on B)
      (sec : fami_section (contractible_fami G)) : contractible G.
Proof.
  split.
  - apply sec.
  - intros.
    apply contractible_fami_contr.
    assert (h := homfas sec).
    unshelve eapply h.
Defined.

CoFixpoint prods_fami_on {B : GSet }{I : Type}(H : I ->  GSet_on B)
           (Gs : forall i, fami_on (H i)) :
  fami_on (prods_GSet_on H).
  unshelve refine (
  {| obfa := fun b => forall i, Gs i b ;
     (* If := fun b => *)
     (*         (* { i & If i b } ; *) *)
     (*         forall i, If i b ; *)
     homfa := fun b b' i1 i2 => _
               (* prods_fam_on' _ _ _  *)
                             (* (fun i => homf'  (p i) (p' i) (i1 _) (i2 _)) *)
  |}).
  (* cbn in p, p'. *)
  apply prods_fami_on.
  - intro i; apply (@homfa _ _ (Gs i)); auto.
    Defined.


CoFixpoint fami_GSet_on {B : GSet}(H : GSet_on B)
           (G :  fami_on H) : GSet_on B.
Proof.
  refine ({| ob_on := fun b => G  b |}).
  intros b1 b2 g1 g2.
  unshelve eapply fami_GSet_on.
  + shelve.
  + assert (h := @homfa _ _ G b1 b2 ).
    eapply (prods_fami_on (I := H b1 * H b2)%type).
    exact (fun i => h (fst i)(snd i)).
Defined.

CoFixpoint fami_GSet_on_I {B : GSet}{I : Type}(H :  I -> GSet_on B)
           (G : forall i, fami_on (H i)) : GSet_on B.
Proof.
  refine ({| ob_on := fun b => forall i, G i b |}).
  intros b1 b2 g1 g2.
  assert (h := fun i => @homfa _ _ (G i) b1 b2 ).
  eapply (fami_GSet_on_I _ ({ i : I & (H i b1 * H i b2)%type})).
  + exact (fun ih12 => h (projT1 ih12) (fst (projT2 ih12))(snd (projT2 ih12))).
Defined.

CoFixpoint yop' {B : GSet}{I J : Type}(ff : J -> I)
           (H : I -> GSet_on B)(G : forall i, fami_on (H i))
  (sec : section
        (fami_GSet_on_I G) 
           (* (fun i : I =>  *)
           (*  homfa (G (projT1 ih12)) (fst (projT2 ih12)) (snd (projT2 ih12)))) *))
  : section (fami_GSet_on_I (fun j : J => G (ff j))).
Proof.
  unshelve esplit.
  - cbn.
    intros.
    apply sec.
  - cbn.
    intros b b'.
    cbn.
    assert (h := homs sec b b').
    cbn in h.
    revert h.
    specialize (yop' (hom b b') {i : I & (H i b * H i b')%type} {i : J & (H (ff i) b * H (ff i) b')%type}).
    specialize (yop' (fun i12 => existT _ (ff (projT1 i12)) (projT2 i12)  )).
    set (G' :=
           (fun ih12 : {i : I & (H i b * H i b')%type} =>
              homfa (G (projT1 ih12)) (fst (projT2 ih12)) (snd (projT2 ih12)))).

    unshelve eset (H' := _ : ( {i : I & (H i b * H i b')%type} -> GSet_on (hom b b'))).
    apply yop'.
Defined.

CoFixpoint fami_gset_section_gset_I {B : GSet}{I : Type}
           (H : I -> GSet_on B)(G : forall i, fami_on (H i))
  (sec : section (fami_GSet_on_I (H := H) G)) : fami_section (prods_fami_on G).
Proof.
  split.
  - intro b.
    cbn.
    apply sec.
  - intros b1 b2 i1 i2.
    cbn.
    apply fami_gset_section_gset_I.
    assert (h := @homs _  _ sec b1 b2).
    cbn zeta in h.
    cbn in h.
    revert h.
    eassert (h := yop' (B := hom b1 b2)
                       (fun i : I => existT _ i (i1 i, i2 i) )
            ).
    apply  h.
Defined.

Section contractible.
Context (TX : GSet)(X : GSet_on TX).

Context { has_idTX : has_id TX } {has_compTX : has_comp TX} .

(* Z should be hProp, so that we don't need to check the equations *)
Context (uniVTX : forall (Z : GSet_on TX)
                    (h: @GSet_on_Mor TX TX (id_Mor TX) X Z),
            has_comp_on Z -> has_id_on Z -> section Z ).

(* autre principe de recurrence (cf mail) *)
Section nouveau_principe.
  Context (Z : forall (t1 t2 : TX), GSet_on (hom t1 t2)).
  Context (morZ : forall (t1 t2 : TX)(x1 : X t1)(x2 : X t2),
              GSet_on_Mor
                                    (* (hom t1 t2)(hom t1 t2) *)
                                    (id_Mor (hom t1 t2))
                                            (hom_on x1 x2) (Z t1 t2)
          ).
  Context (compZ : forall t1 t2, has_comp_on (Z t1 t2))
          (comp0Z : forall t1 t2 t3, ((Z t1 t2 * Z t2 t3) ⇒[ comp0] (Z t1 t3))%GO)
          (idZ : forall t1 t2, has_id_on (Z t1 t2))
          (id0Z : forall t, Z t t (id0 t)).

  Definition Zup : GSet_on TX :=
    {|
      ob_on := fun _ => unit ;
      hom_on := fun t1 t2 _ _ => Z t1 t2
    |}.

  Lemma section_Zup : section Zup.
  Proof.
    apply uniVTX.
    - exact {| ob_on_mor := fun  _ _ => (tt : Zup (id_Mor TX _)) ;
                         hom_on_mor := morZ
                      |}.
    - split.
      + cbn.
        intros.
        apply comp0Z.
      + cbn.
        intros.
        apply compZ.
    - split.
      + intros.
        apply id0Z.
      + intros.
        apply idZ.
        Defined.

  Lemma section_dep (t1 t2 : TX) : section (Z t1 t2).
    apply (homs (section_Zup)).
  Defined.
  End nouveau_principe.

CoInductive GSet_on_on {B : GSet}(G : GSet_on B) :=
  { ob_on_on :> forall b, G b -> Type ;
    hom_on_on : forall a b (g1 : G a) (g2 : G b) ,
                  ob_on_on g1 -> ob_on_on g2 ->
                  GSet_on_on (B := hom a b)(hom_on (g := G) g1 g2) }.

CoFixpoint Pi {B : GSet}{H : GSet_on B}(G : GSet_on_on H) : GSet_on B.
refine ({| ob_on := fun b => forall (h : H b), G b h ;
           hom_on := fun b1 b2 h1 h2 => _
        |}).
cbn in h1, h2.
unshelve eapply Pi.
Abort.

CoFixpoint PiI {B : GSet}{I : Type}
           {H : I -> GSet_on B}(G : forall i, GSet_on_on (H i)) : GSet_on B.
refine ({| ob_on := fun b => forall i (h : H i b), G i b h ;
           hom_on := fun b1 b2 h1 h2 =>
                       PiI _ ({ i : I & (H i b1 * H i b2)%type})
                           (fun i12 => hom_on
                                      (fst (projT2 i12))
                                      (snd (projT2 i12))
                           )
                           _
        |}).
intro i12.
cbn in h1,h2.
eapply hom_on_on.
Abort.
exact (hom_on)



(* Goal: prove that WX is fully contractible on TX *)

(* Lemma contractibleWX : contractible WX. *)
  (*
Lemma fully_contractibleWX : fully_contractible WX.
Proof.
  apply uniVTX.
*)


(* Zut, je ne peux pas hprop-ité, je vais etre obligé de montrer des équations.

Ah si, en squashant g1 : || G b1 || et || G b2 ||
Mais alors, ne vais-je point être embté pour définir || ob_on (hom_on g1 g2) z || ?
non, car je peux désquasher g1 g2, car hProp est lui même hProp.

Et mais, en fait, is_contractible g1 g2 = hom_on G g1 g2
(le con!)

Faudrait juste squasher G
 *)

CoFixpoint is_contractible' (B : GSet)
           {compB : has_comp B}
           {idB : has_id B}
  : GSet_on B :=  (* hom_on G g1 g2 *)
  {|
    ob_on := fun (z : B) => 
               forall (G : GSet_on B)
                 (Y : GSet_on B),
                 (Y ⇒[ id_Mor B] G)%GO ->

                 (* (g1 : G b1) (g2 : G b2) , *)
                 has_comp_on G -> has_coh G ->
                                   (ob_on G z);
    hom_on := fun (z1 z2 : B) h1 h2 =>
                @is_contractible' (hom (g := B) z1 z2)
                                  (compS compB z1 z2 )
                                  _
  |}.


CoFixpoint sec_mor 
  (B : GSet)
  (G : GSet_on B)
  (* (sec : section (famGSet_to_GSet_on (is_contractible_fam G))) *)
  (b  b' : B)
  (g : G b)
  (g' : G b'):
        (famGSet_to_GSet_on
           (prods_fam_on
              (fun f : (G b * G b') =>
                 is_contractible_fam (hom_on (fst f) (snd f)))) ⇒[ id_Mor _ ]
           (famGSet_to_GSet_on (is_contractible_fam (hom_on g g')))
        )%GO.
  Proof.
    unshelve esplit.
    - intro b12.
      cbn.
      intro h.
      exact (h (_ , _)).
    - intros c c' f f'.
      cbn.
  Abort.

CoFixpoint is_contractible_fam_sec_contr 
           (B : GSet) (G : GSet_on B)
           (sec : section (famGSet_to_GSet_on (is_contractible_fam G))) :
  contractible G.
Proof.
  split.
  - apply (obs sec).
  - intros b b' g g'.
    apply is_contractible_fam_sec_contr.
    assert (h := ( (homs sec) b b')).
    revert h.
    cbn zeta.
    cbn.
    clear sec.
    Set Printing Implicit.
    Set Printing All.
    cbn delta in h. 
    cbn in h.
    cbn.
    apply h.


(*
CoFixpoint is_contractible2 (B : GSet) (G : GSet_on B)
  : GSet_on B :=  
  {|
    ob_on := fun (z : B) => (ob_on G z);
    hom_on := fun (z1 z2 : B) _ _ =>
                prods_GSet_on (I := G z1 * G z2)
                              (fun g12 => @is_contractible2
                                         (hom z1 z2)
                                         (hom_on (g := G) (fst g12)(snd g12))
                              )
  |}.
*)

Arguments is_contractible' B {_} {_}.

CoFixpoint is_contractible'_contractible
           (TX' : GSet){compTX : has_comp TX'}{idTX : has_id TX'}
           (X' : GSet_on TX')
   (WX' : GSet_on TX')
        (ηW: @GSet_on_Mor TX' TX' (id_Mor TX') X' WX')
        (compWX' : has_comp_on WX')
        (cohWX' : has_coh WX')
  : section (is_contractible' TX') -> contractible WX'.
Proof.
  intro sec.
  split.
  - intro b.
    eapply (obs sec) ; try assumption.
    exact ηW.
  -  intros s1 s2 w1 w2.
      eapply is_contractible'_contractible; eauto with typeclass_instances.
      apply (homs sec).
Defined.

Lemma X_ctr' : (X ⇒[ id_Mor TX] (is_contractible' TX))%GO.
Proof.
  unshelve esplit.
  - intros s x.
    cbn.

Lemma sec_is_contr' : section (is_contractible' TX).
Proof.
  apply uniVTX.
     (* + exact (hom_on w1 w2). *)
     + apply (hom_on_mor (ff := ηW)).
     assert (h := is_contractible'_contractible).
     specialize (h (hom_on w1 w2)).
     apply is_contractible'_contractible.
     Guarded.
     ; eauto with typeclass_instances.
Defined.


(* the weak omega *)
Context (WX : GSet_on TX)
        (ηW: @GSet_on_Mor TX TX (id_Mor TX) X WX)
        (compWX : has_comp_on WX)
        (cohWX : has_coh WX).
CoFixpoint is_contractible' {B : GSet}
           (b1 b2 : B)
           (* (G : GSet_on B) *)
           (* (g1 : G b1)(g2 : G b2) *)
  : GSet_on (hom b1 b2) :=  (* hom_on G g1 g2 *)
  {|
    ob_on := fun (z : hom b1 b2) => 
                 forall (G : GSet_on B)
                 (g1 : G b1) (g2 : G b2) ,
                 has_comp_on G -> has_coh G ->
                                   (ob_on (hom_on g1 g2) z);
    hom_on := fun (z1 z2 : hom b1 b2) h1 h2 =>
                 is_contractible' h1 h2
  |}.


(* Goal: prove is_contractible WX *)
Definition Z : GSet_on TX :=
  {| ob_on := fun a => WX a ;
     hom_on :=  fun s1 s2 w1 w2 =>
                  @is_contractible' TX s1 s2 WX w1 w2
  |}.

Lemma ce_quon_veut : section Z -> is_contractible WX.
Proof.
  intro sec.
  split.
  - intros s1 s2 w1 w2 s12.
    assert (h := homs sec (b := s1) (b' := s2) w1 w2 ).
    apply (obs h).
  - intros s1 s2 w1 w2.
    apply is_contractible'_implies_contractible.
    apply (homs sec).
Defined.

CoFixpoint X_Zfix TX' (X' : GSet_on TX') (WX' : GSet_on TX')
           (ηW' : (X' ⇒[ id_Mor TX'] WX')%GO)
   (g g' : TX') (a : X' g) (b : X' g'):
  ((hom_on a b) ⇒[ id_Mor (hom g g')] (is_contractible' (ηW' g a) (ηW' g' b)))%GO.
Proof.
  unshelve refine ({|
                      ob_on_mor := fun s x => _
           |}).
  - cbn.
    assert (h := hom_on_mor ηW').
    eassert (h' :=ob_on_mor (h _ _ _ _)).
    apply h'.
    assumption.
  - intros.
    apply X_Zfix.
Defined.

(* We are left with proving section Z using uniVTX *)

Definition X_Z : (X ⇒[ id_Mor TX] Z)%GO :=
   {| ob_on_mor := fun s x => (ob_on_mor ηW x :   Z (id_Mor TX s)) ;
             hom_on_mor :=  fun s1 s2 x1 x2 =>  X_Zfix ηW x1 x2
           |}.

(* Lemma  *)
(*   (b1, b2, b3 : TX) *)
(*   (g1 : WX b1) *)
(*   (g2 : WX b2) *)
(*   (g3 : WX b3) *)
(*   (h : ((hom_on g1 g2 * hom_on g2 g3) ⇒[ comp0] (hom_on g1 g3))%GO) *)
Lemma compZ : has_comp_on Z.
  refine (
   {| comp0_on := _ ;
               compS_on := _
           |}).
  - intros.
    cbn in g1 , g2, g3.
    assert (h := comp0_on compWX  g1 g2 g3).
    apply h.
    cbn.
    apply comp0_on.

Lemma secZ : section Z.
Proof.
  apply uniVTX.
  - exact X_Z.
  - exact X_Z.

  

(* On va supposer que Z est hprop, comme ça pas besoin de vérifier
les équations *)
Record charTX (TX : GSet)(X : GSet_on TX) :=
  { has_idTX :> has_id TX ;
  has_compTX :> has_comp TX ;
  (* has_eqTX :> has_ *)
  univTX : forall (Z : GSet_on TX)
             (h: @GSet_on_Mor TX TX (id_Mor TX) X Z), has_comp_on Z ->
      section Z }.
