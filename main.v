Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Declare Scope GSet_scope.
Delimit Scope GSet_scope with G.

CoInductive GSet := { ob :> Type ; hom : ob -> ob -> GSet }.

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



(* GSet indexed on another *)

CoInductive GSet_on (G : GSet) :=
  { ob_on :> G -> Type ; hom_on : forall a b, ob_on a -> ob_on b -> GSet_on (hom a b) }.

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

CoInductive statementAndre {B : GSet}{I : Type}(G : I -> GSet_on B) :=
  {
    pa_ob :
      forall (b1 b2 : B) i i'
             (g1 : G i b1)( g1' : G i' b1)
             (g2 : G i b2)( g2' : G i' b2),
      (hom_on g1 g2 ⇒[ id_Mor _] (hom_on g1' g2'))%GO ;
    pa_hom : forall (b1 b2 : B),
                    (* (g1 : G b1)(g2 : G b2), *)
        statementAndre (B := hom b1 b2)(I := {i : I & (G i b1 * G i b2)%type})
                       ( fun i => hom_on (fst (projT2 i)) (snd (projT2 i)))
  }.

(* In fact, only comp0 is needed *)
Definition whiskers (B : GSet)(compB : has_comp B)(b1 b2 b3 b4 : B)
           (bb1 : hom b1 b2)(bb2 : hom b3 b4) : 
  (hom b2 b3 ⇒ (hom b1 b4))%G .


CoFixpoint preuveAndreNext  {B : GSet}{I : Type }(G : I -> GSet_on B)
   (* (b1 b2 : B)(g1 : G b1)(g2 : G b2)  *)
       (m :       forall (b1 b2 : B) i i'
             (g1 : G i b1)( g1' : G i' b1)
             (g2 : G i b2)( g2' : G i' b2),
      (hom_on g1 g2 ⇒[ id_Mor _] (hom_on g1' g2'))%GO 
)
   (* (m : (hom_on g1 g2 ⇒[ id_Mor _] (hom_on g1' g2'))%GO) *)
   : statementAndre G (* (hom_on g1 g2) *).
split.
- assumption.
- intros.
  apply preuveAndreNext.
  cbn.
  intros bb1 bb2 [i [g1 g2]] [i' [g1' g2']].
  cbn.
  specialize (m b1 b2 i i' g1 g1' g2 g2').
  intros gg1 gg1' gg2 gg2'.
  assert (msuc := hom_on_mor m).
  specialize (msuc bb1 bb2 gg1 gg2).
  cbn in msuc.
  Set Printing Implicit.
  eapply @hom_on_mor in m.

(* correspond a un element sur le pullback? hmm, a moitie: on n'a pas les morphismes
puisque homb ne depend pas de obb
 *)
CoInductive bizarre {B : GSet}(G : GSet_on B) :=
  { obb :> B -> Type ;
     homb : forall (b b' : B)
             (g : G b)(g' : G b'),
         bizarre (B := hom b b')(hom_on g g')
  }.

(* Definition usual_stuff (p : forall {B : GSet}(G : GSet_on B) (H : bizarre G)) *)

CoInductive sectionb  {B : GSet}(G : GSet_on B) (H : bizarre G) :=
  {
    obbs : forall b,  H b ;
    hombs : forall b1 b2 g1 g2, sectionb (B := hom b1 b2) (G := hom_on g1 g2)
                                         (homb H g1 g2)

  }.

CoFixpoint contractibleb  {B : GSet}(G : GSet_on B) : bizarre G :=
  {| obb := fun b => G b ; homb := fun b1 b2 g1 g2 => contractibleb (B := hom b1 b2)(hom_on g1 g2) |}.


CoInductive has_compb {B : GSet}(G : GSet_on B){compB : has_comp B}(* {compG : has_comp_on G} *) (H : bizarre G) :=
  { compb0 : forall (b1 b2 b3 : B)(bb1 : hom b1 b2)(bb2 : hom b2 b3)
                     (g1 : G b1) (g2 : G b2)(g3 : G b3)
                     (gg1 : hom_on g1 g2 bb1)(gg2 : hom_on g2 g3 bb2),
      homb H g1 g2 bb1 ->
      homb H g2 g3 bb2 ->
      homb H g1 g3 (comp0 (bb1,bb2)) ;
    compbS : forall (b1 b2 : B)(g1 : G b1)(g2 : G b2),
        has_compb (B := hom b1 b2)(G := hom_on g1 g2) (compB := _)(* (compG := _) *)(homb H g1 g2)
  }.

CoFixpoint has_compb_contr {B : GSet}(G : GSet_on B){compB : has_comp B}{compG : has_comp_on G} :
  has_compb (contractibleb G).
split.
- intros until g3.
  cbn.
  intros gg1 gg2 gg1' gg2'.
  Abort.

CoInductive has_idb {B : GSet}(G : GSet_on B){idB : has_id B}{idG : has_id_on G}(H : bizarre G) :=
  {
    idb0 : forall b (g : G b), homb H g g (id0 b) ;
    idbS : forall b1 b2 (g1 : G b1)(g2 : G b2),
        has_idb (B := hom b1 b2)(G := hom_on g1 g2) (idB := _)(idG := _)(homb H g1 g2)
  }.


CoFixpoint has_idb_contr {B : GSet}(G : GSet_on B){idB : has_id B}{idG : has_id_on G} : has_idb (contractibleb G).
split.
- intros.
  cbn.
  apply idG.
- intros.
  apply has_idb_contr.
  Defined.


CoInductive X_onb {B : GSet}(X G : GSet_on B)(eta : (X ⇒[ id_Mor B] G)%GO) (P : bizarre G) :=
  { obX_onb : forall b (x : X b), P b ;
    homX_onb : forall (b1 b2 : B)(x1 : X b1)(x2 : X b2),
        X_onb (B := hom b1 b2)(X := hom_on x1 x2)(G := hom_on (g := G) _ _)
              (hom_on_mor eta x1 x2)
              (homb P (eta _ x1) (eta _ x2))
  }.


CoFixpoint X_on_contr {B : GSet}(X G : GSet_on B)(eta : (X ⇒[ id_Mor B] G)%GO) : X_onb eta (contractibleb G).
Proof.
  split.
  - apply eta.
  - cbn.
    intros.
    apply X_on_contr.
Defined.

Section universal.
Context (TX : GSet)(X : GSet_on TX).

Context { has_idTX : has_id TX } {has_compTX : has_comp TX} .

(* Z should be hProp, so that we don't need to check the equations *)
(* TODO: check on paper *)
Context (uniVTX : forall (G : GSet_on TX)
                         (etaG : @GSet_on_Mor TX TX (id_Mor TX) X G)
                         (compG : has_comp_on G)
                         (idG : has_id_on G)
            (Z : bizarre G),
            has_compb Z -> has_idb Z -> X_onb etaG Z -> sectionb Z ).

(* G = WX *)
Context (G : GSet_on TX)
                         (etaG : @GSet_on_Mor TX TX (id_Mor TX) X G)
                         (compG : has_comp_on G)
                         (cohG : has_coh G).
Lemma contractible_weak : sectionb (contractibleb G).
Proof.
  unshelve eapply (uniVTX _ _  has_idb_contr (X_on_contr etaG)).
