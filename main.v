Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive GSet := { ob :> Type ; hom : ob -> ob -> GSet }.

CoInductive GSet_Mor (G H : GSet) :=
  { ob_mor :> G -> H ;
    hom_mor : forall a b, GSet_Mor (hom a b) (hom (ob_mor a)(ob_mor b)) }.

CoFixpoint  GSet_prod (G H : GSet) : GSet :=
  {| ob := G * H ; hom := fun a b => GSet_prod (hom (fst a)(fst b)) (hom (snd a)(snd b)) |}.

Infix "*" := GSet_prod : GSet_scope.
Infix "⇒" := GSet_Mor (at level 10) : GSet_scope .
Delimit Scope GSet_scope with G.

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




(* Is it contractible *)
CoInductive is_contractible {B : GSet}(G : GSet_on B) :=
 {
    contr0 :     forall  (b1 : B)(b2 : B)(g1 : G b1)(g2 : G b2)
                    (b12 : hom b1 b2) , hom_on g1 g2 b12 ;
    contrS : forall (b1 b2 : B) (g1 : G b1)(g2 : G b2),
      is_contractible (B := hom b1 b2)(hom_on g1 g2)
 }.

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

