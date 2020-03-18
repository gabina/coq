(* Bianchi, Gabina Luz - Parcial 1 *)

(*Ejercicio 1*)
Section Problema1.
Variables L O I C : Prop.
Definition R1 := (L -> O) /\ (I -> C). (* Si era leal, habrìa obedecido las órdenes, y si era inteligente, las habría comprendido*)
Definition R2 := ~ O \/ ~ C. (* O el general desobedeció las órdenes o no las comprendió*)
Definition Conclusion :=  ~ L \/ ~ I. (*el general era desleal o no era inteligente*)


Variable p q : Prop.
Lemma contra :forall p q : Prop, (p -> q) -> (~q -> ~p).
Proof.
intros.
unfold not.
intro.
absurd q0.
assumption.
apply H.
assumption. 
Qed.

Lemma ej1: (R1 /\ R2) -> Conclusion.
Proof.
unfold R1.
unfold R2.
unfold Conclusion.
intros.
elim H; intros.
elim H0; intros.
elim H1; intros.
left.
apply (contra L O H2).
assumption.
right.
apply (contra I C H3).
assumption.
Qed.

End Problema1.

(*Ejercicio 2*)
Section Problema2.
Require Import Classical.
Variable C : Set.
Variable P : C -> C -> Prop.
Lemma lema2 : (exists x : C, (exists y : C, P x y)) \/ ~(exists x : C, P x x).
Proof.
elim (classic (exists x : C, P x x)); intros.
left.
elim H.
intros.
(exists x).
(exists x).
assumption.
right.
assumption.
Qed.
End Problema2.

(*Ejercicio 3*)
Section Problema3.
Variable U : Set.
Variable a : U.
Variables P Q R T : U -> Prop.


Lemma Ej3_1 : (forall x : U, P x -> Q x) -> P a -> Q a.
Proof.
exact (fun (H : forall x : U, P x -> Q x) X => H a X).
Qed.
Lemma Ej3_2 : (forall x : U, P x -> Q x) -> (forall x : U, Q x -> R x) ->
forall x : U, P x -> R x.
Proof.
intros.
exact (H0 x (H x H1)).
Qed.

Lemma L3_3: (forall x:U, Q x) \/ (forall y:U, T y) -> forall z:U, Q z \/ T z.
Proof.
intros;elim H; intros; [left | right]; apply H0.
Qed.

End Problema3.


(*Ejercicio 4*)

Section Problema4.

Parameter ABnat : forall n : nat, Set.
Parameter ABnull : ABnat O.
Parameter ABadd : forall (n m : nat), nat -> ABnat n -> ABnat m -> ABnat (n + m + 1).
Check ABadd.

Definition AB1 := ABadd O 0 7 ABnull ABnull. (* Árbol de un único nodo con valor 7*)
Check AB1.
Definition AB2 := ABadd 1 0 8 AB1 ABnull. (*Árbol con un 8 en su raíz y un 7 como hijo izquierdo*)
Check AB2.
Definition AB3 := ABadd 2 0 9 AB2 ABnull. (*Árbol pedido*)
Check AB3.

Parameter ABG : forall (X: Set) (n : nat), Set.
Parameter ABGnull : forall X : Set, ABG X O.
Parameter ABGadd : forall (X : Set) (n m : nat), X -> ABG X n -> ABG X m -> ABG X (n + m + 1).
Check ABGadd.

End Problema4.

(*Ejercicio 5*)

Section Problema5.

Variable Bool: Set.
Variable TRUE : Bool.
Variable FALSE : Bool.
Variable Not : Bool -> Bool.
Variable Imp : Bool -> Bool -> Bool.
Variable Xor : Bool -> Bool -> Bool.

Axiom Disc : ~ (FALSE = TRUE).
Axiom BoolVal : forall b : Bool, b = TRUE \/ b = FALSE.
Axiom NotTrue : Not TRUE = FALSE.
Axiom NotFalse : Not FALSE = TRUE.
Axiom ImpFalse : forall b : Bool, Imp FALSE b = TRUE.
Axiom ImpTrue : forall b : Bool, Imp TRUE b = b.
Axiom XorTrue : forall b : Bool, Xor TRUE b = Not b.
Axiom XorFalse : forall b : Bool, Xor FALSE b = b.

Lemma L51 : forall b: Bool, Xor b b = FALSE.
Proof.
intros.
elim (BoolVal b);intros; rewrite H; [rewrite XorTrue | rewrite XorFalse].
rewrite NotTrue.
reflexivity.
reflexivity.
Qed.

Lemma L52: forall b1 b2: Bool, Imp b1 b2 = FALSE -> b1 = TRUE /\ b2 = FALSE.
Proof.
intros.
elim (BoolVal b1);intros.
rewrite H0 in H.
rewrite ImpTrue in H.
split; assumption.
rewrite H0 in H.
rewrite ImpFalse in H.
symmetry in H.
absurd (FALSE = TRUE).
apply Disc.
assumption.
Qed.

End Problema5.

