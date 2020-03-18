(* Trabajo Práctico 3 *)
(* Gabina Luz Bianchi *)

Section Ejercicio3. (* Necesito la definición de o para el ejrcicio 4 *)
Variable A B C: Set.

Definition apply := fun (A B : Set) (f: A->B) => fun a:A => (f a).
Definition o := fun (A B C : Set) (f: A->B) => fun g: B->C => fun a:A => ( g (f a)).
Definition twice := fun (A : Set) (f: A->A) => fun a:A => (f (f a)).

End Ejercicio3.

Section Ejercicio4.
Variable A: Set.

Definition id := fun (A : Set) (x : A) => x.

(* Prueba 1 *)
Theorem e41 : forall x:A, (o A A A (id A) (id A) x) = (id A x).
Proof.
intros.
compute.
reflexivity.
Save.

(* Prueba 2 *)
Theorem e42 : forall x:A, (o A A A (id A) (id A) x) = (id A x).
Proof.
intros.
cbv delta beta.
reflexivity.
Save.

(* Prueba 3 *)
Theorem e43 : forall x:A, (o A A A (id A) (id A) x) = (id A x).
Proof.
intros.
cbv delta.
simpl.
reflexivity.
Save.

End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK (A B: Set) (x : A) (y : B) := x.

Definition opS (A B C : Set) (f : A -> B -> C) (g: A -> B)  (x : A) := ((f x) (g x)).

Check opI.
Check opK.
Check opS.

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall (A B : Set), opS A (B -> A) A (opK A (B -> A)) (opK A B) = (opI A).
Proof.
intros.
compute.
reflexivity.
Save.

End Ejercicio5.

Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall X:Set, Matrix X 0.
Parameter addM : forall (X:Set) (n:nat), Matrix X n -> Array X (n + 1) -> Matrix X (n+1).

Definition A1 := (addA nat 0 1 (emptyA nat)).
Check A1.
Definition M1 := addM nat 0 (emptyM nat) A1. (* matriz de una columna *)
Check M1.
Definition A2 := (addA nat 1 2 ((addA nat 0 2 (emptyA nat)))).
Check A2.
Definition M2 := addM nat 1 M1 A2. (* matriz de dos columnas *) 
Check M2.
Definition A3 := addA nat 2 3 (addA nat 1 3 ((addA nat 0 3 (emptyA nat)))).
Check A3.
Definition M3 := addM nat 2 M2 A3. (* matriz de tres columnas *)
Check M3.

End Ejercicio10.


Section Ejercicio11.

Parameter ABNat : forall n : nat, Set.
Parameter emptyAB : ABNat 0.
Parameter addAB : forall n : nat, ABNat n -> ABNat n -> nat -> ABNat (n+1).

Definition BT1 := addAB 0 emptyAB emptyAB 7. (*Árbol binario de altura 1 cuya raíz es 7*)
Check BT1.
Definition BT2 := addAB 1 BT1 BT1 3.
Check BT2.

Parameter ABtype : forall (X: Set) (n : nat), Set.
Parameter emptyABtype : forall X: Set, ABtype X 0.
Parameter addABtype : forall (X: Set) (n : nat), ABtype X n -> ABtype X n -> X -> ABtype X (n+1).
Check addABtype.

End Ejercicio11.

Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
   exact (H x (H0 x)).
Save.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Save.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
    exact (fun (H : forall x : U, P -> A x) (H0 : P) (x : U) => (H x H0)).
Save.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
     exact (fun (H :forall x y : U, R x y) (x : U) => (H x x)).
Save.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
     exact (fun (H : forall x y:U, R x y -> R y x) (z : U) => (H e z)).
Save.

End Ejercicio15.