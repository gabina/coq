(*Trabajo Practico 4.
Gabina Luz Bianchi *)

Section Ej1.

Set Implicit Arguments. 
Inductive list (A:Set) : Set :=
          nil : list A
        | cons : A -> list A -> list A.


Inductive bintree (A:Set) : Set :=
          nilbt : bintree A
        | consbt : A -> bintree A -> bintree A -> bintree A.


(* Inductive Array (A:Set) (n:nat) -> Set *)
Inductive Array (A:Set) : nat -> Set :=
          nila : Array A 0
        | consa : forall n:nat, A -> Array A n -> Array A (n+1). 

Inductive Leq : nat -> nat -> Prop :=
          le0 : forall n:nat, Leq 0 n
        | leS : forall (n m :nat), Leq n m -> Leq (S n) (S m).

Inductive eq_list {A:Set} (R : A -> A -> Prop) : list A -> list A -> Prop :=
          eq_nil : eq_list R (nil A) (nil A)
        | eq_cons : forall (a1 a2 : A) (l1 l2 : list A), 
      (eq_list R l1 l2) -> (R a1 a2) -> eq_list R (cons a1 l1) (cons a2 l2). 

Inductive sorted {A:Set} (R : A -> A -> Prop) : list A -> Prop :=
          sorted_nil : sorted R (nil A)
        | sorted_1 : forall (a : A), sorted R (cons a (nil A))
        | sorted_cons : forall (a1 a2 : A) (l1 : list A), 
      (sorted R (cons a2 l1)) -> (R a1 a2) -> sorted R (cons a1 (cons a2 l1)).

Inductive mirror {A:Set} : bintree A -> bintree A -> Prop := 
          mirror_nil : mirror (nilbt A) (nilbt A)
        | mirror_cons : forall (a : A) (b1 b2 b3 b4 : bintree A), 
      (mirror b1 b2) -> (mirror b3 b4) -> mirror (consbt a b1 b3) (consbt a b4 b2).

Inductive isomorfo {A:Set} : bintree A -> bintree A -> Prop := 
          isomorfo_nil : isomorfo (nilbt A) (nilbt A)
        | isomorfo_cons : forall (a1 a2: A) (b1 b2 b3 b4 : bintree A), 
      (isomorfo b1 b2) -> (isomorfo b3 b4) -> isomorfo (consbt a1 b1 b3) (consbt a2 b2 b4).

End Ej1.

Section Ej2.

Definition boolOr := 
           fun b1 b2: bool => match b1, b2 with 
                            | true, _ => true
                            | false, b2 => b2 end.

Definition boolAnd :=
           fun b1 b2: bool => match b1, b2 with 
                            | true, true => true
                            | _, _ => false end.

Definition boolXor :=
           fun b1 b2: bool => match b1, b2 with
                            | false, true => true
                            | true, false => true
                            | _,_ => false end.
                              
End Ej2.

Section Ej3.

(* 3.1 *)
Fixpoint sum (n m:nat) {struct n}: nat :=
  match n with
       0 => m
     | S k => S (sum k m)
  end.

(* 3.2 *)
Fixpoint prod (n m:nat) {struct n}: nat :=
  match n with
       0 => 0
     | S k => sum m (prod k m)
  end.

(* 3.3 *)
Fixpoint pot (n m:nat) {struct m}: nat :=
  match m with
       0 => 1
     | S k => prod n (pot n k)
  end.

(* 3.4 struct? *)
Fixpoint leBool (n m:nat) : bool :=
  match n, m with
       0, _ => true
     | _, 0 => false
     | (S k), (S j)  => leBool k j
  end.

End Ej3.

Section Ejercicio4.

    (* Ej. 4.1 *)

    Fixpoint length (X: Set) (xs: list X): nat := match xs with
        nil => 0
      | cons x xs' => sum 1 (length xs')
      end.

    (* Ej. 4.2 *)

    Fixpoint append (X: Set) (xs ys: list X) {struct xs}: list X := match xs with
        nil => ys
      | cons x xs' => cons x (append xs' ys)
      end.

    (* Ej. 4.3 *)

    Fixpoint reverse (X: Set) (xs: list X) {struct xs}: list X := match xs with
        nil => nil X
      | cons x xs' => append (reverse xs') (cons x (nil X))
      end.

    (* Ej. 4.4 *)

    Fixpoint filter (X: Set) (p: X -> bool) (xs: list X) {struct xs}: list X
      := match xs with
           nil => nil X
         | cons x xs' => if p x then cons x (filter p xs')
                                else filter p xs'
         end.

    (* Ej. 4.5 *)

    Fixpoint map (X Y: Set) (f: X -> Y) (xs: list X): list Y
      := match xs with
           nil => nil Y
         | cons x xs' => cons (f x) (map f xs')
         end.

    (* Ej. 4.6 *)

    Fixpoint exists' (X: Set) (p: X -> bool) (xs: list X): bool
      := match xs with
           nil => false
         | cons x xs' => boolOr (p x) (exists' p xs')
         end.

End Ejercicio4.

Section Ej5.

(* consbt : A -> bintree A -> bintree A -> bintree A. *)

Fixpoint inverse (A:Set) (t: bintree A) : bintree A:=
  match t with
       nilbt => nilbt A
     | consbt a b0 b1 => consbt a (inverse b1) (inverse b0)
  end.

End Ej5.

Section Ej9.
Lemma SumO : forall (n : nat), sum n 0 = n /\ sum 0 n = n.
Proof.
induction n.

split;reflexivity.
simpl.
split.
elim IHn.
intros.
rewrite H.
reflexivity.
reflexivity.
Qed.

Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
induction n.
reflexivity.

intros.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
induction n.
intros.
reflexivity.
intros.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
induction n.
intros.
simpl.
symmetry.
apply SumO.

intros.
rewrite SumS.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

End Ej9.

Section Ej12.
Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
map f (append l m) = append (map f l) (map f m).
Proof.
induction l.
intros.
reflexivity.
intros.
simpl.
rewrite -> IHl.
reflexivity.
Qed.

Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
filter P (append l m) = append (filter P l) (filter P m).
Proof.
induction l.
reflexivity.
intros.
simpl.
rewrite -> IHl.

case (P a); reflexivity.
Qed.

Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool),
filter P (filter P l) = filter P l.
Proof.
induction l; intros.
simpl.
reflexivity.
simpl.
assert (H: (P a) = true \/ (P a) = false).
    case (P a);[left | right]; trivial.
elim H; intros.
rewrite H0. 
simpl.
rewrite H0.
rewrite -> IHl.
reflexivity.
rewrite H0.
rewrite -> IHl.
reflexivity.
Qed.

Lemma L10 : forall (A : Set) (l m n : list A),
append l (append m n) = append (append l m) n.
Proof.
induction l; intros.
reflexivity.
simpl.
rewrite -> IHl.
reflexivity.
Qed.
End Ej12.

Section Ej14.
Lemma L14 :forall (A:Set) (t: bintree A), mirror t (inverse t).
Proof.
induction t.
simpl.
constructor.
simpl.
constructor;assumption.
Qed.

End Ej14.


Section Ej17.

Inductive posfijo {A:Set} : list A -> list A -> Prop := 
          posfijo_base : forall (xs : list A), posfijo xs xs
        | posfijo_induc : forall (a : A) (xs ys : list A), (posfijo xs ys) -> posfijo xs (cons a ys).

Lemma L171 : forall (A: Set) (l1 l2 l3 : list A), l2 = (append l3 l1) -> posfijo l1 l2. 
Proof.
intros.
rewrite -> H.
clear H.
induction l3.
simpl.
constructor.
simpl.
constructor.
apply IHl3.
Qed.

Lemma L172: forall (A:Set) (l1 l2 : list A), posfijo l1 l2 -> (exists l3:list A, l2 = append l3 l1).
Proof.
intros.
induction H.
exists (nil A).
reflexivity.
elim IHposfijo.
intros.
exists (cons a x).
simpl.
rewrite -> H0.
reflexivity.
Qed.

Lemma L173: forall (A:Set) (l1 l2: list A), posfijo l2 (append l1 l2).
Proof.
intros.
induction l1.
simpl.
constructor.
simpl.
constructor.
assumption.
Qed.

Axiom axio : forall (A:Set) (l1 l2: list A), l1 = append l2 l1 -> l2 = nil A.

Lemma appEmpty (A:Set) : forall (l1 l2 :list A), append l1 l2 = nil A -> l1 = nil A /\ l2 = nil A.
Proof.
intros.
induction l1.
split.
reflexivity.
assumption.
simpl in H.
discriminate H.
Qed.
 
Lemma L174 (A:Set) : forall (l1 l2: list A), posfijo l1 l2 -> posfijo l2 l1 -> l1 = l2.
Proof.
intros.
apply L172 in H.
apply L172 in H0.
elim H; elim H0.
intros.
rewrite H2 in H1.
rewrite L10 in H1.
apply axio in H1.
apply appEmpty in H1.
elim H1; intros.
rewrite H4 in H2.
simpl in H2.
symmetry.
assumption.
Qed.


Lemma L175 (A:Set) : forall (l1 l2 l3: list A), posfijo l1 l2 -> posfijo l2 l3 -> posfijo l1 l3.
Proof.
intros.
induction H0.
induction l1.
assumption.
assumption.
induction H0.
apply posfijo_induc.
assumption.
apply posfijo_induc.
apply IHposfijo.
assumption.
Qed.

Fixpoint ultimo (A:Set) (l: list A) : list A :=
  match l with
       nil => nil A
     | cons a nil => cons a (nil A)
     | cons a l' => ultimo l'
  end.

(*Pruebe que la función último de una lista es un posfijo de dicha lista.*)
Lemma L176: forall (A:Set) (l1: list A), (posfijo (ultimo l1) l1).
Proof.
intros.
induction l1.
simpl.
constructor.
simpl.
destruct l1.
apply posfijo_base.
apply posfijo_induc. 
assumption.
Qed.



End Ej17.



Section Ej20.

Inductive ACom (A:Set) : nat -> Set :=
          Acom_b : A -> ACom A 0
        | Acom_i : forall (m:nat),  A -> ACom A m -> ACom A m -> ACom A (S m).

(* Parameter pot: nat -> nat -> nat. *)
Axiom potO : forall n : nat, pot (S n) 0 = 1.

Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).

    Fixpoint h (A: Set) (n:nat) (t:ACom A n): nat
      := match t with
           Acom_b A => 1
         | Acom_i m A t1 t2 => 2 * (h t1)
         end.


Lemma e20 : forall (A: Set) (n:nat)(t:ACom A n), (h t) = pot 2 n.
Proof.
induction t.
reflexivity.
simpl.
rewrite -> IHt1.
reflexivity.
Qed.

End Ej20.