(*
NOMBRE COMPLETO: Gabina Luz Bianchi
NRO. DE DOCUMENTO: 37447849
*)


Section Problema1.

Require Export List.
Require Export Arith.
Print beq_nat.

Set Implicit Arguments.

Fixpoint eliminar (z : nat) (l : list nat) : list nat :=
       match l with
        nil => nil
      | cons x xs' => if (beq_nat x z) then xs' else cons x (eliminar z xs') 
      end.

Fixpoint pertenece (z : nat) (l : list nat) : bool :=
       match l with
        nil => false
      | cons x xs' => if (beq_nat x z) then true else (pertenece z xs') 
      end.

Fixpoint concatenar (X: Set) (xs ys: list X) {struct xs}: list X := match xs with
        nil => ys
      | cons x xs' => cons x (concatenar xs' ys)
      end.

Lemma L1_1 : forall (A : Set) (l : list A) (x : A), l <> x::l.
Proof. 
intros.
induction l.
   + discriminate.
   + injection.
     intros.
     rewrite H1 in H0.
     absurd(l = x :: l);assumption.
Qed.

Lemma L1_2 : forall (l1 l2 : list nat) (x : nat), 
  pertenece x (concatenar l1 l2) = true -> 
  pertenece x l1 = true \/ pertenece x l2 = true.
Proof.
induction l1; intros.
   + right.
     auto.
   + simpl.
     case_eq (beq_nat a x); intros.
        - left.
          reflexivity.
        - apply IHl1.
          inversion H.
          rewrite -> H0.
          reflexivity.
Qed.

Lemma L1_3 : forall (l : list nat) (x : nat), 
  pertenece x l = true -> eliminar x l <> l.
Proof. 
induction l; intros.
   + discriminate.
   + simpl.
    case_eq (beq_nat a x); intros.
       - apply L1_1.
       - injection.
         intros.
         inversion H.
         rewrite H0 in H4.
         absurd(eliminar x l = l).
            * apply IHl.
              assumption.
            * assumption.
Qed.

End Problema1.


Section Problema2.

Inductive distintas (A:Set) : list A -> list A -> Prop :=
          dist_base : distintas nil nil
        | dist_induc : forall (a1 a2 : A) (l1 l2 :list A), a1 <> a2 -> distintas l1 l2 -> distintas (cons a1 l1) (cons a2 l2).

Hint Constructors distintas.

Require Import Coq.Bool.Bool.

(* Resolución 1*)
Lemma L2_2 : forall (l1 : list bool), { l2 : list bool | distintas l1 l2 }.
Proof. 
intros.
induction l1.
   + exists nil.
     auto.
   + elim IHl1; intros. 
     exists (cons (negb a) x).
     constructor.
        - unfold not.
          intros.
          apply (no_fixpoint_negb a) .
          symmetry.
          assumption.
        - assumption.
Qed.


Lemma L2 : forall (l1 : list bool), { l2 : list bool | distintas l1 l2 }.
Proof. 
intros.
induction l1.
   + exists nil.
     auto.
   + elim IHl1; intros. 
    case_eq a; intros.
       * exists (cons false x).
         constructor.
            - discriminate.
            - assumption.
      * exists (cons true x).
         constructor.
            - discriminate.
            - assumption.
Qed.

End Problema2.

Extraction Language Haskell.
Extract Inductive bool => "Bool" [ "true" "false" ].
Extraction "distintas" L2.
Extraction "distintas2" L2_2.


Require Export List.
Require Export Arith.
Print beq_nat.

Set Implicit Arguments.

Section Problema3.
 
Definition Var := nat.
Definition Valor := nat.

Definition Memoria := Var -> Valor.

Definition lookup (m : Memoria) (v : Var) : Valor := m v.
 
Definition update (m : Memoria) (v : Var) (w : Valor) : Memoria := fun v0 : Var => if (beq_nat v0 v) then w else (m v0).

Inductive Instr : Set :=
        assig  : Var -> Valor -> Instr
        | pC : Instr -> Instr -> Instr
        | ifEq : Var -> Valor -> Instr -> Instr -> Instr.

 
Inductive Execute (m:Memoria): Instr -> Memoria -> Prop := 
          xAss : forall (v:Var) (val:Valor),  Execute m (assig v val) (update m v val)
        | xSeq : forall (m1 m2 : Memoria) (i1 i2: Instr), Execute m i1 m1 -> Execute m1 i2 m2 -> Execute m (pC i1 i2) m2
        | xIfT : forall (m':Memoria) (v1: Var) (i1 i2 :Instr) (val:Valor), lookup m v1 = val -> Execute m i1 m' -> Execute m (ifEq v1 val i1 i2) m'
        | xIfF : forall (m':Memoria) (v1: Var) (i1 i2 :Instr) (val:Valor), lookup m v1 <> val -> Execute m i2 m' -> Execute m (ifEq v1 val i1 i2) m'.

Lemma L3_1 : forall (m1 m2 : Memoria) (var : Var) (val : Valor), Execute m1 (assig var val) m2 -> lookup m2 var = val.
Proof.
intros.
unfold lookup.
inversion H.
unfold update.
assert (beq_nat var var = true).
   symmetry.
   apply beq_nat_refl.
rewrite -> H3.
reflexivity. 
Qed.

Lemma L3_2 : forall (m1 m2 : Memoria) (v : Var) (val : Valor) (i1 i2 : Instr), lookup m1 v <> val -> Execute m1 (ifEq v val i1 i2) m2 -> Execute m1 i2 m2.
Proof.
intros.
inversion H0.
   + absurd ( lookup m1 v = val); assumption.
   + assumption.
Qed.

Require Import Omega.

Theorem aux : forall (m : Memoria) (v1 v2 : Var) (val : Valor), v2 <> v1 -> update m v1 val v2 = m v2.
Proof.
intros.
unfold update.
case_eq (beq_nat v2 v1); intros.
   - absurd (v2 = v1).
      + assumption.
      + apply (beq_nat_true v2 v1).
        assumption.
   - reflexivity.
Qed.

Lemma L3_3: forall (m1 m2 m3 : Memoria) (v1 v2 : Var) (val : Valor) (i1 i2 : Instr), v1 <> v2 -> Execute m1 (pC (assig v1 val) (assig v2 (val+1))) m2 -> Execute m2 i2 m3 -> Execute m2 (ifEq v2 (lookup m2 v1) i1 i2) m3.
Proof.
intros.
inversion H0.
apply xIfF.
   + inversion H6.
     unfold lookup.
     inversion H4.
     unfold update.
     case_eq (beq_nat v2 v2); intros.
        - case_eq (beq_nat v1 v2); intros.
             *  absurd (v1 = v2).
                 assumption.
                 apply (beq_nat_true v1 v2).
                 assumption.
             * assert (beq_nat v1 v1 = true).
                 symmetry.
                 apply (beq_nat_refl v1).
               rewrite -> H15.
               omega.
        - assert (true = beq_nat v2 v2).
             * apply (beq_nat_refl v2).
             * rewrite H13 in H14.
               discriminate.
   + assumption.
Qed.
 
End Problema3.