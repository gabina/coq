(* Práctica 6 *)
(* Gabina Luz Bianchi *)

(* Ejercicio 3 *)

Definition Value := bool.

Inductive BoolExpr : Set :=
| bbool : bool -> BoolExpr
| band : BoolExpr -> BoolExpr -> BoolExpr
| bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
| ebool : forall b : bool, BEval (bbool b) (b:Value)
| eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
| eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
| eandrl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
| enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
| enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.


Fixpoint beval1 (e : BoolExpr) : Value :=
match e with
| bbool b => b
| band e1 e2 =>
               match beval1 e1, beval1 e2 with
               | true, true => true
               | _, _ => false
               end
| bnot e1 => if beval1 e1 then false else true
end.

Fixpoint beval2 (e : BoolExpr) : Value :=
match e with
| bbool b => b
| band e1 e2 => 
               match beval2 e1 with
               | false => false
               | _ => beval2 e2
               end
| bnot e1 => if beval2 e1 then false else true
end.

Lemma beval1cor: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
intros.
exists (beval1 e).
induction e.
   * unfold beval1.
     constructor.
   * simpl.
     case_eq (beval1 e1);intros.
        + case_eq (beval1 e2);intros.
           - constructor.
              rewrite H in IHe1.
              assumption.
              rewrite H0 in IHe2.
              assumption.
           - apply eandr.
             rewrite H0 in IHe2.
             assumption.
        + constructor.
          rewrite H in IHe1.
          auto.
    * simpl.
     case_eq (beval1 e); intros.
        + rewrite H in IHe.
          constructor.
          auto.
       + rewrite H in IHe.
         constructor.
         auto.
Qed.

Lemma beval2cor: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
intros.
exists (beval2 e).
induction e.
   * unfold beval2.
     constructor.
   * simpl.
     case_eq (beval2 e1);intros.
        + case_eq (beval2 e2);intros.
           - constructor.
              rewrite H in IHe1.
              assumption.
              rewrite H0 in IHe2.
              assumption.
           - apply eandr.
             rewrite H0 in IHe2.
             assumption.
        + constructor.
          rewrite H in IHe1.
          auto.
    * simpl.
     case_eq (beval2 e); intros.
        + rewrite H in IHe.
          constructor.
          auto.
       + rewrite H in IHe.
         constructor.
         auto.
Qed.

Hint Constructors BEval.
Hint Constructors BoolExpr.


Lemma beval1cor2: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro; exists (beval1 e).
  induction e.
    auto.

    simpl; destruct (beval1 e1); destruct (beval1 e2); auto.

    simpl; destruct (beval1 e); auto.
Qed.


Lemma beval2cor2: forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro; exists (beval2 e).
  induction e.
    auto.

    simpl; destruct (beval2 e1); destruct (beval2 e2); auto.

    simpl; destruct (beval2 e); auto.
Qed.

Extraction Language Haskell.
Extraction "beval1" beval1cor2.
Extraction "beval2" beval2cor2.

Extract Inductive bool => "Bool" [ "true" "false" ].
Extraction "beval12" beval1cor.
Extraction "beval22" beval2cor.


(* Ejercicio 5 *)


Inductive Le: nat -> nat -> Prop :=
| le0 : forall n:nat, Le 0 n
| leS : forall n m : nat, Le n m -> Le (S n) (S m).

Inductive Gt: nat -> nat -> Prop :=
| gt0 : forall n:nat, (n <> 0) -> Gt n 0
| gtS : forall n m : nat, Gt n m -> Gt (S n) (S m).

Function leBool (n m : nat) : bool :=
match n with
| 0 => true
| S k => match m with
         | 0 => false
         | S p => leBool k p
         end
end.

Hint Constructors Le.
Hint Constructors Gt.
Require Import Omega.

Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
intros.
functional induction (leBool n m).
   +left.
    auto.
  +right.
   constructor.
   discriminate.
  + elim IHb; intros.
     - left.
       auto.
     - right.
       auto.
Qed.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
intros.
functional induction (leBool n m).
   + left.
     omega.
   + right.
     omega.
   + elim IHb; intros.
        - left.
          omega.
        - right.
          omega.
Qed.

(* Ejercicio 6 *)

Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
 match qr with
 (q,r) => (a = b*q + r) /\ r < b
 end.

Require Import Omega.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult. 
Require Import Coq.Arith.Compare_dec.


Definition nat_div_mod :
 forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}. 
Proof.
intros.
destruct b; intros.
   - omega.
   - induction a.
        + exists (0, 0).
          unfold spec_res_nat_div_mod.
          omega.
        + elim IHa.
          intros.
          destruct x.
          case_eq (le_lt_dec b n0); intros.
             * exists (S n,0).
               unfold spec_res_nat_div_mod.
               split; intros.
               rewrite -> plus_0_r.
               unfold spec_res_nat_div_mod in p.
               elim p; intros.
               rewrite -> H1.
               simpl.
               assert (n0 = b).
                  omega.
               rewrite -> H3.
               assert (b * n + b = b * S n).
                  assert ( S n = n + 1).
                  omega.
               rewrite -> H4.
               rewrite -> mult_plus_distr_l.
               omega.
               symmetry in H4.
               rewrite -> H4.
               omega.
               omega.
             * exists (n, S n0).
               unfold spec_res_nat_div_mod.
               split; intros.
               unfold spec_res_nat_div_mod in p.
               elim p; intros.
               rewrite -> H1.
               omega.
               omega.
Qed.

Extraction "divmod" nat_div_mod. 

(* Ejercicio 7 *)

Inductive tree (A:Set) : Set :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
| tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
| tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
intros.
unfold well_founded.
intros.
induction a.
   + apply (Acc_intro).
     intros.
     inversion H.
   + apply (Acc_intro).
     intros.
     inversion H; assumption.
Qed.

(* Ejercicio 8 *)

Fixpoint size (be : BoolExpr) :=
match be with
 | bbool b => 0
 | band b1 b2 => 2 + size b1 + size b2
 | bnot b =>  1 + size b
end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2. 

Theorem well_founded_elt : well_founded (elt).
Proof.
apply well_founded_ltof. 
Qed.