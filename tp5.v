(* Gabina Luz Bianchi *)
(* Trabajo Práctico 5*)

(*Ejercicio 5*)

Section Ejercicio5.

Set Implicit Arguments. 

Require Import Coq.Bool.Bool.

Definition Var := nat.

Inductive BoolExp : Set :=
        varExp  : Var -> BoolExp
        | boolExp : bool -> BoolExp
        | andExp : BoolExp -> BoolExp -> BoolExp
        | negExp : BoolExp -> BoolExp.

Definition Valor := bool.

Definition Memoria := forall v:Var, Valor.

Definition lookup := fun (m:Memoria) (v:Var) => m v.

Inductive evalExp (m:Memoria) : BoolExp -> Valor -> Prop :=
          evar : forall v:Var, evalExp m (varExp v) (lookup m v)
        | eboolt : evalExp m (boolExp true) true
        | eboolf : evalExp m (boolExp false) false 
        | eandl: forall (be1 be2:BoolExp), evalExp m be1 false -> evalExp m (andExp be1 be2) false
        | eandr : forall (be1 be2:BoolExp), evalExp m be2 false -> evalExp m (andExp be1 be2) false
        | eandlr : forall (be1 be2:BoolExp), evalExp m be1 true -> evalExp m be2 true -> evalExp m (andExp be1 be2) true
        | enottt : forall be:BoolExp, evalExp m be true -> evalExp m (negExp be) false 
        | enottf : forall be:BoolExp, evalExp m be false -> evalExp m (negExp be) true.


Theorem ej51a : forall m:Memoria,~ evalExp m (boolExp true) false.
Proof.
intros.
intro.
inversion H.
Qed.

Theorem ej51b : forall m:Memoria,~ evalExp m (boolExp false) true.
Proof.
intros.
intro.
inversion H.
Qed.

Theorem ej52: forall (m:Memoria) (be1 be2:BoolExp) (b:Valor), evalExp m be1 true -> evalExp m be2 b -> evalExp m (andExp be1 be2) b.
Proof.
intros.
destruct b.
constructor; assumption.
apply eandr.
assumption.
Qed.

Fixpoint beval (m:Memoria) (be :BoolExp) : Valor := match be with 
        varExp v => lookup m v
      | boolExp b => b 
      | andExp b1 b2 => (beval m b1) && (beval m b2)
      | negExp b => negb (beval m b) end.

Theorem andExpConm : forall (be1 be2 : BoolExp) (m:Memoria), beval m (andExp be1 be2) = beval m (andExp be2 be1).
Proof.
intros.
simpl.
apply  andb_comm.
Qed.

Theorem evalTrueFalse: forall (m:Memoria) (be:BoolExp), evalExp m be true -> evalExp m be false -> False.
Proof.
intros.
induction be.
   - inversion H.
     inversion H0.
     apply (eq_true_false_abs (lookup m v) H3 H5).
   - destruct b.
        + apply (ej51a H0).
        + apply (ej51b H).
   - inversion H.
     inversion H0.
        + elim IHbe1; assumption.
        + elim IHbe2; assumption.
   - inversion H.
     inversion H0.
     apply IHbe; assumption.  
Qed.

Theorem ej53 : forall (v1 v2 : Valor) (be:BoolExp) (m:Memoria), evalExp m be v1 -> evalExp m be v2 -> v1 = v2.
Proof.
intros.
induction be.
   + inversion H0. 
     inversion H.
     reflexivity.
   + destruct b.
      - inversion H.
        inversion H0.
        reflexivity.
      - inversion H.
        inversion H0.
        reflexivity.
   + inversion H.
      -symmetry in H2.
       rewrite H2 in IHbe1.
       inversion H0.
          * reflexivity.
          * reflexivity.
          * assert (False).
            apply (evalTrueFalse H7 H4).
            elim H10.
       -symmetry in H2.
        rewrite H2 in IHbe1.
         inversion H0.
          * reflexivity.
          * reflexivity.
          * assert (False).
            apply (evalTrueFalse H9 H4).
            elim H10.
       -inversion H0.
           * assert (False).
             apply (evalTrueFalse H3 H9).
             elim H10.
           * assert (False).
             apply (evalTrueFalse H5 H9).
             elim H10.
           * reflexivity.
    + inversion H.
         -inversion H0.
             * reflexivity.
             * assert (False).
               apply (evalTrueFalse H2 H5).
               elim H7.
         -inversion H0.
             * assert (False).
               apply (evalTrueFalse H5 H2).
               elim H7.
             * reflexivity.
Qed. 

Theorem ej54: forall (be1 be2 : BoolExp) (m:Memoria), evalExp m be1 false -> (evalExp m (negExp (andExp be1 be2)) true).
Proof.
intros.
constructor.
apply eandl.
assumption.
Qed.

Theorem ej55 : forall (m: Memoria) (be:BoolExp), evalExp m be (beval m be).
Proof.
intros.
induction be.
   + simpl.
     constructor.
   + simpl.
     destruct b; constructor.
   + simpl.
     destruct (beval m be1).
        - simpl.
          destruct (beval m be2).
             * constructor.
               assumption.
               assumption.
             * apply eandr.
               assumption.
        - simpl.
          constructor.
          assumption.
   + simpl.
     destruct (beval m be).
        - simpl.
          constructor.
          assumption.
        - simpl.
          constructor.
          assumption.
Qed.

End Ejercicio5.

Section Ejercicio6.

Inductive LInstr : Set :=
       vacio : LInstr
     | secuencia : Instr -> LInstr -> LInstr
with Instr : Set :=
        skip  : Instr
        | var : Var -> BoolExp -> Instr
        | ifThenElse : BoolExp -> Instr -> Instr -> Instr
        | whileDo : BoolExp -> Instr -> Instr
        | repeat : nat -> Instr -> Instr
        | beginEnd : LInstr -> Instr.

Infix "puntoYComa" := secuencia (right associativity, at level 94).

Definition PP (v1 v2 : Var) : Instr := beginEnd ((var v1 (boolExp true)) puntoYComa (var v2 (negExp (varExp v1))) puntoYComa vacio ).

Definition swap (aux v1 v2 : Var) : Instr := beginEnd ((var aux (varExp v1)) puntoYComa (var v1 (varExp v2)) puntoYComa (var v2 (varExp aux)) puntoYComa vacio).

Require Import Coq.Arith.EqNat.


Definition update (m: Memoria) (v1:Var) (b : Valor) := fun v0:Var => if (beq_nat v0 v1) then b else (m v0).


Theorem ej64 : forall (v:Var) (b:Valor) (m:Memoria), lookup (update m v b) v = b.
Proof.
intros.
unfold lookup.
unfold update.
assert (beq_nat v v = true).
   symmetry.
   apply beq_nat_refl. 
rewrite -> H.
reflexivity.
Qed.

Theorem ej65 : forall (m:Memoria) (v1 v2 : Var) (b : Valor), v1 <> v2 -> lookup (update m v1 b) v2 = lookup m v2.
Proof.
intros.
unfold lookup.
unfold update.
case_eq (beq_nat v2 v1); intros.
   - absurd (v1 = v2).
        + assumption.
        + symmetry.
          apply (beq_nat_true v2 v1 H0).
   - reflexivity.
Qed.

End Ejercicio6.

Section Ejercicio7.

Infix "puntoYComa" := secuencia (right associativity, at level 94).

Inductive execute_l (m:Memoria) : LInstr -> Memoria -> Prop :=
          xEmptyblock : execute_l m vacio m
        | xNext :  forall (i : Instr) (li : LInstr) (m' m'': Memoria), execute m i m' -> execute_l m' li m'' -> execute_l m (i puntoYComa li) m''
with 
        execute (m:Memoria) : Instr -> Memoria -> Prop :=
          xAss : forall (be:BoolExp) (b:Valor) (v:Var), evalExp m be b -> execute m (var v be) (update m v b)
        | xSkip : execute m skip m
        | xIfThen : forall (m':Memoria) (be:BoolExp)(p1 p2:Instr), evalExp m be true -> execute m p1  m' -> execute m (ifThenElse be p1 p2)  m'
        | xIfElse : forall (m':Memoria) (be:BoolExp)(p1 p2:Instr), evalExp m be false -> execute m p2 m' -> execute m (ifThenElse be p1 p2) m'       
        | xWhileTrue : forall (m' m'':Memoria) (be:BoolExp)(p :Instr), evalExp m be true -> execute m p  m' -> execute m' (whileDo be p)  m'' -> execute m (whileDo be p) m''  
        | xWhileFalse : forall (be:BoolExp)(p :Instr), evalExp m be false -> execute m (whileDo be p)  m
        | xRepeat0 : forall i:Instr, execute m (repeat 0 i) m
        | xRepeatS : forall (m' m'':Memoria) (i:Instr) (n:nat), execute m i m' -> execute m' (repeat n i)  m'' -> execute m (repeat (S n) i) m''
        | xBeginEnd : forall (li:LInstr) (m': Memoria), execute_l m li m' -> execute m (beginEnd li) m'.


Theorem notNegfalseIsFalse :  forall m:Memoria, evalExp m (negExp (boolExp false)) false -> False.
Proof.
intros.
inversion H.
absurd (evalExp m (boolExp false) true).
apply ej51b.
assumption.
Qed.

Theorem notNegtrueIsTrue :  forall m:Memoria, evalExp m (negExp (boolExp true)) true -> False.
Proof.
intros.
inversion H.
absurd (evalExp m (boolExp true) false).
apply ej51a.
assumption.
Qed.

Theorem ej72 : forall (m m' : Memoria) (e1 e2 : Instr), execute m (ifThenElse (negExp (boolExp false)) e1 e2) m' ->  execute m (ifThenElse (boolExp false) e2 e1) m'.
Proof.
intros.
inversion H.
   - apply xIfElse.
      + constructor.
      + assumption.
   - elim (notNegfalseIsFalse H4).
Qed.

Theorem ej73 : forall (b:Valor) (m m' : Memoria) (e1 e2 : Instr), execute m (ifThenElse (negExp (boolExp b)) e1 e2) m' ->  execute m (ifThenElse (boolExp b) e2 e1) m'.
Proof.
intros.
destruct b.
   - inversion H.
       * elim (notNegtrueIsTrue H4).
       * apply xIfThen.
         + constructor.
         + assumption.
   - apply (ej72 H).
Qed.

Theorem ej74: forall (m m':Memoria) (i:Instr), execute m (whileDo (boolExp false) i) m' -> m = m'.
Proof.
intros.
inversion H.
   - absurd (evalExp m (boolExp false) true).
      + apply ej51b.
      + assumption.
   - reflexivity.
Qed.


Theorem ej75: forall (m m':Memoria) (i:Instr) (be:BoolExp), execute_l m ( (ifThenElse be i skip) puntoYComa (whileDo be i) puntoYComa vacio) m' -> execute m (whileDo be i) m'.
Proof.
intros. 
inversion_clear H.
inversion_clear H0.
   apply xWhileTrue with (m':=m'0).
   assumption.
   assumption.
   inversion_clear H1.
   inversion H3.
   rewrite H4 in H0.
   assumption.

   inversion H2.
   inversion H1.
   inversion H7.
   rewrite H9 in H5.
   assumption.
(*
inversion H2.
   apply xWhileTrue with (m':=m'0).
      assumption.
      assumption.
      inversion H4.
         inversion H15.
         rewrite H17 in H13.
         assumption.
      inversion H2.*)
Qed.


Theorem ej76: forall (n:nat) (i:Instr) (m m' : Memoria), execute_l m (i puntoYComa (repeat n i puntoYComa vacio)) m' -> execute m (repeat (S n) i) m'.
Proof.
intros.
inversion H.
apply xRepeatS with (m':=m'0).
   assumption.
   inversion H4.
   inversion H9.
   rewrite H11 in H7.
   assumption.
Qed. 

Theorem ej77: forall (n1 n2:nat) (m1 m2 m3: Memoria) (i:Instr), execute m1 (repeat n1 i) m2 -> execute m2 (repeat n2 i) m3 -> execute m1 (repeat (n1+n2) i) m3.
Proof.
induction n1.
intros.
   simpl.
   inversion H.
   assumption.

intros.
simpl.
inversion H.
apply xRepeatS with (m':=m').
   assumption.
   apply (IHn1 n2 m' m2 m3 i H5 H0). 
Qed.

Check PP.

Theorem ej78aux : forall (m : Memoria) (v1 v2 : Var) (b : Valor), v2 <> v1 -> update m v1 b v2 = m v2.
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

Check ej78aux.

Theorem ej78a: forall (m m':Memoria) (v1 v2 : Var), v1 <> v2 -> execute m (PP v1 v2) m' ->  m' v1 = true . 
Proof.
intros.
unfold PP in H0.
inversion_clear H0.
inversion_clear H1. 
inversion_clear H2.
inversion H3.
rewrite H4 in H1.
inversion H0.
inversion H1.
rewrite -> (ej78aux m'0 b0 H).
inversion H7.
symmetry in H5.
rewrite -> H5.
rewrite -> H13.
unfold update.
case_eq (beq_nat v1 v1); intros.
         + reflexivity.
         + absurd (true = false).
              * discriminate.
              * rewrite -> (beq_nat_refl v1).
                assumption.
Qed.

Theorem ej78b: forall (m m':Memoria) (v1 v2 : Var), v1 <> v2 -> execute m (PP v1 v2) m' -> m' v2 = false. 
Proof.
intros.
assert ( m' v1 = true).
   apply (ej78a H H0).
unfold PP in H0.
inversion_clear H0.
inversion_clear H2. 
inversion_clear H3.
inversion H4.
rewrite H5 in H2.
inversion H2.
unfold update.
case_eq (beq_nat v2 v2); intros.
      + inversion H8.
         * reflexivity.
         * inversion H11. 
           unfold lookup.
           symmetry in H6.
           rewrite H6 in H1.
           rewrite (ej78aux m'0 b H) in H1.
           symmetry.
           assumption.
      + absurd (true = false).
            * discriminate.
             * rewrite -> (beq_nat_refl v2).
               assumption.
Qed.

Theorem ej78: forall (m m':Memoria) (v1 v2 : Var), v1 <> v2 -> execute m (PP v1 v2) m' -> (m' v2 = false /\ m' v1 = true).
Proof.
intros.
split.
   + apply (ej78b H H0).
   + apply (ej78a H H0).
Qed.


End Ejercicio7.