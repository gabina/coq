(* BIANCHI, GABINA LUZ *)

(* Practica 1 *)

Section P1.
Variables A B C:Prop.

(* Ej 1.1 *)
Theorem e11: A->A.
Proof.
intro.
assumption.
Qed.

(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
intro.
intro.
assumption.
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
intros.
apply H.
assumption.
apply H0.
assumption.
Qed.

(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
intros.
apply H0.
apply H.
assumption.
Qed.

(*Ej 2.2*) 
Theorem e22: (A->B->C)->B->A->C.
Proof.
intros.
apply H.
assumption.
assumption.
Qed.

(*Ej 3.1 *)
Theorem e31_1: A->A->A.
Proof.
intros.
exact H.
Qed.


Theorem e31_2: A->A->A.
Proof.
intros.
exact H0.
Qed. 

Print e31_1.
Print e31_2.

(* Ej 3.2 *)
Theorem e32_1: (A->B->C)->A->(A->C)->B->C.
Proof.
intros.
apply H1.
assumption.
Qed.

Theorem e32_2: (A->B->C)->A->(A->C)->B->C.
Proof.
intros.
apply H.
assumption.
assumption.
Qed.

Print e32_1.
Print e32_2.
(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
intros.
intro. (* Como se da cuenta de lo que quiero suponer*)
absurd A.
assumption.
assumption.
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
intros.
split.
assumption.
assumption.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
intros.
elim H0.
assumption.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
intros.
left.
assumption.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
intros.
right.
assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
intros.
elim H.
intro.
right.
assumption.
intro.
left.
assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
intros.
elim H1.
assumption.
assumption.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
intro.
elim H.
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
intros.
intro.
absurd B.
assumption.
apply H.
assumption.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
intro.
absurd A.
elim H.
intros.
assumption.
elim H.
intros.
assumption.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
intros.
intro.
elim H0.
intros.
absurd B.
assumption.
apply H.
assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
intros.
elim H.
intros.
intro.
absurd B.
apply H2.
assumption.
assumption.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
unfold not.
intros.
elim H.
intros.
apply H1.
assumption.
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
intros.
unfold not.
intros.
elim H0.
intros.
elim H.
assumption.
assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
unfold iff.
split.
intro.
elim H.
intro.
right.
assumption.
intro.
left.
assumption.
intro.
elim H.
intro.
right.
assumption.
intro.
left.
assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
intros.
elim H.
intro.
apply H0.
assumption.
intro.
assumption.
Qed.

End P1.


Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
intro.
elim H.
intro.
intro.
assumption.
intros.
absurd (~A).
assumption.
assumption.
Qed.

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
intros.
elim H.
intros.
right.
intro.
assumption.
intros.
left.
intro.
absurd A.
assumption.
assumption.
Qed.

(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
intros.
elim H.
intro.
right.
intro.
unfold not in H0.
apply H0.
split.
assumption.
assumption.
intros.
left.
assumption.
Qed.


Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A.
Proof.
intros.
elim (classic A0).
intro.
assumption.
intro.
absurd (~A0).
assumption.
assumption.
Qed.

(* Ej 8.2 *) 
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
intros.
elim (classic (A0 -> B0)).
intros.
left.
assumption.
intros.
right.
intro.
absurd (A0 -> B0).
assumption.
intro.
assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
intros.
elim (classic A0).
intros.
right.
intro.
unfold not in H.
apply H.
split.
assumption.
assumption.
intros.
left.
assumption.
Qed.

End Logica_Clasica.


Section Ejercicio9.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : ~NM \/ ~RED.
Hypothesis H2 : CONS \/ ~UTIL.

Theorem ej9 : NM /\ UTIL -> CONS /\ ~RED.
Proof.
intros.
elim H2.
intro.
split.
assumption.
unfold not.
intro.
elim H1.
intro.
absurd NM.
assumption.
elim H.
intros.
assumption.
intros.
absurd(RED).
assumption.
assumption.
intros.
split.
absurd(UTIL).
assumption.
elim H.
intros.
assumption.
unfold not.
intro.
absurd(UTIL).
assumption.
elim H.
intros.
assumption.
Qed.

End Ejercicio9.

(* Ej. 10 UTILIZANDO TAUTO*)
Section P10.
Variables A B C:Prop.

(* Ej 10.1 *)
Theorem e101: A->A.
Proof.
auto.
Qed.

(* Ej 10.2 *)
Theorem e102: A->B->A.
auto.
Qed.

(* Ej 10.3 *)
Theorem e103: (A->(B->C))->(A->B)->(A->C).
Proof.
auto.
Qed.

End P10.

Section Ejercicio11.
(* Ej 11 *)
(* Formalizaciones a cargo del estudiante *)
Variable MR UK SD C E : Prop.

(* MR: usa medias rojas
   UK: usa kilt
   SD: sale los domingos
   C: es casado
   E: es escocés
   *)

Variable p q : Prop.
Lemma contra :forall p q : Prop, (p -> q) -> (~q -> ~p).
Proof.
intros.
unfold not.
intro.
absurd q0.
-assumption.
-apply H.
 assumption. 
Qed.

Lemma dobleNegacion :forall p q : Prop, (p -> q) -> (p -> ~~q).
Proof.
intros.
unfold not.
intro.
apply H1.
apply H.
assumption.
Qed.

Hypothesis R1 : ~E -> MR. (*Todo no escocés debe usar medias rojas.*)
Hypothesis R2 : UK \/ ~MR. (*Todo miembro usa kilt o no usa medias rojas.*)
Hypothesis R3: C -> ~SD. (* Los miembros casados no salen los domingos.*)
Hypothesis R4: (SD -> E) /\ (E -> SD). (*Un miembro sale los domingos si y sólo si es escocés.*)
Hypothesis R5: UK -> (E /\ C). (* Todo miembro que usa kilt es escocés y es casado.*)
Hypothesis R6: E -> UK. (*Todo miembro escocés usa kilt.*)

Theorem ej111 :False.
Proof.
absurd UK.
unfold not.
intro.
- elim R4.
  intros.
  absurd SD.
  apply R3.
  apply R5.
  assumption.
  apply H1.
  apply R5.
  assumption.
- elim R2.
  intro.
  assumption.
  intros.
  elim R4.
  intros.
  apply R6.
  apply H0.
  cut (~~SD -> ~C).
  intros.
  absurd MR.
  assumption.
  apply R1.
  apply (contra E UK).  
  assumption.
  apply (contra UK (E /\ C)).
  assumption.
  unfold not.
  intro.
  absurd C.
  apply H2.
  apply (dobleNegacion E SD).
  assumption.
  elim H3.
  intros.
  assumption.
  elim H3.
  intros.
  assumption.
  apply (contra C (~SD)).
  assumption.
Qed. 

Theorem ej112 :False.
Proof.
absurd UK.
unfold not.
intro.
- tauto. 
- tauto.
Qed. 

End Ejercicio11.

Section Ejercicio12.

(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: (PF \/ PA) -> (PH \/ PR).
Hypothesis Regla2: ~PR \/ PF.
Hypothesis Regla3: (PH /\ ~PR) -> PA.


Theorem ej12: (~PA /\ PF) -> ~~PR.
Proof.
intros.
elim H.
intros.
intro.
absurd PA.
assumption.
apply Regla3.
elim Regla1.
intros.
split.
assumption.
assumption.
intros.
absurd PR.
assumption.
assumption.
left.
assumption.
Qed.

End Ejercicio12.
