(*Trabajo Práctico 2.
Gabina Luz Bianchi *)

Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).
Definition Reflexividad := forall x:U, (R x x).
Definition Simetria := forall x y :U, (R x y) -> (R y x).
Definition Transitividad := forall x y z :U, (R x y) /\ (R y z) -> (R x z).

Theorem e231: H1 /\ H2 -> Reflexividad /\ Simetria /\ Transitividad. 
Proof.
unfold H1.
unfold H2.
intros.
unfold Reflexividad.
unfold Simetria.
unfold Transitividad.
elim H.
intros.
split.
intros.
apply H.
split.
intros.
apply (H3 x y x).
split.
assumption.
apply H0.
intros.
apply (H3 y x z).
elim H4.
intros.
split.
apply (H3 x y x).
split.
assumption.
apply H0.
assumption.
Qed.

Definition Irreflexividad := forall x:U, ~(R x x).
Definition Asimetria := forall x y:U, (R x y) -> ~(R y x).
 
Lemma e232 : Asimetria -> Irreflexividad.
Proof.
unfold Asimetria.
unfold Irreflexividad.
intros.
intro.
absurd (R x x).
apply (H x x).
assumption.
assumption.
Qed.

End Ejercicio3.

Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intros; split; apply H.
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
intros; elim H; intros; elim H0;intros; [left | right];exists x; intros; assumption.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
intros; elim H; intros; [left | right]; apply H0.
Qed.

End Ejercicio7.

Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
intros.
elim (classic (A x)).
intros.
assumption.
intros.
absurd (exists x : U, ~ A x).
assumption.
exists x.
assumption.
Qed.


Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
intros.
elim (classic (exists x : U, ~ A x)); intro.
assumption.
unfold not in H.
elim H.
apply  not_ex_not_forall.
assumption.
Qed.

End Ejercicio9.



Section Ejercicio10.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
transitivity (S (sum (S O) O)).
apply sumS.
rewrite -> sum0.
reflexivity.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
intros.
intro.
elim H.
intros.
elim H3.
intros.
absurd (O = (S x)).
apply disc.
transitivity n;assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
intros.
rewrite prodS.
rewrite prod0.
apply sum0.  
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
intros.
unfold not.
intros.
absurd ((S n) = O).
intro.
apply (disc n).
symmetry.
assumption.
apply (inj).
assumption.
Qed.


Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
intros.
exists (S O).
do 2 rewrite -> prodS.
rewrite -> prod0.
rewrite -> sum0.
reflexivity.
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
intros.
unfold not.
intros.
elim (allNat n).
intros.
absurd (n = O); assumption.
intros.
elim H3.
intros.
absurd (S (sum m x) = O).
unfold not.
intros.
apply (disc (sum m x)).
symmetry.
assumption.
symmetry in H4.
rewrite H4 in H0.
rewrite sumS in H0.
assumption.
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
intros.
elim (allNat m).
intro.
elim (allNat n).
intros.
split; assumption.
intro.
elim H3.
intros.
symmetry in H4.
rewrite H4 in H.
rewrite sumS in H.
symmetry in H.
apply disc in H.
elim H.
intros.
elim H0.
intros.
elim (allNat n).
intros.
rewrite H4 in H.
rewrite sum0 in H.
split; assumption.
intros.
elim H4.
intros.
symmetry in H5.
rewrite H5 in H.
rewrite sumS in H.
symmetry in H.
apply (disc) in H.
elim H.
Qed.

End Ejercicio10.

