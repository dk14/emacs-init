Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).


Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B x => A (incr x)
  | A x => B x         
  end.

Example test_incr_1: incr(Z) = B Z.
Proof. simpl. reflexivity. Qed.

Example test_incr_2: incr(B (B Z)) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.


Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B Z => 1
  | B x => 1 + 2 * (bin_to_nat x)
  | A x => 2 * (bin_to_nat x)
  end.


Example test_bin_nat_1: bin_to_nat(A (B (B Z))) = 6.
Proof. simpl. reflexivity. Qed.

Example test_bin_nat_2: bin_to_nat(A (A (A (B Z)))) = 8.
Proof. simpl. reflexivity. Qed.

Compute incr(A (B (B Z))).

Example test_bin_inc_nat: bin_to_nat(incr(A (B (B Z)))) = 7.
Proof. simpl. reflexivity. Qed.


From TLC Require Import LibTactics.

Theorem test: forall code: bin, bin_to_nat(incr(code)) = 1 + bin_to_nat(code).
Proof.
intros n.
induction n as [|n'1 IHn1|n'2 IHn2].
- simpl. reflexivity.
- unfold incr. destruct n'1.
  * reflexivity.
  * simpl.
    auto.
  * simpl.
    auto.
- destruct n'2.
  * reflexivity.
  * simpl.
    simpl in IHn2.
    rewrite <- IHn2.
    destruct n'2. reflexivity. simpl. auto. simpl. auto.
  * simpl.
    simpl in IHn2.
    rewrite -> IHn2.
    destruct n'2. reflexivity. simpl. auto. simpl. auto.
Qed.



