Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Check true.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "~ x" := (negb x) (at level 75, right associativity).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => ~ b2
  | false => true
  end.


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check negb.

Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

Inductive megacolor : Type :=
| non_visible
| visible (v: color).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Definition isred (c : megacolor) : bool :=
  match c with
  | visible (primary red) => true
  | _ => false
  end.

Check visible (primary red).

Compute isred(visible (primary blue)).

Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.

  Inductive nat : Type :=
  | O
  | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Compute (pred (S (S O))).

End NatPlayground.

Check (S (S (S (S O)))).


Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 1).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Check evenb.

Definition oddb (n : nat) : bool := negb (evenb n).


Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.


  Compute (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.
  
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => S 0
  | S n' => mult n (factorial n')
  end.
  
                             
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  match leb n m with
  | false => false
  | true => leb (S n) m
  end.


                             
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 3) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Axiom plus_O_n : forall n : nat, 0 + n = n.


Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.
Qed.

Theorem plus_id_example : forall n m k:nat,
  n = m ->
  n + n = m + m.

Proof.
  intros a b c H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_O_n.
  reflexivity. Qed.



Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.

Proof.
  intros n m H.
  rewrite -> H.
  rewrite <- plus_1_l.
  reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Compute 1 + 1 =? S (S O).



Theorem plus_comm : forall a b: nat, a + b = b + a.
Proof.
  induction a as [| a0 a1].
  (* Case Z *)
  - induction b as [| b0 b1].
    + reflexivity.
    (* Case S b *)
    + simpl. rewrite <- b1. simpl. reflexivity.
  (* Case a = S a *)
  - induction b as [| b0 b1].
    (* Case Z  *)
    + simpl. rewrite (a1 0). reflexivity.
    (* Case S b *)
    + simpl. rewrite <- b1.
      simpl. rewrite (a1 (S b0)).
      simpl. rewrite (a1 b0).
      reflexivity.
Qed.

Theorem plus1: forall n, n + 1 = S n.
Proof. intros n. rewrite -> plus_comm. reflexivity. Qed.
  
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - simpl plus.
    reflexivity.
  - simpl plus.
    rewrite plus1.
    reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - simpl (negb true). reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' :
  forall n : nat,
    (n + 1) =? 0 = false.

Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 :
  forall b c : bool, b && c = true -> c = true.

Proof.
  intros b c H.
  destruct b.
  - destruct c.
    + reflexivity. 
    + rewrite <- H. reflexivity.
  - destruct c.
    + reflexivity.
    + rewrite <- H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 :
  forall n : nat, 0 =? (n + 1) = false.

Proof.
  intros []; repeat reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem neg_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  destruct b; repeat reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

Proof.
  
  intros b c H.
  destruct b, c; try reflexivity; try (simpl in H; rewrite H; reflexivity).
Qed.

Theorem andb_eq_orb' :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

Proof.
  
  intros b c.
  destruct b.
  
  - simpl. intros H1. rewrite H1. reflexivity.
  - simpl. intros H2. rewrite H2. reflexivity.
Qed.

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

Theorem plus_n_O_firsttry : forall n:nat,
    n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.


Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.  

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_comm2 : forall n m : nat,
    n + m = m + n.

Proof.
  intros n m.
  induction n as [| n' Ihn'], m as [ | m'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl.  rewrite -> Ihn'. simpl. rewrite plus_n_Sm. reflexivity.

Qed.

Theorem plus_comm3 : forall n m : nat,
    n + m = m + n.

Proof.
  intros n m.
  induction n as [| n' Ihn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - rewrite <- plus_n_Sm. rewrite <- Ihn'. simpl. reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .

Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem evenb_S :
  forall n : nat,
    evenb (S n) = negb (evenb n).

Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.


Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrites the wrong plus! *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.


Module Prods.
       
Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap :
  forall (p : natprod),
    (snd p, fst p) = swap_pair p.

Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd :
  forall (p : natprod),
    fst (swap_pair p) = snd p.

Proof.
  intros p. destruct p as [n m].
  simpl.
  reflexivity.
Qed.

End Prods.

Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (snd (pair 3 5)).

Notation "( x , y )" := (pair x y).



Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.


Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  destruct p. simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p.
  simpl swap_pair. simpl fst. simpl snd.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  destruct p.
  simpl swap_pair.
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.



Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].

Proof. reflexivity. Qed.

Fixpoint oddmembers (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
            | true => h :: (oddmembers t)
            | false => (oddmembers t)
            end
  end.
  
Example test_oddmembers:
  oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3].
Proof. reflexivity. Qed.

Definition countoddmembers (l: natlist) : nat :=
 length (oddmembers l).

  
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.


Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => match l2 with
            | nil => l1
            | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
              end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v: nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match (eqb v h) with
            | true => 1 + count(v) (t)
            | false => count(v) (t)
            end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match (count v s) with
  | 0 => false
  | _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match (eqb h v) with
            | true => t
            | false => h :: (remove_one v t)
            end
  end.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match (eqb h v) with
            | true => (remove_all v t)
            | false => h :: (remove_all v t)
            end
  end.


Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1, s2 with
  | nil, _ => true
  | _ , nil => false
  | h :: t, _  => match (member h s2) with
                | true => subset t (remove_one h s2)
                | false => false
                end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.



Theorem equality: forall (n: nat), eqb n n = true.
Proof. induction n. auto. auto. Qed.

Theorem bag_theorem: forall (n : nat) (bb : bag), (eqb (count n (n :: bb)) O) = false.

Proof.

simpl.
destruct n as [|n0].
- simpl. reflexivity.
- simpl.
  destruct bb.
  + simpl. induction n0.
    * simpl. reflexivity.
    * rewrite equality. reflexivity.
  + simpl eqb. rewrite equality. simpl. reflexivity.
Qed.


Theorem nil_app : forall l:natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    simpl length.
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl length.
    simpl pred.
    reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

Proof.

  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l =  *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.

intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl app.
    simpl length.
    simpl plus.
    reflexivity.
  - (* l1 = cons *)
    simpl app.
    simpl length.
    rewrite -> IHl1'.
    simpl plus.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.

  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length. simpl. rewrite -> plus_comm. simpl.
    simpl. rewrite -> IHl'. reflexivity.
Qed.



Search rev.


Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  induction l.
  - simpl app. reflexivity.
  - simpl app. rewrite -> IHl. reflexivity.
Qed.

Search app.


Theorem rev_l : forall l: natlist, forall n: nat, rev (n :: l) = rev (l) ++ [n].
Proof. reflexivity. Qed.
  


Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1.
  - simpl. destruct l2. reflexivity. simpl. rewrite  app_nil_r. reflexivity.  
  - simpl. destruct l2 as [| n' l2'].
    + simpl. rewrite app_nil_r. reflexivity.
    + rewrite IHl1. simpl. rewrite app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.




Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  simpl.
  induction l1.
  - simpl. reflexivity.
  - induction  n.
    + simpl. induction l2.
      * simpl. rewrite app_nil_r. rewrite app_nil_r. reflexivity.
      * rewrite <- IHl1. reflexivity.
    + simpl. induction l2.
      * simpl. rewrite app_nil_r. rewrite app_nil_r. reflexivity.
      * rewrite IHl1. reflexivity.
Qed.


Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1 :: t1, h2 :: t2 => match (eqb h1 h2) with
                       | true => (eqblist t1 t2)
                       | false => false
                       end
  end.

Example test_eqblist1 : (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
    true = eqblist l l.

Proof.
  induction l.

  - simpl. reflexivity.
  - simpl. rewrite equality. rewrite IHl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.

Proof.
  simpl.
  reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  induction s.

  - simpl. reflexivity.
  - simpl. destruct n.
    + simpl. rewrite leb_n_Sn. reflexivity.
    + simpl. rewrite IHs. reflexivity.
Qed.


Theorem sum_zero : forall (s : bag), (sum s []) = s.
Proof.
  induction s.
  - reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.


Theorem bag_count_sum : forall (s1 s2 : bag) (n: nat),
    (count n s1) + (count n s2) = count n (sum s1 s2).

Proof.
  induction s1 as [| n1 t1 IHs1].
  - simpl. reflexivity.
  - simpl. induction n.
    + rewrite <- IHs1. destruct n1.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + rewrite <- IHs1. destruct n1.
      * simpl. reflexivity.
      * simpl. destruct (n =? n1). reflexivity. reflexivity. 
Qed.


Theorem injective_rev_rev : forall (l1 l2 : natlist), l1 = l2 -> rev l1 = rev l2.
Proof.
  intros l1 l2 H1.
  rewrite H1.
  reflexivity.
Qed.

Theorem injective_rev : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H1.
  apply injective_rev_rev in H1.
  repeat rewrite rev_involutive in H1.
  rewrite <- H1.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End NatList.


Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  destruct x. simpl. rewrite NatList.equality. reflexivity.
Qed.

Module PartialMap.
Export NatList.
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.



Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  simpl. destruct x. rewrite <- eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H1.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

End PartialMap.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

Set Warnings "-notation-overridden,-parsing".

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.

Check boollist.

Check (nil nat).

Check (cons nat 3 (nil nat)).

Check nil.

Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X : Type) : Type :=
  | d (m : mumble)
  | e (x : X).

Check b a 5.

Check d bool (b a 5).

Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Check c.

  
End MumbleGrumble.


Fixpoint repeat' X x count :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.

Check repeat.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} _ _.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (@repeat''' X x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. destruct m, n. all: rewrite IHl ; reflexivity. 
Qed.

Lemma app_length : forall X (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1.
  - simpl. reflexivity.
  - simpl. destruct l2. all: rewrite IHl1 ; reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1.
  - simpl. destruct l2. all: rewrite app_nil_r; reflexivity.
  - simpl. destruct l2. all: rewrite IHl1, app_assoc; reflexivity.
Qed.


Theorem rev_app_distr_gen: forall X, forall l1 l2 : list X,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1.
  - simpl. destruct l2. reflexivity. simpl. rewrite  app_nil_r. reflexivity.  
  - simpl. destruct l2.
    + simpl. rewrite app_nil_r. reflexivity.
    + rewrite IHl1. simpl. rewrite app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr_gen. rewrite IHl. simpl. reflexivity.
Qed.




Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.


Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (l, r) :: t => match (split t) with
                 | (ll, rr) => (l :: ll, r :: rr)
                 end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.

Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: t => Some h
  end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
                                                     
Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.


Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (evenb n) && (negb (n <=? 7))) l.
    
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool)(l : list X) : list X * list X :=
  ((filter test l), (filter (fun x => negb (test x)) l)).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.


Lemma destruct_map_list : forall X Y (f: X -> Y) (h: X) (t: list X),
    map f (t ++ [h]) = map f t ++ [f h].
Proof.
  simpl.
  induction t.
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

  
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. rewrite <- destruct_map_list. reflexivity.
Qed.


Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X): (list Y) :=
  match l with
  | nil => nil
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.


Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb).

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k: nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

  Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun _ n => S n) l 0.

  Example test_fold_length1 : fold_length [4;7;0] = 3.
  Proof. reflexivity. Qed.

  Theorem fold_length_correct : forall X (l : list X),
      fold_length l = length l.
  Proof.
    induction l.
    - simpl. unfold fold_length. simpl. reflexivity.
    - simpl. rewrite <- IHl. unfold fold_length. simpl. reflexivity.
  Qed.

  Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
    fold (fun x l' => (f x) :: l') l [].

  Theorem fold_map_correct: forall X Y (l: list X) (f: X -> Y),
      fold_map f l = map f l.
  Proof.
    induction l.
    - simpl. unfold fold_map. simpl. reflexivity.
    - simpl. intros f. rewrite <- IHl. reflexivity.
  Qed.

  Definition prod_curry {X Y Z : Type}
             (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

  Definition prod_uncurry {X Y Z : Type}
             (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

  Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
  Proof. reflexivity. Qed.

  Check @prod_curry.
  Check @prod_uncurry.

  Theorem uncurry_curry : forall (X Y Z : Type)
                            (f : X -> Y -> Z)
                            x y,
      prod_curry (prod_uncurry f) x y = f x y.
  Proof.
    intros X Y Z f x y.
    unfold prod_curry.
    unfold prod_uncurry.
    simpl.
    reflexivity.
  Qed.

  Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
      prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros X Y Z f p.
    unfold prod_uncurry.
    unfold prod_curry.
    destruct p.
    simpl.
    reflexivity.
  Qed.

  Theorem out_of_bound: forall X n l, length l = n -> @nth_error X l n = None.
    intros X n l H.
    destruct H.
    induction l.
    -  simpl. reflexivity.
    - simpl. rewrite <- IHl. reflexivity.
  Qed.

  Module Church.
    Definition cnat := forall X : Type, (X -> X) -> X -> X.

    Definition one : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f x.

    Definition two : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f (f x).

    Definition zero : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => x.

    Definition three : cnat := @doit3times.

    Definition succ (n : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

    Example succ_1 : succ zero = one.
    Proof. simpl. unfold succ. unfold one. unfold zero. reflexivity. Qed.

    Example succ_2 : succ one = two.
    Proof. simpl. unfold succ. unfold two. unfold one. reflexivity. Qed.

    Example succ_3 : succ two = three.
    Proof. simpl. unfold succ. unfold three. unfold two. reflexivity. Qed.



    Definition plus (n m : cnat) : cnat :=
      fun (X : Type) (f: X -> X) (x: X) => n X f (m X f x).

    Example plus_1 : plus zero one = one.
    Proof. reflexivity. Qed.

    Example plus_2 : plus two three = plus three two.
    Proof. reflexivity. Qed.

    Example plus_3 :
      plus (plus two two) three = plus one (plus three three).
    Proof. reflexivity. Qed.

    Definition mult (n m : cnat) : cnat :=
      fun (X : Type) (f: X -> X) => n X (m X f).

    Example mult_1 : mult one one = one.
    Proof. reflexivity. Qed.

    Example mult_2 : mult zero (plus three three) = zero.
    Proof. reflexivity. Qed.

    Example mult_3 : mult two three = plus three three.
    Proof. reflexivity. Qed.

    
    Definition exp (n m : cnat) : cnat :=
      fun (X : Type) (f: X -> X) => m (X -> X) ((n X)) f.
    

    Example exp_1 : exp two two = plus two two.
    Proof. unfold exp. unfold plus. unfold mult. unfold two. unfold one. reflexivity. Qed.
        
    Example exp_2 : exp three zero = one.
    Proof.  unfold exp. unfold mult. unfold zero. unfold one. reflexivity. Qed.

    Example exp_3 : exp three two = plus (mult two (mult two two)) one.
    Proof. reflexivity. Qed.

  End Church.
End Exercises.



Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq2.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with m. apply H0. apply H.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  injection H0 as H3 H4.
  symmetry.
  apply H3.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - simpl.
    intros. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  simpl in H. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.
Qed.





Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m H. destruct m.  reflexivity. discriminate H.
  - destruct m as [| m'].
    + simpl. intros H. discriminate H.
    + intros H.
      apply f_equal.
      apply IHn'.
      repeat rewrite <- plus_n_Sm in H.
      simpl in H.
      repeat apply S_injective in H.
      apply H.
Qed.

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + simpl. discriminate eq.
    + apply f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal.
Qed.


Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n.
  - intros m H. destruct m.
    * reflexivity.
    * discriminate H.
  - intros m H. destruct m.
    * discriminate H.
    * apply f_equal. apply IHn. simpl in H. apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.


Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal.
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  - simpl. reflexivity.
  - intros n H. rewrite <- H. simpl. apply IHl. reflexivity.
Qed.


Definition square n := n * n.


Theorem mult_S: forall a b, S a * b = a * b + b.
  simpl.
  induction a.
  - simpl. intros b. rewrite plus_comm. simpl. reflexivity.
  - intros b. simpl. rewrite IHa. rewrite plus_comm. reflexivity.
Qed.


Theorem plus_S_a_b: forall a b, S a + b = a + S b.
Proof.
  simpl.
  induction a.
  - simpl. reflexivity.
  - simpl. intros b. rewrite IHa. reflexivity.
Qed.

Theorem mult_comm: forall a b, a * b = b * a.
Proof.
  induction a.
  - simpl. intros b. rewrite mult_0_r. reflexivity.
  - simpl. intros b. rewrite IHa. induction b.
    + simpl. reflexivity.
    + rewrite mult_S. rewrite plus_comm. rewrite mult_S.
      rewrite <- IHb. rewrite <- IHa. rewrite (plus_comm b).
      rewrite (plus_comm _ (S b)).
      rewrite (plus_comm _ b).
      repeat rewrite plus_assoc.
      rewrite (plus_comm _ (S a)).
      rewrite (plus_comm _ a).
      repeat rewrite plus_assoc.
      rewrite plus_S_a_b.
      reflexivity.
Qed.

Theorem mult_distrib: forall a b c, a * (b + c) = a * b + a * c.
Proof.
  induction a.
  - simpl. reflexivity.
  - intros b c. rewrite mult_S. rewrite mult_S. rewrite mult_S.
    rewrite IHa.
    repeat rewrite plus_assoc.
    repeat rewrite (plus_comm _ b).
    repeat rewrite plus_assoc.
    reflexivity.
Qed.

Theorem mult_1n : forall n, n = 1 * n.
Proof. simpl. intros n. rewrite <- plus_comm. simpl. reflexivity. Qed.

Theorem mult_assoc: forall a b c, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  induction a, b, c.
  1, 2, 3, 4, 5, 6, 7: simpl.
  5, 6: rewrite <- IHa. simpl.
  1, 2, 3, 4, 5, 6: reflexivity.
  - repeat rewrite mult_0_r. simpl. reflexivity.
  - rewrite mult_S. rewrite IHa.
    repeat rewrite (mult_comm _ (S c)).
    rewrite <- mult_distrib.
    rewrite <- mult_S.
    reflexivity.
Qed.
    
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc.
  reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.
Qed.



Lemma split_nil: forall (X: Type) (Y: Type), @split X Y [] = ([], []).
Proof. reflexivity. Qed.

Lemma xplit_nil_reason:  forall (X: Type) (Y: Type) (l: list (X * Y)) (xx: list Y),
    @split X Y l = ([], xx) -> l = [].
Proof.
  intros X Y l xx H.
  induction l.
  -  reflexivity.
  - destruct x. simpl in H. rewrite IHl in H.
    * simpl in H. discriminate.
    * rewrite <- H. destruct (split l). discriminate H.
Qed.


Lemma xplit_nil_reason_2:  forall (X: Type) (Y: Type) (l: list (X * Y)) (xx: list X),
    @split X Y l = (xx, []) -> l = [].
Proof.
  intros X Y l xx H.
  induction l.
  -  reflexivity.
  - destruct x. simpl in H. rewrite IHl in H.
    * simpl in H. discriminate.
    * rewrite <- H. destruct (split l). discriminate H.
Qed.
  

Lemma tuples: forall X (x : X) (y: X), (x, x) = (y, y) -> x = y.
Proof. intros X x y H. injection H as H1 H2. apply H1. Qed.


Theorem to_fst: forall X Y (x: X) (y: Y) (t: X * Y), (x, y) = t -> x = fst t.  
Proof. intros X Y x y t H. symmetry in H. rewrite H. simpl. reflexivity. Qed.


Theorem to_snd: forall X Y (x: X) (y: Y) (t: X * Y), (x, y) = t -> y = snd t.  
Proof. intros X Y x y t H. symmetry in H. rewrite H. simpl. reflexivity. Qed.


Theorem combine_tup: forall X Y (x: X) (y: Y) (l: list (X * Y)),
    combine (fst (split ((x, y) :: l))) (snd (split ((x, y) :: l))) = (x, y) :: l.
Proof.
  induction l.
  - simpl. reflexivity.
  - destruct x0. simpl in *. destruct (split l) in *. simpl in *.
    destruct (combine x1 y1) in *.
    * injection IHl as H1. symmetry in H1. rewrite H1. reflexivity.
    * injection IHl as H1. symmetry in H1. rewrite H1. reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.

  induction l.
  - intros l1 l2 H. simpl in H. injection H as H1 H2. rewrite <- H1, <- H2. simpl. reflexivity.
  - intros l1' l2' H. induction l1', l2'.
    * apply xplit_nil_reason in H. discriminate H.
    * apply xplit_nil_reason in H. discriminate H.
    * apply xplit_nil_reason_2 in H. discriminate H.
    * symmetry in H. apply to_fst in H as H1. apply to_snd in H as H2.
      rewrite  H1. rewrite H2.
      destruct x.
      apply combine_tup.
Qed.
      
Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
       else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        eqn: again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.
Qed.


Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn:Hf.
  - destruct b.
    * rewrite Hf. rewrite Hf. reflexivity.
    * rewrite <- Hf. destruct (f false) eqn:Hff.
      ** destruct (f true) eqn:Hfff.
         *** rewrite Hfff. reflexivity.
         *** rewrite Hff. reflexivity.
      ** rewrite Hff. rewrite Hff. reflexivity.
  - destruct b.
    * destruct (f false) eqn:Hff.
      ** rewrite Hf. reflexivity.
      ** rewrite Hff. reflexivity.
    * rewrite Hf. rewrite Hf. reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  induction n, m.
  -  simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. apply IHn.
Qed.


Lemma idd: forall n, n =? n = true.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

    
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  induction n, m, p.
  1,2,3,4,5,6,7,8:simpl.
  1,3: reflexivity.
  intros H1 H2. discriminate H2.
  1, 2, 3 : intros H; discriminate H.
  - intros H1 H2. discriminate H2.
  - intros H1 H2. apply eqb_true in H1. apply eqb_true in H2.
    symmetry in H2. rewrite H1, H2. apply idd.
Qed.

Definition empty {X} (l: list X) :=
  match l with
  | [] => true
  | _ => false
  end.

Definition split_combine_statement : Prop :=
  forall X Y (l1: list X) (l2: list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).



Theorem detuple : forall X Y (x : X) (y : Y) (t : X * Y),
    x = fst t -> y = snd t -> (x, y) = t.
Proof.
  intros X Y x y t H1 H2.
  rewrite H1, H2.
  destruct t.
  simpl.
  reflexivity.
Qed.

Theorem zero_length: forall X (l: list X), length l = 0 -> l = [].
Proof.
  intros X l H.
  destruct l.
  - reflexivity.
  - simpl in H. discriminate H.
Qed.

Theorem tail_eq: forall X (x : X) (l1 : list X) (l2 : list X),
    l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros X x l1 l2 H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y.
  induction l1.

  - simpl. intros l2 H. symmetry in H. apply zero_length in H.
    rewrite H. reflexivity.
  - intros l2 H. simpl in *. destruct l2.
    * simpl in H. discriminate H.
    * simpl in *.
      injection H as H.
      symmetry. apply detuple.
      ** simpl. destruct (split (combine l1 l2))  eqn:Hh. simpl.
         symmetry in Hh. apply to_fst in Hh. rewrite Hh.
         apply tail_eq.
         rewrite IHl1.
         *** simpl. reflexivity.
         *** rewrite <- H. reflexivity.
      ** simpl. destruct (split (combine l1 l2)) eqn:Hh. simpl.
         symmetry in Hh. apply to_snd in Hh. rewrite Hh.
         apply tail_eq.
         rewrite IHl1.
         *** simpl. reflexivity.
         *** rewrite <- H. reflexivity.
Qed.

Theorem filter_properly_defined: forall X (x: X) (l : list X) (test : X -> bool),
    hd_error (filter test l) = Some x -> test x = true.
Proof.
  intros X x l test H.
  induction l.
  - simpl in H. discriminate H.
  - simpl in H. destruct (test x0) eqn: HH in H.
    * simpl in H. injection H as H. rewrite <- H. apply HH.
    * rewrite H in IHl. apply IHl. reflexivity.
Qed.

Theorem convert: forall X (l: list X) (r: list X),
    l = r -> hd_error l = hd_error r.
Proof. intros X l r H. rewrite H. reflexivity. Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf H.
  apply convert in H. simpl in H. apply filter_properly_defined in H. apply H.
Qed.


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => match (test h) with
            | true => forallb test t
            | false => false
            end
  end.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => match (test h) with
            | true => true
            | false => existsb test t
            end
  end.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  unfold existsb'.
  induction l.
  - simpl. reflexivity.
  - simpl. destruct (test x).
    * simpl. reflexivity.
    * simpl. rewrite <- IHl. reflexivity.
Qed.



Check 3 = 3.

Check forall n m : nat, n + m = m + n.

Check 2 = 2.

Check forall n : nat, n = 2.

Check 3 = 4.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

Check @eq.

Check 3 = 3.

Check forall n m : nat, n + m = m + n.

Check 2 = 2.

Check forall n : nat, n = 2.

Check 3 = 4.

Example and_example : (3 + 4 = 7) /\ (2 * 2 = 4).

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  apply and_intro.
  - destruct m.
    * rewrite plus_comm in H. simpl in H. apply H.
    * rewrite plus_comm in H. discriminate H.
  - destruct n.
    * simpl in H. apply H.
    * discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    * apply HP.
    * apply HQ.
  - apply HR.
Qed.

Check and.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 \/ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros PProp NotP QProp P.
  destruct NotP.
  apply P.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~ ~ P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H H1.
  unfold not.
  unfold not in H1.
  intros H2.
  apply H1 in H.
  - destruct H.
  - apply H2.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  destruct H.
  apply H0 in H.
  destruct H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    exfalso.
    unfold not in H.
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.


Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [H1| H2].
    * split.
      ** left. apply H1.
      ** left. apply H1.
    * split.
      ** right. apply H2.
      ** right. apply H2.
  - intros [H1  H2]. destruct H1, H2.
    * left. apply H.
    * left. apply H.
    * left. apply H0.
    * right. split.
      ** apply H.
      ** apply H0.
Qed.

From Coq Require Import Setoids.Setoid.


Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m. destruct n as [|n']. 
    + intros _. left. reflexivity.
    + destruct m as [|m'].
        - intros _. right. reflexivity.
        - intros contra. discriminate contra.
Qed.   

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite <- or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H. (* note implicit destruct here *)
  destruct H as [m].
  exists (2 + m).
  apply H.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not (P x)).
Proof.
  intros X P.
  unfold not.
  intros H1 [x].
  apply H.
  apply H1.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros H. destruct H.  destruct H.
    * left. exists x. apply H.
    * right. exists x. apply H.
  - intros H. destruct H.
    * destruct H. exists x. left. apply H.
    * destruct H. exists x. right. apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | L]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
  - exfalso. apply L.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma or_eq : forall X (x: X), (x = x) <-> True.
Proof.
  intros X x.
  split.
  - intros H. apply I.
  - intros H. reflexivity.
Qed.

Lemma or_true : forall P : Prop, (True \/ P) <-> True.
Proof.
  intros P.
  split.
  - intros H. apply I.
  - intros H. left. apply I.
Qed.

Lemma and_true : forall P : Prop, (P /\ True) <-> P.
Proof.
  intros P.
  split.
  - intros H. destruct H. apply H.
  - intros H. split.
    * apply H.
    * apply I.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  induction l.
  - simpl. split.
    * intros [].
    * intros H. destruct H. destruct H. apply H0.
  - simpl. split.
    * intros [H | H].
      ** exists x. split.
         *** apply H.
         *** left. reflexivity.
      ** destruct IHl. apply H0 in H. destruct H.
         exists x0. destruct H. split.
         *** apply H.
         *** right. apply H2.
    * intros H. destruct H. destruct H. destruct H0.
      ** left. rewrite <- H0 in H. apply H.
      ** right. apply IHl. exists x0. split.
         *** apply H.
         *** apply H0.
Qed.

Lemma false_or : forall P : Prop, False \/ P <-> P.
Proof.
  intros P.
  split.
  - intros H. destruct H.
    * exfalso. apply H.
    * apply H.
  -  intros H. right. apply H.
Qed.

Axiom list_app_zero: forall X (l : list X), l ++ [] = l.

Lemma or_false : forall P : Prop, P \/ False <-> P.
Proof.
  intros P.
  split.
  - intros H. destruct H.
    * apply H.
    * exfalso. apply H.
  -  intros H. left. apply H.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  induction l.
  - simpl. rewrite false_or. reflexivity.
  - simpl. rewrite <- or_assoc. split.
    * intros H. induction l'.
      ** simpl. rewrite or_false. rewrite list_app_zero in H. apply H.
      ** simpl. rewrite IHl in H. simpl in H. apply H.
    * intros H. induction l'.
      ** simpl. rewrite list_app_zero in *. simpl in *. rewrite or_false in *. apply H.
      ** simpl in *. rewrite <- IHl in H. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => (P h) /\ (All P t)
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  induction l.
  - simpl. split.
    * intros _. apply I.
    * intros _ x H. exfalso. apply H.
  - simpl in *. rewrite <- IHl. split.
    * intros H. split.
      ** apply H. left. reflexivity.
      ** intros x0. intros H2. apply H. right. apply H2.
    * intros H. intros x0. intros H1. destruct H. destruct H1.
      ** rewrite <- H1. apply H.
      ** apply H0. apply H1.
Qed.


Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (fun n => if (oddb n) then Podd n else Peven n).

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (oddb n).
  - intros H1 H2. apply H1. reflexivity.
  - intros H1 H2. apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (oddb n).
  - intros H _. apply H.
  - intros _ H. discriminate H.
Qed.
         
Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  unfold combine_odd_even.
  destruct (oddb n).
  - intros _ H. discriminate H.
  - intros H _. apply H.
Qed.

Check plus_comm.

Lemma plus_comm33 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  (* WORKED IN CLASS *)
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. simpl. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].


Theorem delist: forall X (x : X) (l : list X), x :: l = [x] ++ l.
Proof. reflexivity. Qed.

Lemma rev_append_acc : forall X (a b: list X),
    rev_append a b = rev_append a [] ++ b.
Proof.
  intros X a.
  induction a.
  - simpl. reflexivity.
  - simpl. intros b. rewrite IHa with (x :: b).
    rewrite IHa with [x].
    rewrite delist. rewrite app_assoc.
    reflexivity.
Qed.
      
Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  unfold tr_rev.
  intros l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. rewrite rev_append_acc. reflexivity.
Qed. 
   
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k.
  induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.


Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n.
  induction n.
  - simpl. exists 0. reflexivity.
  - rewrite evenb_S. destruct evenb.
    * simpl. destruct IHn. exists x. apply eq_S. apply H.
    * simpl. destruct IHn. rewrite H. exists (S x). simpl. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. destruct H. induction n1.
    * simpl. reflexivity.
    * simpl. apply IHn1.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2: bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  - intros H. split.
    * destruct b1.
      ** reflexivity.
      ** simpl in H. discriminate H.
    * destruct b2.
      ** reflexivity.
      ** rewrite andb_commutative in H. simpl in H. discriminate H.
  - intros H. destruct b1, b2.
    * simpl. reflexivity.
    * destruct H. discriminate H0.
    * destruct H. discriminate H.
    * destruct H. discriminate H.
Qed.

Lemma or_b_commutative: forall (a b : bool), a || b = b || a.
Proof. intros a b. destruct a.
       - simpl. destruct b. all: reflexivity.
       - simpl. destruct b. all: reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  - intros H. destruct b1.
    * left. reflexivity.
    * simpl in H. right. apply H.
  - intros H. destruct H.
    * rewrite H. simpl. reflexivity.
    * rewrite H. rewrite or_b_commutative. simpl. reflexivity.
Qed.

Theorem eq_x_x : forall x, x =? x = true.
Proof. intros x. induction x.
       - simpl. reflexivity.
       - simpl. apply IHx.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  
  split.
  - intros H. unfold not. intros H1. rewrite H1 in H. rewrite eq_x_x in H. discriminate H.
  - intros H. unfold not in H. rewrite <- eqb_eq in H. destruct eqb.
    * exfalso. apply H. reflexivity.
    * reflexivity.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | h1 :: t1, h2 :: t2 => eqb h1 h2 && eqb_list eqb t1 t2
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H l1.
  induction l1.
  - intros l2. destruct l2.
    * simpl. split. intros H1. reflexivity. intros H2. reflexivity.
    * simpl. split. intros H1. discriminate H1. intros H2. discriminate H2.
  - induction l2.
    * simpl. split. intros H1. discriminate H1. intros H2. discriminate H2.
    * simpl. rewrite andb_true_iff. split.
      ** intros H1. destruct H1. rewrite H in H0.
         rewrite H0. rewrite IHl1 in H1. rewrite H1.
         reflexivity.
      ** intros H2. injection H2 as HH1 HH2. split.
         *** rewrite HH1. rewrite H. reflexivity.
         *** rewrite IHl1. apply HH2.
Qed.

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.

intros X test l.
induction l.
- simpl. split. intros _. apply I. intros _. reflexivity.
- simpl. split.
  * destruct test.
    ** intros H. split.
       *** reflexivity.
       *** apply IHl. apply H.
    ** intros H. discriminate H.
  * destruct test.
    ** intros H. destruct H. apply IHl. apply H0.
    ** intros H. destruct H. discriminate H.
Qed.

Definition excluded_middle := forall P : Prop,
    P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H.  intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~~(P \/ ~P).
Proof.
  intros P.
  intros H. unfold not in H. apply H. right. intros H2. apply H. left. apply H2.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    not (exists x, not (P x)) -> (forall x, P x).
Proof.
  intros EM.
  intros X P.
  intros H.
  intros x.
  destruct EM with (P x).
  - apply H0.
  - destruct H. exists x. apply H0.
Qed.

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
    (P->Q) -> (~P\/Q).

Theorem classic_to_peirce:
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle.
  unfold peirce.
  intros H. intros P. destruct H with P.
  * intros Q. intros H1. apply H0.
  * intros Q. intros H1. unfold not in H0. apply H1.
    intros H2. exfalso. apply H0. apply H2.
Qed.
                     
Theorem classic_to_dneg:
  excluded_middle -> double_negation_elimination.
Proof.
  unfold excluded_middle.
  unfold double_negation_elimination.
  intros H. intros P. destruct H with P.
  - intros H1. apply H0.
  - intros H1. apply H1 in H0. exfalso. apply H0.
Qed.

Theorem classic_to_de_morgan:
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle.
  unfold de_morgan_not_and_not.
  intros H. intros P Q. destruct H with P.
  - intros H1. left. apply H0.
  - destruct H with Q.
    * intros H2. right. apply H1.
    * intros H2. unfold not in *.  exfalso. apply H2. split.
      ** apply H0.
      ** apply H1.
Qed.

Theorem classic_to_implies_to_or:
  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle.
  unfold implies_to_or.
  intros H. intros P Q. destruct H with P.
  - intros H1. right. apply H1. apply H0.
  - intros H1. left. apply H0.
Qed.

Theorem implies_to_or_to_classic:
  implies_to_or -> excluded_middle.
Proof.
  unfold excluded_middle.
  unfold implies_to_or.
  intros H. intros P.
  destruct H with P P.
  - intros H0. apply H0.
  - right. apply H0.
  - left. apply H0.
Qed.

Theorem implies_classic_eqv:
  implies_to_or <-> excluded_middle.
Proof. split. apply implies_to_or_to_classic. apply classic_to_implies_to_or. Qed.

Theorem de_morgan_to_implies:
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  intros H. intros P Q.
  intros H0. apply H.
  unfold not.
  intros H1. destruct H1. destruct H1.
  intros H3. apply H2. apply H0. apply H3.
Qed.

Theorem demorgan_classic_eqv:
  de_morgan_not_and_not <-> excluded_middle.
Proof.
  split.
  - rewrite <- implies_classic_eqv. apply de_morgan_to_implies.
  - apply classic_to_de_morgan.
Qed.

Theorem dneg_to_classic:
  double_negation_elimination -> excluded_middle.
Proof.
  unfold double_negation_elimination.
  unfold excluded_middle.
  intros H. intros P.
  apply H.
  apply excluded_middle_irrefutable.
Qed.

Theorem dneg_classic_eqv:
  double_negation_elimination <-> excluded_middle.
Proof. split. apply dneg_to_classic. apply classic_to_dneg. Qed.

Theorem peirce_to_dneg:
  peirce -> double_negation_elimination.
Proof.
  unfold peirce.
  unfold double_negation_elimination.
  intros H P.
  unfold not.
  intros H0.
  apply H with False.
  intros H1.
  exfalso.
  apply H0.
  apply H1.
Qed.

Theorem peirce_classic_eqv:
  peirce <-> excluded_middle.

Proof.
  split.
  - rewrite <- dneg_classic_eqv. apply peirce_to_dneg.
  - apply classic_to_peirce.
Qed.

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).

Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n, even n -> even (S (S n)).
  
Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  even (double n).
Proof.
  intros n. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
    even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~even 1.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)
Abort.

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m H1 H2.
  induction H1, H2.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply H2.
  - rewrite plus_comm in *. simpl in *. apply ev_SS. apply H1.
  - simpl. apply ev_SS. apply IHeven.
Qed.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intros n.
  split.
  - intros H. induction H.
    * apply ev_0.
    * apply ev_SS. apply ev_0.
    * apply ev_sum.
      ** apply IHeven'1.
      ** apply IHeven'2.
  - intros H. induction H.
    * apply even'_0.
    * assert (H2 : forall n, S (S n) = n + 2).
      { intros n0. rewrite plus_comm. simpl. reflexivity. }
      rewrite H2. apply even'_sum.
      ** apply IHeven.
      ** apply even'_2.
Qed.

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m H H1.
  induction H1.
  - simpl in *. apply H.
  - apply IHeven. simpl in H. apply evSS_ev in H. apply H.
Qed.

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros n m p H1 H2.
  apply (ev_ev__ev (n + p)).
  - rewrite (plus_comm _ p). rewrite (plus_comm _ p). rewrite plus_assoc.
    rewrite (plus_comm _ p). rewrite plus_assoc. rewrite <- double_plus.
    rewrite plus_comm. rewrite plus_assoc. rewrite plus_comm. rewrite plus_assoc.
    apply ev_sum.
    *  apply H1.
    * apply ev_double.
  - apply H2.
Qed.

Module Playground.

  Inductive le : nat -> nat -> Prop :=
  | le_n n: le n n
  | le_S n m (H : le n m) : le n (S m).

  Notation "m <= n" := (le m n).


  Theorem test_le1 : 3 <= 3.
  Proof. apply (le_n 3). Qed.

  Theorem test_le2 :
    3 <= 6.
  Proof.
    apply (le_S 3 5).
    apply (le_S 3 4).
    apply (le_S 3 3).
    apply (le_n 3).
  Qed.

  Theorem test_le3 :
    (4 <= 2) -> 2 + 2 = 5.
  Proof.
    intros H.
    inversion H.
    inversion H2.
    inversion H5.
  Qed.

End Playground.

Definition lt (n m:nat) := le (S n) m.
Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).
Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).
Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop := total n m : total_relation n m.

Definition empty_relation (n m : nat) := False.

Lemma tot : forall (n m : nat), total_relation n m.
Proof. intros n m. apply total. Qed.

Lemma empt : forall (n m : nat), not (empty_relation n m).
Proof. intros n m. unfold not. intros H. inversion H. Qed.

Theorem n_le_m__Sn_le_Sm: forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
    * apply le_n.
    * apply le_S. apply IHle.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  induction m.
  - inversion H. apply le_n. inversion H1. 
  - inversion H.
    * apply le_n.
    * apply le_S. apply IHm. apply H1.
Qed.

Theorem le_eqv: forall n m, n <= m <-> S n <= S m.
Proof.
  split. apply n_le_m__Sn_le_Sm. apply Sn_le_Sm__n_le_m. Qed.
        
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1.
  induction H1.
  - intros H2. apply H2.
  - intros H2. apply IHle. apply Sn_le_Sm__n_le_m. apply le_S. apply H2.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  -  apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  induction b.
  - rewrite plus_comm. simpl. apply le_n.
  - rewrite plus_comm. simpl. rewrite plus_comm. apply le_S. apply IHb.
Qed.

Theorem not_le: forall n m : nat,  not (S n + m <= n).
Proof.
  intros n m.
  unfold not.
  intros H.
  induction n, m.
  - simpl in *. inversion H.
  - simpl in *. inversion H.
  - simpl in *. rewrite plus_comm in *. simpl in *. apply Sn_le_Sm__n_le_m in H.
    apply IHn. apply H.
  - apply IHn. simpl in H. apply Sn_le_Sm__n_le_m in H. simpl. apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  split.
  - induction n1, n2.
    * simpl in H. apply H.
    * simpl in H. inversion H.
      ** apply n_le_m__Sn_le_Sm. apply O_le_n.
      ** apply n_le_m__Sn_le_Sm. apply O_le_n.
    * simpl in *. rewrite plus_comm in *. simpl in *. apply H.
    * destruct IHn1.
      ** simpl in H. apply Sn_le_Sm__n_le_m. apply le_S. apply H.
      ** apply Sn_le_Sm__n_le_m in H. apply not_le in H. exfalso. apply H.
      ** apply n_le_m__Sn_le_Sm in l. apply l.
  - rewrite plus_comm in H. induction n2, n1.
    * simpl in H. apply H.
    * simpl in H. inversion H.
      ** apply n_le_m__Sn_le_Sm. apply O_le_n.
      ** apply n_le_m__Sn_le_Sm. apply O_le_n.
    * simpl in *. rewrite plus_comm in *. simpl in *. apply H.
    * destruct IHn2.
      ** simpl in H. apply Sn_le_Sm__n_le_m. apply le_S. apply H.
      ** apply Sn_le_Sm__n_le_m in H. apply not_le in H. exfalso. apply H.
      ** apply n_le_m__Sn_le_Sm in l. apply l.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros n m H. apply le_S. unfold lt in H. apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n.
  - intros m H. apply O_le_n.
  - intros m H. induction m.
    * simpl in *. discriminate H.
    * rewrite <- le_eqv.
      apply IHn.
      inversion H.
      reflexivity.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m H.
  generalize dependent n.
  induction m.
  - intros n H. induction n.
    * simpl. reflexivity.
    * simpl in *. inversion H.
  - intros n H. induction n.
    * simpl. reflexivity.
    * simpl in *. apply IHm.
      rewrite le_eqv.
      apply H.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split. apply leb_complete. apply leb_correct.
Qed.


Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o.
  repeat rewrite leb_iff. apply le_trans.
Qed.

Module R.

  Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

  Lemma R1: R 1 1 2.
  Proof. apply c2. apply c3. apply c1. Qed.
  Lemma R2: R 2 2 6.
  Proof. apply c2. apply c2. apply c3. apply c3. Abort.

  Definition fR : nat -> nat -> nat := plus.

  Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
  Proof.
    unfold fR.
    split.
    - intros H. induction H.
      * simpl. reflexivity.
      * rewrite <- IHR. simpl. reflexivity.
      * rewrite <- IHR. rewrite plus_comm. simpl. rewrite plus_comm. reflexivity.
      * simpl in IHR. injection IHR as IHR2. rewrite plus_comm in IHR2.
        simpl in IHR2. injection IHR2 as IHR3. rewrite plus_comm. apply IHR3.
      * rewrite plus_comm. apply IHR.
    - generalize dependent n. generalize dependent m. induction o.
      * induction m.
        ** intros n H. simpl in *. rewrite H. apply c1.
        ** intros n H. discriminate H.
      * induction m.
        ** intros n H. simpl in *. rewrite H. apply c3. apply IHo. simpl. reflexivity.
        ** intros n H. apply c2. apply IHo. simpl in H. injection H as H1. apply H1.
  Qed.

End R.

Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

Example r1: R 2 [1;0].
Proof.
  apply c2.
  apply c2.
  apply c1.
Qed.

Example r2: R 1 [1;2;1;0].
Proof.
  apply c3.
  apply c2.
  apply c3.
  apply c3.
  apply c2.
  apply c2.
  apply c2.
  apply c1.
Qed.

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~(s =~ EmptySet).
Proof.
  intros T s.
  intros H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss.
  - simpl in *.  apply MStar0.
  - simpl in *. apply MStarApp.
    * apply H. left. reflexivity.
    * apply IHss. intros s H1. apply H. right. apply H1.
Qed.

Theorem list_h: forall T (x : T) (l1 l2 : list T), l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros T x l1 l2 H. rewrite H. reflexivity.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T.
  split.
  - intros H. generalize dependent s1. induction s2.
    * intros s1 H. inversion H. reflexivity.
    * intros s1 H. inversion H. inversion H3. rewrite <- delist.
      apply list_h. apply IHs2. apply H4.
  - intros H. rewrite H. generalize dependent s1. induction s2.
    * intros s1 H. simpl. apply MEmpty.
    * intros s1 H. simpl. rewrite delist. apply MApp.
      ** apply MChar.
      ** apply IHs2 with s2. reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  - intros H. induction H. induction H.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. rewrite andb_true_iff. split. apply IHexp_match1. apply IHexp_match2.
    * simpl. rewrite orb_true_iff. left. apply IHexp_match.
    * simpl. rewrite orb_true_iff. right. apply IHexp_match.
    * simpl. reflexivity.
    * simpl. reflexivity.
  - induction re.
    * intros H. simpl in *. discriminate H.
    * intros H. simpl in *. exists []. apply MEmpty.
    * intros H. exists [t]. apply MChar.
    * simpl in *. intros H. rewrite andb_true_iff in H. destruct H. induction IHre1, IHre2.
      ** apply H0.
      ** exists (x ++ x0). apply MApp. apply H1. apply H2.
      ** apply H0.
      ** apply H.
    * intros H. simpl in *. rewrite orb_true_iff in H. destruct H.
      ** destruct IHre1.
         *** apply H.
         *** exists x. apply MUnionL. apply H0.
      ** destruct IHre2.
         *** apply H.
         *** exists x. apply MUnionR. apply H0.
    * intros H. exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate Heqre'.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. simpl. apply H.
  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.

intros T s r H.
  remember (Star r) as r'.
  induction H as [| | | | |r'|s s' r'' H _ H' IH'];
  try (inversion Heqr' as [Heq]).
  - exists [ ]. split.
    + simpl. reflexivity.
    + intros _ [].
      
  - subst. apply IH' in Heqr'. destruct Heqr' as [x Hx]. clear IH'.
  destruct Hx as [Hfs' Hxr]. subst. clear H'.
  exists (s :: x). split.
    + simpl. trivial.
    + intros s' H''. destruct H''.
      * subst. trivial.
      * apply Hxr. trivial.
Qed.


Module Pumping.
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.


Require Import Coq.omega.Omega.
Require Export Logic.

Lemma sum_le: forall (n1 n2 n3 n4 : nat), n1 + n2 <= n3 + n4 -> n1 <= n3 \/ n2 <= n4.
Proof.
  intros n1 n2 n3 n4 H.
  omega.
Qed.

Lemma sum_le2: forall (n1 n2 n3 : nat), n1 + n2 <= n3 -> n1 <= n3 /\ n2 <= n3.
Proof.    
  intros n1 n2 n3 H. split.
  - omega.
  - omega.
Qed.

Lemma length_le: forall T (s1 s2 : list T), 1 <= length (s1 ++ s2) -> 1 <= length s1 \/ 1 <= length s2.
Proof.
  intros T s1 s2 H.
  rewrite app_length in H.
  omega.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. omega.
  - simpl. omega.
  - simpl. rewrite app_length. intro H.
    apply sum_le in H. destruct H.
    + apply IH1 in H.
      destruct H as [x0 [x1 [x2]]].
      destruct H as [Hs [Hx Happ]]. clear IH1. clear IH2.
      exists x0, x1, (x2 ++ s2). split.
      * rewrite Hs. repeat rewrite <- app_assoc. reflexivity.
      * split.
        ** trivial.
        ** intros m. rewrite app_assoc. rewrite app_assoc. apply MApp.
           *** rewrite <- app_assoc. apply Happ.
           *** apply Hmatch2.
    + apply IH2 in H.
      destruct H as [x0 [x1 [x2]]].
      destruct H as [Hs [Hx Happ]]. clear IH1. clear IH2.
      exists (s1 ++ x0), x1, x2. split.
      * rewrite Hs. repeat rewrite <- app_assoc. trivial.
      * split.
        ** apply Hx.
        ** intros m. repeat rewrite <- app_assoc. apply MApp.
           *** apply Hmatch1.
           *** apply Happ.      
  - simpl. intros H. apply sum_le2 in H. destruct H. apply IH in H. clear IH. clear H0.
    destruct H as [x1 [x2 [x3]]].
    destruct H as [H0 [H1 H2]].
    exists x1, x2, x3. split.
    + apply H0.
    + split.
      * apply H1.
      * intros m. apply MUnionL. apply H2.
  - simpl. intros H. rewrite plus_comm in H. apply sum_le2 in H.
    destruct H. apply IH in H. clear IH. clear H0.
    destruct H as [x1 [x2 [x3]]].
    destruct H as [H0 [H1 H2]].
    exists x1, x2, x3. split.
    + apply H0.
    + split.
      * apply H1.
      * intros m. apply MUnionR.
        apply H2.
  - simpl. omega.
  - simpl in *. intros H. apply length_le in H.
    destruct H.
    * exists [], s1,s2. split.
      ** simpl. trivial.
      ** split.
         *** induction s1.
             **** inversion H.
             **** unfold not. intros HH. inversion HH.
         *** intros m. simpl. apply star_app.
             **** induction m.
                  ***** simpl. apply MStar0.
                  ***** simpl. apply star_app. apply MStar1. apply Hmatch1. apply IHm.
             **** apply Hmatch2.
    * apply IH2 in H.
      destruct H as [x1 [x2 [x3]]].
      destruct H as [H0 [H1 H2]].
      exists (s1 ++ x1), x2, x3.
      split.
      ** rewrite H0. repeat rewrite <- app_assoc. trivial.
      ** split.
        *** apply H1.
        *** intros m. rewrite <- app_assoc.  apply MStarApp.
          **** apply Hmatch1.
          **** apply H2.
Qed.

End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.


Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  split.
  - intros H0. destruct H.
    * reflexivity.
    * unfold not in *. apply H in H0. inversion H0.
  - intros H0. destruct H.
    * apply H.
    * discriminate H0.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l H.
  induction l.
  - simpl. unfold not. intros [].
  - simpl. unfold not. intros H0. destruct H0.
    * rewrite H0 in H. simpl in H. destruct (eqbP n n) in H.
      ** inversion H.
      ** unfold not in H1. apply H1. reflexivity.
    * simpl in *. destruct (eqbP n x) in H.
      ** inversion H.
      ** simpl in *. apply IHl in H. clear IHl. clear H1. unfold not in *. apply H, H0.
Qed.

Inductive nostutter {X:Type} : list X -> Prop :=
| nostutter_empty : nostutter []
| nostutter_cons (hd: X) (tail: list X):
    (hd_error tail) <> (Some hd) -> nostutter tail -> nostutter (hd :: tail).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; simpl; unfold not; intros H; inversion H.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  constructor.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  constructor. simpl. unfold not. intros H. inversion H.
  constructor.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.

  contradiction H1. trivial.
Qed.

Definition tl {T} (l: list T) : list T :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Inductive merge {T : Type} : (list T) -> (list T) -> (list T) -> Prop :=
| merge_empty_empty : merge [] [] []                            
| merge_l (l1 l2 l : list T) :
    l1 <> [] -> hd_error l1 = hd_error l -> merge (tl l1) l2 (tl l) -> merge l1 l2 l
| merge_r (l1 l2 l : list T) :                                                                
    l2 <> [] -> hd_error l2 = hd_error l -> merge l1 (tl l2) (tl l) -> merge l1 l2 l.

Example merge_example: merge [1;6;3] [4;2] [1;4;6;2;3].
Proof.
  simpl. constructor. unfold not. intros H. inversion H. simpl. trivial.
  simpl. constructor 3. unfold not. intros H. inversion H. simpl. trivial.
  simpl. constructor. unfold not. intros H. inversion H. simpl. trivial.
  simpl. constructor 3. unfold not. intros H. inversion H. simpl. trivial.
  simpl. constructor. unfold not. intros H. inversion H. simpl. trivial.
  simpl. constructor.
Qed.

Theorem hd_error_empty: forall X (l : list X), hd_error l = None -> l = [].
Proof.
  intros X l H.
  induction l.
  - trivial.
  - simpl in *. inversion H.
Qed.

Theorem forallb_tail: forall X (l : list X) (test : X -> bool),
    forallb test l = true -> forallb test (tl l) = true.
Proof.
  intros X l test H.
  induction l.
  -  simpl. trivial.
  - simpl in *. destruct (test x).
    * apply H.
    * inversion H.
Qed.

Theorem forallb_false : forall X (l : list X) (test : X -> bool),
    forallb test l = true -> (forall x, hd_error l = Some x -> test x = true).
Proof.
  intros X  l test H0.
  induction l.
  - intros x H. simpl in *. inversion H.
  - simpl in *. intros x0. destruct (test x) eqn:TT.
    * intros H. injection H as H. subst. apply TT.
    * discriminate H0.
Qed.
    

Theorem existsb_true : forall X (l : list X) (test : X -> bool),
     existsb test l = false -> (forall x, hd_error l = Some x -> test x = false).
Proof.
  intros X l test H0.
  induction l.
  - intros x H. simpl in *. inversion H.
  - simpl in *. intros x0. destruct (test x) eqn:TT.
    *  discriminate H0.
    * intros H. injection H as H. subst. apply TT.
Qed.


Theorem existsb_tail: forall X (l : list X) (test : X -> bool),
    existsb test l = false -> existsb test (tl l) = false.
Proof.
  intros X l test H.
  induction l.
  - simpl. trivial.
  - simpl in *. destruct (test x).
    * inversion H.
    * apply H.
Qed.

Theorem list_decom: forall X (x: X) (t l: list X),
    hd_error l = Some x /\ tl l = t -> x :: t = l.
Proof.
  intros X x t l H.
  destruct H.
  rewrite <- H0.
  induction l.
  - simpl in *. discriminate H.
  -  simpl in *. subst. injection H as HH. rewrite HH. trivial.
Qed.

Theorem empty_merge: forall X (l : list X),
    merge l [] [] -> l = [].
Proof.
  intros X l H.
  inversion H.
  - trivial.
  - subst. simpl in *. apply hd_error_empty in H1. apply H1.
  - subst. unfold not in *. simpl in *. destruct H0. trivial.
Qed.

Theorem fiter_filter : forall X (l l1 l2: list X) (test : X -> bool),
    merge l1 l2 l ->
    forallb test l1 = true ->
    existsb test l2 = false ->
    filter test l = l1.
Proof.
  intros X.
  induction l.
  - intros l1 l2 test Hm Hl1 Hl2. simpl. inversion Hm.
    * trivial.
    * simpl in H. apply hd_error_empty in H0. subst. trivial.
    * simpl in *. subst. apply hd_error_empty in H0. subst. simpl in *.
      clear Hl2 Hl1. apply empty_merge in Hm. symmetry. trivial.
  - simpl in *. intros l1 l2 test Hm Hl1 Hl2. inversion Hm.
    * clear Hm. subst. simpl in *. apply IHl with (tl l1) l2 test in H1.
      ** destruct test eqn:TT.
         *** clear IHl. apply list_decom. split.
             **** trivial.
             **** symmetry. trivial.
         *** apply forallb_false with X l1 test x in Hl1. subst.
             rewrite Hl1 in TT. inversion TT. apply H0.
      ** apply forallb_tail. apply Hl1.
      ** apply Hl2.
    * subst. simpl in *. apply IHl with l1 (tl l2) test in H1.
      ** destruct (test x) eqn:TT.
         *** apply existsb_true with X l2 test x in Hl2. subst.
             rewrite Hl2 in TT. inversion TT. apply H0.
         *** apply H1.
      ** apply Hl1.
      ** apply existsb_tail. apply Hl2.
Qed.

Require Import Coq.omega.Omega.
Require Export Logic.



Inductive subseq: list nat -> list nat -> Prop :=
  subseq_nil : forall l, subseq [] l
| subseq_inboth : forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2)
| subseq_in2nd  : forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l.
  induction l.
  - apply subseq_nil.
  - apply subseq_inboth. apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  induction H.
  - apply subseq_nil.
  - apply subseq_inboth. apply IHsubseq.
  - apply subseq_in2nd. apply IHsubseq.
Qed.
  
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent H1.
  generalize dependent l1.
  induction H2.
  - intros l1 H1. inversion H1. apply subseq_nil.
  - intros l0 H1. inversion H1.
    * apply subseq_nil.
    * apply subseq_inboth. apply IHsubseq. apply H3.
    * apply subseq_in2nd. rewrite <- H0. apply IHsubseq. rewrite <- H0 in H3. apply H3.
  - intros l0 H1. apply subseq_in2nd. apply IHsubseq. apply H1.
Qed.


Lemma subseq_l_xl: forall x l1 l2, subseq l1 (x :: l2) -> subseq l1 l2 \/ hd_error l1 = Some x.
Proof.
  intros x l1 l2 H.
  inversion H.
  - subst. simpl in *. left. constructor.
  - subst. right. simpl. trivial.
  - subst. left. apply H2.
Qed.

Lemma subseq_xl_l: forall x l1 l2, subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros x l1 l2 H.
  apply subseq_trans with (x::l1).
  - constructor. apply subseq_refl.
  - apply H.
Qed.
  
Lemma subseq_xl_xl: forall x1 x2 l1 l2, subseq (x1 :: l1) (x2 :: l2) -> subseq l1 l2.
Proof.
  intros x1 x2 l1 l2 H.
  apply subseq_l_xl in H as H0.
  destruct H0.
  - apply subseq_trans with (x1 :: l1).
    * constructor. apply subseq_refl.
    * apply H0.
  - simpl in *. injection H0 as H1. subst. inversion H.
    * subst. apply H1.
    * subst. apply subseq_xl_l in H2. apply H2.
Qed.

Theorem fiter_filter' : forall (l l': list nat) (test : nat -> bool),
    subseq l' l ->
    forallb test l' = true ->
    length (filter test l) >= length (filter test l').
Proof.
  induction l.
  - intros l' test H0 H1. simpl. inversion H0. subst. simpl. omega.
  - intros l' test H0 H1. simpl in *. destruct (test x) eqn:TT.
    * simpl in *. induction l'.
      ** simpl. omega.
      ** simpl in *.  destruct (test x0) eqn:TTT.
         *** simpl. assert (H: forall n m, n >= m -> S n >= S m).
             **** intros n m H. omega.
             **** apply H. apply IHl.
                  ***** apply subseq_xl_xl in H0. apply H0.
                  ***** apply H1.
         *** discriminate H1.
    * apply IHl.
      ** clear IHl.
         apply subseq_l_xl in H0. destruct H0.
         *** apply H.
         *** assert (Herror: hd_error l' = Some x -> exists t, l' = x :: t).
             **** intros HH. exists (tl l'). induction l'.
                  ***** simpl in *. discriminate HH.
                  ***** simpl in *. injection HH as HH. rewrite HH. reflexivity.
             **** apply Herror in H. destruct H as [t H]. subst. clear Herror.
             simpl in H1. rewrite TT in H1. discriminate H1.
      ** apply H1.
Qed.




Inductive pal: list nat -> Prop :=
| empty_pal : pal []
| single_pal : forall (x : nat), pal [x]
| pal_extend: forall (l1 l2 : list nat), l1 = rev l1 -> pal (l2 ++ l1 ++ (rev l2)).                                           

Theorem pal_app_rev:
  forall l, pal (l ++ rev l).
Proof. intros l. apply (pal_extend [] l). simpl. trivial. Qed.

Theorem pal_rev:
  forall l, pal l -> l = rev l.
Proof.
  intros l H.
  induction H.
  - constructor.
  - constructor.
  - rewrite rev_app_distr. rewrite rev_app_distr. rewrite rev_involutive.
    rewrite <- app_assoc. rewrite H. rewrite rev_involutive. rewrite <- H. trivial.
Qed.

Theorem tail_eq2: forall l1 l2 : list nat, l1 = l2 -> tl l1 = tl l2.
Proof.
  intros l1 l2 H. rewrite H. trivial.
Qed.

Theorem rev_pal:
  forall l, l = rev l -> pal l.
Proof.
  intros l H.
  destruct l.
  - constructor.
  - simpl in H. rewrite delist in *.
    apply tail_eq2 in H as H1. simpl in H1.
    destruct (rev l) eqn: HHH.
    * simpl in *. rewrite H1. constructor.
    * simpl in H1.
      subst.
      rewrite rev_app_distr in HHH. simpl in HHH.
      rewrite delist in HHH. injection HHH as H1.
      constructor.
      symmetry.
      apply H0.
Qed.
    
Definition disjoint (l1 l2 : list nat) : Prop :=
  forall x, In x l1 -> not (In x l2).

Inductive NoDup: list nat -> Prop :=
| nodup_empty : NoDup []
| nodup_single : forall (x : nat), NoDup [x]
| nodup_app : forall (l1: list nat) (l2 : list nat),
    NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).

Theorem nodup_1:
  forall l1 l2 l3, NoDup l1 -> NoDup l2 -> NoDup l3 ->
              disjoint l1 l2 -> disjoint l2 l3 -> disjoint l1 l3 -> NoDup (l1 ++ l2 ++ l3).
Proof.
  intros l1 l2 l3 H1 H2 H3 HH1 HH2 HH3.
  constructor.
  - apply H1.
  - constructor.
    * apply H2.
    * apply H3.
    * apply HH2.
  - unfold disjoint in *.
    intros x.
    intros HHH.
    unfold not in *.
    intros HHH1.
    apply In_app_iff in HHH1.
    destruct HHH1.
    * apply HH1 with x.
      ** apply HHH.
      ** apply H.
    * apply HH3 with x.
      ** apply HHH.
      ** apply H.
Qed.

Theorem nodup_2: forall l1 l2, NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l2 ++ l1).
Proof.
  intros l1 l2 H1 H2 H3.
  constructor.
  - apply H2.
  - apply H1.
  - unfold disjoint in *.
    unfold not in *.
    intros x HH1 HH2.
    apply H3 with x.
    * apply HH2.
    * apply HH1.
Qed.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H.
  induction l.
  - simpl. inversion H.
  - rewrite delist in H. rewrite In_app_iff in H. simpl in H.
    destruct H.
    * destruct H.
      ** subst. exists [], l. simpl. trivial.
      ** inversion H.
    * destruct IHl.
      ** apply H.
      ** destruct H0. exists (x0 :: x1), x2.
         simpl. rewrite H0. trivial.
Qed.

Require Import Coq.Arith.Lt.

Inductive repeats {X:Type} : list X -> Prop :=
| one_repeat : forall x, repeats [x; x]
| with_repeat_left : forall l1 l2, repeats l1 -> repeats (l1 ++ l2)
| with_repeat_right : forall l1 l2, repeats l1 -> repeats (l2 ++ l1)
| repeats_el: forall x l, In x l -> repeats (x :: l).


Theorem exclude_In: forall X (x1 x2 : X) (l1 l2 : list X),
    In x1 (l1 ++ x2 :: l2) -> x1 <> x2 -> In x1 (l1 ++ l2).
Proof.
  intros X x1 x2 l1 l2 H1 H2.
  apply In_app_iff.
  apply In_app_iff in H1. rewrite delist in H1.
  destruct H1.
  - left. apply H.
  - apply In_app_iff in H. destruct H.
    * exfalso. unfold not in *. apply H2. simpl in H. destruct H.
      ** symmetry. apply H.
      ** inversion H.
    * right. apply H.
Qed.

Theorem exclude_length: forall X (x : X) (l1 l2 : list X),
    length (l1 ++ x :: l2) = S (length (l1 ++ l2)).
Proof.
  intros X x l1 l2.
  rewrite app_length. rewrite delist.
  rewrite app_length. rewrite app_length.
  simpl. rewrite <- plus_1_l.
  rewrite <- (plus_1_l (length l1 + length l2)).
  repeat rewrite plus_assoc. rewrite (plus_comm 1 (length l1)).
  trivial.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
  intros X l1. induction l1 as [|x l1' IHl1'].
  - intros l2 Hem H Hlength. simpl in *. inversion Hlength.
  - intros l2 Hem H Hlength. simpl in *.
    destruct (Hem (In x l1')).
    * apply repeats_el. apply H0.
    * unfold not in *. rewrite delist. constructor 3.
      destruct (Hem (In x l2)).
      ** apply in_split in H1.
         inversion H1. inversion H2.
         apply IHl1' with (x0 ++ x1).
         *** apply Hem.
         *** intros x2 HH. subst.
             destruct (Hem (x2 = x)).
             **** subst. contradiction.
             **** clear IHl1' H1 H2 Hem. apply exclude_In with x.
                  ***** apply H. right. apply HH.
                  ***** apply H3.
         *** subst. clear H H0 H1. rewrite exclude_length in Hlength.
             apply lt_S_n. apply Hlength.
      ** unfold not in *. exfalso. apply H1. apply H. left. trivial.
Qed.

Require Export Coq.Strings.Ascii.
Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. subst. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
   assert (app_nil: forall X (s : list X), [] ++ s = s). intros. simpl. trivial.
  split.
  - intros. inversion H. subst. 
    destruct s1.
    * simpl in *. left. split. apply H3. apply H4.
    * simpl in *. injection H1 as H11 H22. subst. right.
      exists s1, s2. split.
      ** reflexivity.
      ** split. apply H3. apply H4.  
  -  intros. destruct H.
     * destruct H.
       rewrite <- app_nil with ascii (a::s).
       apply MApp. apply H. apply H0.
     * destruct H as [s0 [s1]]. destruct H. destruct H0.
       rewrite H. rewrite delist. rewrite app_assoc. apply MApp.
       ** simpl. apply H0.
       ** simpl. apply H1.
Qed.

Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H. subst.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split.
  - intros H.
    remember (a :: s) as s'.
    remember (Star re) as star'.
    induction H.
    * discriminate.
    * discriminate.
    * discriminate.
    * discriminate.
    * discriminate.
    * discriminate.
    * injection Heqstar' as HH. subst.
      destruct s1.
      ** simpl in *. apply IHexp_match2. apply Heqs'. reflexivity.
      ** clear IHexp_match2. clear IHexp_match1.
         simpl in Heqs'.
         inversion Heqs'. subst. clear Heqs'.
         exists s1, s2. split.
         *** trivial.
         *** split. apply H. apply H0.
  - intros H. destruct H as [s0 [s1]]. destruct H. destruct H0. subst.
    apply (MStarApp (a :: s0) s1). apply H0. apply H1.
Qed.

Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

Fixpoint match_eps (re: @reg_exp ascii) : bool :=
  match re with
  | EmptyStr => true
  | App re1 re2 => andb (match_eps re1) (match_eps re2)
  | Star _ => true
  | Union re1 re2 => orb (match_eps re1) (match_eps re2)
  | _ => false
  end.


Theorem empty_app : forall X (l1 l2 : list X), l1 ++ l2 = [] <-> l1 = [] /\ l2 = [].
Proof.
  intros X l1 l2.
  split.
  - intros H. split.
    * destruct l1.
      ** reflexivity.
      ** inversion H.
    * destruct l2.
      ** reflexivity.
      ** destruct l1.
         *** simpl in H. inversion H.
         *** simpl in H. inversion H.
  - intros H. destruct H. subst. simpl. reflexivity.
Qed.

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros.
  apply iff_reflect.
  split.
  - induction re.
    * intros. inversion H.
    * intros. simpl. trivial.
    * intros. inversion H.
    * intros. inversion H. subst. apply empty_app in H1.
      destruct H1. subst. apply IHre1 in H3. apply IHre2 in H4.
      simpl. apply andb_true_iff. split. apply H3. apply H4.
    * intros. inversion H.
      ** subst. apply IHre1 in H2. simpl.
         apply orb_true_iff. left. apply H2.
      ** subst. apply IHre2 in H1. simpl.
         apply orb_true_iff. right. apply H1.
    * intros. simpl. trivial.
  - induction re.
    * simpl. intros. inversion H.
    * simpl. intros. apply MEmpty.
    * simpl. intros. inversion H.
    * simpl. intros. apply andb_true_iff in H. destruct H.
      rewrite <- (app_nil_r _ []). apply MApp.
      ** apply IHre1 in H. apply H.
      ** apply IHre2 in H0. apply H0.
    * simpl. intros. apply orb_true_iff in H. destruct H.
      ** apply MUnionL. apply IHre1 in H. apply H.
      ** apply MUnionR. apply IHre2 in H. apply H.
    * simpl. intros. apply MStar0.
Qed.

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char a' => if (ascii_dec a a') then EmptyStr else EmptySet
  | App re1 re2 => if (match_eps re1)
                  then Union (App (derive a re1) re2) (derive a re2)
                  else App (derive a re1) re2
  | Union re1 re2 => Union (derive a re1) (derive a re2)
  | Star re => App (derive a re) (Star re)
  end.

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. simpl. trivial. Qed.

Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. simpl. trivial. Qed.

Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. simpl. trivial. Qed.

Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. simpl. trivial. Qed.

Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. simpl. trivial. Qed.

Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. simpl. trivial. Qed.

Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. simpl. trivial. Qed.

Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. simpl. trivial. Qed.

Theorem app_nil_l : forall X (l : list X), l = [] ++ l.
Proof. simpl. trivial. Qed.

Lemma derive_corr : derives derive.
Proof.
  split.
  - intros H.
    generalize dependent s.
    induction re; intros s H.
    * inversion H.
    * inversion H.
    * inversion H. subst.
      simpl. destruct (ascii_dec t t).
      apply MEmpty. unfold not in *. exfalso. apply n. trivial.
    *  simpl in *. inversion H. subst.
       apply app_ne in H. 
       destruct (match_eps_refl re1).
       ** destruct s1.
          *** simpl in *. subst. apply MUnionR. apply IHre2. apply H4.
          *** simpl in *. apply MUnionL. inversion H1. subst.
              apply MApp.
              **** clear H1. apply IHre1. apply H3.
              **** apply H4.
       ** unfold not in *. destruct s1.
          *** exfalso. apply H0, H3.
          *** simpl in *. inversion H1. subst. clear H1 H0.
              apply MApp.
              **** apply IHre1, H3.
              **** apply H4.
    * simpl in *. inversion H.
      ** subst. apply MUnionL. apply IHre1. apply H2.
      ** subst. apply MUnionR. apply IHre2. apply H1.
    * simpl. apply star_ne in H.
      destruct H as [s0 [s1]]. destruct H. destruct H0.
      subst. apply MApp.
      ** apply IHre, H0.
      ** apply H1.
  - intros H.
    generalize dependent s.
    induction re; intros s H.
    * inversion H.
    * inversion H.
    * simpl in *. destruct (ascii_dec a t).
      ** inversion H. subst. apply MChar.
      ** inversion H.
    * simpl in *. destruct (match_eps_refl re1).
      ** inversion H. subst.
         *** inversion H3. subst. rewrite delist. rewrite app_assoc. apply MApp.
             **** simpl in *. apply IHre1, H5.
             **** apply H6.
         *** subst. rewrite app_nil_l with ascii (a :: s).
             apply MApp.
             **** apply H0.
             **** apply IHre2, H3.
      ** inversion H. subst. rewrite delist. rewrite app_assoc. apply MApp.
         *** simpl. apply IHre1. apply H4.
         *** apply H5.
    * simpl in *. inversion H; subst.
      ** apply MUnionL, IHre1, H2.
      ** apply MUnionR, IHre2, H1.
    * simpl in *. inversion H. subst. rewrite delist. rewrite app_assoc. apply MStarApp.
      ** simpl. apply IHre. apply H3.
      ** apply H4.
Qed.

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | h :: t => regex_match t (derive h re)
  end.

Theorem regex_refl : matches_regex regex_match.
Proof.
  unfold matches_regex.
  intros s.
  induction s as [| h t IH]; simpl; intros.
  - apply (match_eps_refl re).
  - destruct  (IH (derive h re)) as [refl_t | refl_f].
    * apply ReflectT. apply derive_corr in refl_t. apply refl_t.
    * apply ReflectF. unfold not in *. intros H. apply derive_corr in H.
      apply refl_f in H. apply H.
Qed.
