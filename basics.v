Inductive day : Type :=
    | monday : day
    | tuesday : day
    | wednesday : day
    | thursday : day
    | friday : day
    | saturday : day
    | sunday : day.

Definition next_weekday (d: day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => monday
    | sunday => monday
    end.

Inductive bool : Type :=
    | true : bool
    | false : bool.

Definition negb (b: bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1: bool) (b2: bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1: bool) (b2: bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Infix "&&" := andb.
Infix "||" := orb.

Definition nandb (b1: bool) (b2: bool) : bool :=
    negb (b1 && b2).

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
    b1 && b2 && b3.

Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Fixpoint evenb (n: nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Definition oddb (n: nat) : bool :=
    negb (evenb n).

Module NatPlayground.

Fixpoint plus (n: nat) (m: nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Fixpoint minus (n m: nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

Fixpoint mult (n m: nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

End NatPlayground.

Fixpoint exp (base power: nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

Fixpoint factorial (n: nat) : nat :=
    match n with
    | O => S O
    | S n' => mult n (factorial n')
    end.

Fixpoint beq_nat (n m: nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
              end
    end.

Fixpoint leb (n m: nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => leb n' m'
        end
    end.

Theorem plus_0_n : forall n: nat, 0 + n = n.
Proof.
    intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n: nat, 1 + n = S n.
Proof.
    intros n. simpl. reflexivity. Qed.

Theorem mult_0_l: forall n: nat, 0 * n = 0.
Proof.
    intros n. simpl. reflexivity. Qed.

Theorem plus1_neq_0: forall n: nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive: forall b: bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
  Qed.

Theorem andb_commutative: forall b c, andb b c = andb c b.
  Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
  Qed.

Theorem andb_true_elim2: forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  (* If c is true, we don't care about the
     hypothesis. The statement is true. *)
  - reflexivity.
  (* If c is false, we need to make sure that
     the hypothesis evaluates to false.
     [since true -> false would break the proof.]
  *)
  - rewrite <- H.
    destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem zero_nbeq_plus_1: forall n: nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity.
  Qed.



