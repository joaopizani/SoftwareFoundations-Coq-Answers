Require Coq.Unicode.Utf8.

Inductive Day : Type :=
| Monday    : Day
| Tuesday   : Day
| Wednesday : Day
| Thursday  : Day
| Friday    : Day
| Saturday  : Day
| Sunday    : Day.

Definition nextWeekday (d : Day) : Day :=
  match d with
    | Monday => Tuesday
    | Tuesday => Wednesday
    | Wednesday => Thursday
    | Thursday => Friday
    | Friday => Saturday
    | Saturday => Sunday
    | Sunday => Monday
  end.

Eval simpl in (nextWeekday (nextWeekday Friday)).


Example testNextNextSunday : nextWeekday (nextWeekday Sunday) = Tuesday.
Proof. simpl. reflexivity. Qed.


Inductive Bool : Type :=
| False : Bool
| True  : Bool.

Definition negb (b : Bool) : Bool :=
  match b with
    | False => True
    | True  => False
  end.

Definition andb (b₁ b₂ : Bool) : Bool :=
  match b₁ with
    | False => False
    | True  => b₂
  end.

Definition orb (b₁ b₂ : Bool) : Bool :=
  match b₁ with
    | False => b₂
    | True  => True
  end.


Definition admit {T : Type} : T. Admitted.


Definition nandb (b₁ b₂ : Bool) : Bool := negb (andb b₁ b₂).

Example test_nandb_1 : nandb False False = True.
Proof. simpl. reflexivity. Qed.

Example test_nandb_2 : nandb False True  = True.
Proof. simpl. reflexivity. Qed.

Example test_nandb_3 : nandb True  False = True.
Proof. simpl. reflexivity. Qed.

Example test_nandb_4 : nandb True  True  = False.
Proof. simpl. reflexivity. Qed.


Definition andb3 (b₁ b₂ b₃ : Bool) : Bool := andb b₁ (andb b₂ b₃).

Example test_andb3_1 : andb3 True  True  True  = True.
Proof. simpl. reflexivity. Qed.

Example test_andb3_2 : andb3 False True  True  = False.
Proof. simpl. reflexivity. Qed.

Example test_andb3_3 : andb3 True  False True  = False.
Proof. simpl. reflexivity. Qed.

Example test_andb3_4 : andb3 True  True  False = False.
Proof. simpl. reflexivity. Qed. 


Check negb True.


Module PlaygroundNat.

  Inductive ℕ : Type :=
  | O : ℕ
  | S : ℕ -> ℕ.

  Definition pred (n : ℕ) : ℕ :=
    match n with
      | O => O
      | S n' => n'
    end.

End PlaygroundNat.


Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Eval simpl in minustwo 4.

Check minustwo.


Fixpoint evenb (n : nat) : Bool :=
  match n with
    | O => True
    | S O => False
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : Bool := negb (evenb n).

Example test_oddb_1 : oddb 1 = True.
Proof. simpl. reflexivity. Qed.

Example test_oddb_2 : oddb 4 = False.
Proof. simpl. reflexivity. Qed.


Module PlaygroundPlus.

  Fixpoint plus (n m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.