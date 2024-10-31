From Coq Require Import String Arith List Lia Nat Bool Peano_dec.
Import ListNotations.

Definition propvar := nat.

Inductive formula : Set :=
| Atomic : propvar -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula.

Definition asgn := nat -> Prop.

Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => atomics v
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
  end.

Require Import ListSet.

Section my_tauto.
  Variable atomics : asgn.

  Definition add (s : set propvar) (v : propvar) :=
    set_add eq_nat_dec v s.

  Fixpoint allTrue (s : set propvar) : Prop :=
    match s with
    | nil => True
    | v :: s' => atomics v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> atomics v
    -> allTrue (add s v).
  Proof.
    induction s; simpl; intuition;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; simpl; intuition.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> atomics v.
  Proof.
    induction s; simpl; intros; intuition congruence.
  Qed.
End my_tauto.

Ltac position x ls :=
  match ls with
  | [] => constr:(@None nat)
  | x :: _ => constr:(Some 0)
  | _ :: ?ls' =>
    let p := position x ls' in
    match p with
    | None => p
    | Some ?n => constr:(Some (S n))
    end
  end.

Ltac vars_in P acc :=
  let t := type of P in
  match type of P with
    Prop =>
      match P with
      | True => acc
      | False => acc
      | ?Q1 /\ ?Q2 =>
          let acc' := vars_in Q1 acc in
          vars_in Q2 acc'
      | ?Q1 \/ ?Q2 =>
          let acc' := vars_in Q1 acc in
          vars_in Q2 acc'
      | _ =>
          let pos := position P acc in
          match pos with
          | Some _ => acc
          | None => constr:(P :: acc)
          end
      end
  end.
