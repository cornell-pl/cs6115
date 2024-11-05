From Coq Require Import Bool String List Extraction Lia.
Open Scope string_scope.
Import ListNotations.

Module ilist.
  Section ilist.
    Context {A : Set}.

    Inductive ilist : nat -> Set :=
    | Nil : ilist O
    | Cons : forall {n}, A -> ilist n -> ilist (S n).

  End ilist.

  Arguments ilist A n : clear implicits.

End ilist.


Module MoreIlist.
  Import ilist.

  Fail Definition firstElements
       {n A B}
       (ls1 : ilist A n)
       (ls2 : ilist B n) : option (A * B) :=
    match ls1 with
    | Cons v1 _ =>
        Some (v1,
               match ls2 in ilist _ N
                     return match N with
                            | O => unit
                            | S _ => B end with
               | Cons v2 _ => v2
               | Nil => tt
               end)
    | Nil => None
    end.

  Fail Fixpoint zip
       {n A B} (ls1 : ilist A n) (ls2 : ilist B n)
       {struct ls1} : ilist (A * B) n :=
    match ls1 in ilist _ N return ilist B N -> ilist (A * B) N with
    | Cons v1 ls1' =>
        fun ls2 =>
          match ls2 in ilist _ N return
                match N with
                | O => unit
                | S N' => ilist A N' -> ilist (A * B) N
                end with
          | Cons v2 ls2' =>
              fun ls1' => Cons (v1, v2) (zip ls1' ls2')
          | Nll => tt
          end ls1'
    | Nil => fun _ => Nil
    end ls2.
  
End MoreIlist.

Module fixlist.
  Section fixlist.
    Context {A : Type}.

    Fixpoint fixlist n: Type :=
      match n with
      | 0 => unit
      | S n => A * fixlist n
      end.

    Definition hd {n} (v: fixlist (S n)) :=
      fst v.

    Fixpoint app {n0} (v0: fixlist n0) {n1} (v1: fixlist n1):
      fixlist (n0 + n1) :=
      match n0 return fixlist n0 -> fixlist (n0 + n1) with
      | 0 => fun _ => v1
      | S n => fun v0 => (fst v0, app (snd v0) v1)
      end v0.

    Fixpoint inject (ls : list A): fixlist (length ls) :=
      match ls return fixlist (length ls) with
      | [] => tt
      | hd :: tl => (hd, inject tl)
      end.

    Fixpoint unject {n} (v : fixlist n): list A :=
      match n return fixlist n -> list A with
      | 0 => fun _ => []
      | S n => fun v => fst v :: unject (snd v)
      end v.

    Theorem inject_unject_identity : forall l, unject (inject l) = l.
    Proof.
      induction l; simpl; congruence.
    Qed.

  End fixlist.

  Arguments fixlist A n : clear implicits.

(*|
Without peeking, try to define the functions `zip`, `map`, and `map2`.
|*)

  Fail Fixpoint zip {A B n} (va: fixlist A n) (vb: fixlist B n)
    : fixlist (A * B) n := tt.

  Fail Fixpoint map {A B n} (f: A -> B) := tt.

  Fail Fixpoint map2 {A B C n} (f: A -> B -> C) := tt.

End fixlist.


Import fixlist.

Fixpoint fixnat (n: nat): Set :=
  match n with
  | 0 => False
  | S n => option (fixnat n)
  end.

Fail Fixpoint fixlist_nth {A n}
  (fl: fixlist A n) (idx: fixnat n) {struct n}: A := tt.

Fail Fixpoint fixnat_to_nat {n} := tt.


