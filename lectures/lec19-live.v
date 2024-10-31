From Coq Require Import Bool String List Extraction Lia.
Open Scope string_scope.
Import ListNotations.

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall {t}, exp Bool -> exp t -> exp t -> exp t

| Pair : forall {t1 t2}, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall {t1 t2}, exp (Prod t1 t2) -> exp t1
| Snd : forall {t1 t2}, exp (Prod t1 t2) -> exp t2.

(*|
Here is a standard "tagged" interpreter
|*)

Inductive val : Type :=
  VNat : nat -> val
| VBool : bool -> val
| VPair : val -> val -> val.

Fixpoint tagDenote {t} (e:exp t) : option val :=
  match e with
  | NConst n =>
    Some (VNat n)
  | Plus e1 e2 =>
    match tagDenote e1, tagDenote e2 with
    | Some (VNat n1), Some (VNat n2) =>
                      Some (VNat (n1 + n2))
    | _,_ => None
    end
  | Eq e1 e2 => 
      match tagDenote e1, tagDenote e2 with
      | Some (VNat n1), Some (VNat n2) =>
                        Some (VBool (if PeanoNat.Nat.eq_dec n1 n2 then true else false))
      | _,_ => None
      end
  | BConst b => Some (VBool b)
  | And e1 e2 =>
    match tagDenote e1, tagDenote e2 with
    | Some (VBool b1), Some (VBool b2) =>
                       Some (VBool (andb b1 b2))
    | _,_ => None
    end
  | If e1 e2 e3 =>
    match tagDenote e1 with
    | Some (VBool b) =>
      if b then tagDenote e2 else tagDenote e3
    | _ => None
    end
  | Pair e1 e2 =>
      match tagDenote e1, tagDenote e2 with
      | Some v1, Some v2 =>
          Some (VPair v1 v2)
      | _,_ => None
      end 
  | Fst e =>
      match tagDenote e with
      | Some (VPair v1 v2) => Some v1
      | _ => None
      end
  | Snd e =>
      match tagDenote e with
      | Some (VPair v1 v2) => Some v2
      | _ => None
      end
  end.

(*|
Your task: can you write a "tagless" interpreter?
|*)
