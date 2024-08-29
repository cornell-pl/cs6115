Definition or (P Q : Prop) : Prop := (* FIXME *) True.

Lemma or_intro_left P Q : P -> or P Q.
Proof.
Admitted.

Lemma or_intro_right P Q : Q -> or P Q.
Proof.
Admitted.

Lemma or_elim P Q (R : Prop) : or P Q -> (P -> R) -> (Q -> R) -> R.
Proof.
Admitted

Lemma or_correct P Q : or P Q <-> P \/ Q.
Proof.
Admitted.

