(* The Universe contains 'Things.', for example: "I", "London", etc. *)
Parameter U: Set.

(* existence is affirmed or denied, is regarded as the Predicate *)
Definition Predicate := U -> Prop.

(*
A 'Proposition', when in normal form, asserts, as to certain two Classes, which are called its 'Subject' and 'Predicate', either

that some Members of its Subject are Members of its Predicate;

or that no Members of its Subject are Members of its Predicate;

or that all Members of its Subject are Members of its Predicate.

*)

(* All Members of its Subject are Members of its Predicate; Proposition in A *)
Notation "'All' subject 'are' predicate" := (forall x:U, subject(x) -> predicate(x)) (at level 50).
Notation "'All' subject 'is' predicate" := (forall x:U, subject(x) -> predicate(x)) (at level 50).

(* No Members of its Subject are Members of its Predicate; Proposition in E *)
Notation "'No' subject 'are' predicate" := (forall x:U, subject(x) -> ~predicate(x)) (at level 50).
Notation "'No' subject 'is' predicate" := (forall x:U, subject(x) -> ~predicate(x)) (at level 50).

(* Some Members of its Subject are Members of its Predicate; Proposition in I *)
Notation "'Some' subject 'are' predicate" := (exists x:U, subject(x) /\ predicate(x)) (at level 50).
Notation "'Some' subject 'are' 'not' predicate" := (exists x:U, subject(x) /\ ~predicate(x)) (at level 50).



Axiom contraposition: forall subject predicate: Predicate, (No subject are predicate) -> (No predicate are subject).
Axiom doubleneg: forall p: Prop, ~~p->p.


Parameter selfish popular helpful: Predicate.
Axiom A1: No selfish is popular.
Axiom A2: All helpful is popular.
Theorem T1: No selfish is helpful.
  intros.
  apply A1 in H.
  contradict H.
  apply A2.
  assumption.
Qed.


Parameter soldiers valiant brave: Predicate.
Axiom A3: All soldiers are valiant.
Axiom A4: Some soldiers are brave.
Theorem T2: Some valiant are brave.
Proof.
  destruct A4.
  destruct H.
  apply A3 in H.
  exists x.
  split.
  assumption.
  assumption.
Qed.


Parameter my_uncles generous gourmet: Predicate.
Axiom A5: No gourmet is generous.
Axiom A6: All my_uncles are generous.
Theorem T3: No my_uncles are gourmet.
  intros.
  apply A6 in H.
  contradict H.
  apply A5.
  assumption.
Qed.


Parameter cats understanding_French chickens: Predicate.
Axiom A7: All cats are understanding_French.
Axiom A8: Some chickens are cats.
Theorem T4: Some chickens are understanding_French.
destruct A8.
destruct H as [a b].
apply A7 in b.
exists x.
tauto.
Qed.

(*
'To begin with,' said the Cat, 'a dog's not mad. You grant that?'
'I suppose so,' said Alice.
'Well, then,' the Cat went on,*
'you see, a dog growls when it's angry, and wags its tail when it's pleased. 
Now I growl when I'm pleased, and wag my tail when I'm angry.
Therefore I'm mad.'
*)
Parameter mad cat dogs angry: Predicate.
Axiom A9: No dogs are mad.
(* TODO finish Alice speaks to Cheshire Cat *)