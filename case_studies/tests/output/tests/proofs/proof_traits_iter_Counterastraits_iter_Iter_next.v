From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_traits_iter_Counterastraits_iter_Iter_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iter_Counterastraits_iter_Iter_next_proof (π : thread_id) :
  traits_iter_Counterastraits_iter_Iter_next_lemma π.
Proof.
  traits_iter_Counterastraits_iter_Iter_next_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
