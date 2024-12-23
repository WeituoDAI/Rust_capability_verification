From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_structs_EvenInt_add_even.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma structs_EvenInt_add_even_proof (π : thread_id) :
  structs_EvenInt_add_even_lemma π.
Proof.
  structs_EvenInt_add_even_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { apply Zeven_plus_Zeven; solve_goal. all: shelve. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
