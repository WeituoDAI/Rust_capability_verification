From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_u32astraits_foo_Fooi32_bar.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u32astraits_foo_Fooi32_bar_proof (π : thread_id) :
  u32astraits_foo_Fooi32_bar_lemma π.
Proof.
  u32astraits_foo_Fooi32_bar_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
