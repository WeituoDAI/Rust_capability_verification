From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.paper_examples.generated Require Import generated_code_paper_examples generated_specs_paper_examples generated_template_mut_ref_add_42.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma mut_ref_add_42_proof (π : thread_id) :
  mut_ref_add_42_lemma π.
Proof.
  mut_ref_add_42_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
