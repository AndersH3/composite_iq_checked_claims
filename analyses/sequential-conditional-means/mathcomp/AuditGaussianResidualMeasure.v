(** Module: AuditGaussianResidualMeasure.v
    Purpose: Audit the transitive logical assumptions of the Gaussian
    residual-measure theorems and the auxiliary Borel translation lemma.
    Run separately from compilation and independent kernel checking.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; no new mathematical axioms.
*)
Require Import GaussianResidualMeasure.

(* Audit the reusable measurability certificate for real translation. *)
Print Assumptions gmc_translation_measurable.
(* Audit translation invariance on arbitrary measurable events. *)
Print Assumptions gmc_lebesgue_translation.
(* Audit the centered Gaussian probability law. *)
Print Assumptions gmc_normal_centered_event.
(* Audit integrated factorization on measurable rectangles. *)
Print Assumptions gmc_transformed_residual_rectangle.
