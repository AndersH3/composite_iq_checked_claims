(** Module: AuditProductLawIndependence.v
    Purpose: Reproduce the independently verified product-law theorem's
    transitive logical-assumption audit without signature pretty-printing.
    Researcher/requester: Anders Hellström.
    AI disclosure: AI-assisted audit source; no new declarations.
*)
Require Import ProductLawIndependence.

(* Audit the equivalence of independence and joint-law factorization. *)
Print Assumptions independent_rvs_iff_product_joint_law.
