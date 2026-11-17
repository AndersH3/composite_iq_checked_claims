#!/bin/sh
# FormalML Rocq 9.2 compatibility proof patch script.
#
# Intended upstream version: IBM/FormalML commit
# 8ee433dc802fca35f6bceb6dacb69d3c1315e886 (2026-09-29).
# Purpose: Fix tactics in upstream Stdlib list/order and Coquelicot
# fixed-point proofs whose former intuition/automation leaves subgoals
# open under Rocq 9.2. Only proof bodies are replaced; all original
# declarations and statements remain unchanged.
# No axiom, parameter, Admitted, Abort or unsafe tactic is inserted.
# Each target line is checked before modification to fail closed if
# the pinned upstream commit differs.
#
# AI disclosure: AI-assisted compatibility refactoring; verification
# requires compiling the unmodified theorem statements with Rocq.
# Researcher/requester: Anders Hellström.
#
# Run from the root of the already checked out FormalML repository.
set -eu
# Upstream 2026-09-29 FormalML breaks here under Rocq 9.2:
# the former "intuition; f_equal; auto" leaves an open goal.
# Patch only this proof, retaining its original exact statement.
# No new axiom, admitted lemma or foundational rewrite is added.
test "$(sed -n 614p rocq/lib_utils/LibUtilsListAdd.v)" = \
  "        induction l1; destruct l2; simpl; intuition."
test "$(sed -n 615p rocq/lib_utils/LibUtilsListAdd.v)" = \
  "        f_equal; auto."
sed -i "614,615c\\        induction l1 as [|a l1 IH]; intros [|b l2] Hlen; simpl in *; try discriminate; try reflexivity.\n        inversion Hlen; subst; rewrite IH by assumption; reflexivity." \
  rocq/lib_utils/LibUtilsListAdd.v
# The next upstream forallb2/forallb equivalence also relies on
# fragile firstorder search; replace its proof with an explicit
# shape split and IH, preserving its statement and all assumptions.
test "$(sed -n 624p rocq/lib_utils/LibUtilsListAdd.v)" = \
  "        induction l1; destruct l2; simpl; intuition;"
test "$(sed -n 625p rocq/lib_utils/LibUtilsListAdd.v)" = \
  "          repeat rewrite andb_true_iff in *; firstorder."
sed -i "624,625c\\        induction l1 as [|a l1 IH]; intros [|b l2]; simpl.\n        - split; intros; intuition.\n        - split; intros H; [destruct H as [Hlen _]; discriminate | discriminate].\n        - split; intros H; [destruct H as [Hlen _]; discriminate | discriminate].\n        - split.\n          + intros [Hlen H].\n            injection Hlen as Hlen.\n            apply andb_true_iff in H as [Ha Htail].\n            apply andb_true_iff; split; [exact Ha |].\n            apply (proj1 (IH l2)); split; assumption.\n          + intros H.\n            apply andb_true_iff in H as [Ha Htail].\n            apply (proj2 (IH l2)) in Htail.\n            destruct Htail as [Hlen Htail].\n            split; [simpl; f_equal; exact Hlen |].\n            apply andb_true_iff; split; assumption." \
  rocq/lib_utils/LibUtilsListAdd.v
# Repair the next unclosed upstream proof with an explicit
# boolean-to-Forall2 induction (exact original statement).
test "$(sed -n 649p rocq/lib_utils/LibUtilsListAdd.v)" = \
  "        induction l1; destruct l2; simpl; intuition; inv;"
test "$(sed -n 650p rocq/lib_utils/LibUtilsListAdd.v)" = \
  "          repeat rewrite andb_true_iff in *; firstorder."
sed -i "649,650c\\        induction l1 as [|a l1 IH]; intros [|b l2]; simpl.\n        - split; intro H; constructor.\n        - split; intro H; [discriminate H | inversion H].\n        - split; intro H; [discriminate H | inversion H].\n        - split.\n          + intro H.\n            apply andb_true_iff in H as [Hab Htail].\n            constructor; [exact Hab |].\n            apply (proj1 (IH l2)); exact Htail.\n          + intro H.\n            inversion H as [|a0 b0 l10 l20 Hab Htail]; subst.\n            apply andb_true_iff; split.\n            * exact Hab.\n            * apply (proj2 (IH l2)); exact Htail." \
  rocq/lib_utils/LibUtilsListAdd.v
# FormalML upstream also leaves the reflexive direction of
# the lifted PartialOrder proof open with Rocq 9.2. Replace
# just that tactic, preserving the original proposition and
# obtaining list reflexivity from the registered Stdlib instance.
test "$(grep -Fc -- "- repeat red; subst; intuition." rocq/lib_utils/LibUtilsListAdd.v)" -eq 1
sed -i "s/- repeat red; subst; intuition\./- subst; split; apply Forall2_refl; typeclasses eauto./" rocq/lib_utils/LibUtilsListAdd.v
# Rocq 9.2 exposes an incomplete upstream boolean pair-order
# proof; replace just its proof script, not its proposition.
# Use the already established nonreflexive append lemma and
# the standard forallb_app/andb_true_iff identities.
ordline=$(grep -n "^    Lemma forallb_ordpairs_refl_app_cons " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$ordline"
proofline=$((ordline + 5))
qedline=$((ordline + 11))
test "$(sed -n "${proofline}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${qedline}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${proofline},${qedline}c\\    Proof.\\n      intros Hlist Hxx Hall.\\n      rewrite forallb_ordpairs_refl_conj in Hlist.\\n      apply andb_true_iff in Hlist as [Hord Hdiag].\\n      rewrite forallb_ordpairs_refl_conj.\\n      apply andb_true_iff; split.\\n      - apply forallb_ordpairs_app_cons; assumption.\\n      - rewrite forallb_app; simpl.\\n        rewrite Hdiag, Hxx; intuition.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v
# Upstream remove_in_neq depended on intuition to discharge an
# induction case; make the two membership directions explicit.
# The statement and use of Stdlib List.remove remain unchanged.
remove_line=$(grep -n "^    Lemma remove_in_neq$" rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$remove_line"
pstart=$((remove_line + 3))
pend=$((remove_line + 9))
test "$(sed -n "${pstart}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${pend}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${pstart},${pend}c\\    Proof.\\n      intros Hxy.\\n      induction l as [|a l IH]; simpl.\\n      - tauto.\\n      - destruct (eqdec y a) as [Hya | Hya]; subst.\\n        + split.\\n          * intros [Hxa | Hin]; [congruence | exact (proj1 IH Hin)].\\n          * intros Hin; right; exact (proj2 IH Hin).\\n        + simpl; split.\\n          * intros [Hxa | Hin].\\n            -- left; exact Hxa.\\n            -- right; exact (proj1 IH Hin).\\n          * intros [Hxa | Hin].\\n            -- left; exact Hxa.\\n            -- right; exact (proj2 IH Hin).\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v
# The upstream fold/filter induction relies on a fragile
# intuition pass that leaves the membership contradiction open.
# Use Stdlib filter_In with explicit nonmembership reasoning.
foldline=$(grep -n "^    Lemma fold_left_remove_all_In " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$foldline"
proofline=$((foldline + 4))
qedline=$((foldline + 14))
test "$(sed -n "${proofline}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${qedline}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${proofline},${qedline}c\\    Proof.\\n      revert init a.\\n      induction l as [|b l IH]; intros init a Hin; simpl in *.\\n      - split; [exact Hin | tauto].\\n      - specialize (IH (filter (nequiv_decb b) init) a Hin).\\n        destruct IH as [HinFiltered HnotTail].\\n        apply filter_In in HinFiltered.\\n        destruct HinFiltered as [HinInit HneqBool].\\n        split; [exact HinInit |].\\n        intros [Hab | Htail].\\n        + subst b.\\n          unfold nequiv_decb, equiv_decb, negb in HneqBool.\\n          destruct (equiv_dec a a) as [_ | Hcontra];\\n            [discriminate | congruence].\\n        + apply HnotTail; exact Htail.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v
# fixed_point.v upstream relied on intuition to discharge
# an elementary successor-order side condition. Under 9.2 that
# goal remains open and the next existential tactic runs on it.
# Replace only the induction/order side-condition tactic.
test "$(sed -n 1147p rocq/CertRL/LM/fixed_point.v)" = "apply Hev."
test "$(sed -n 1148p rocq/CertRL/LM/fixed_point.v)" = "intuition."
sed -i "1148c\\apply Nat.le_add_r." rocq/CertRL/LM/fixed_point.v


# Rocq 9.2 no longer closes upstream's ad hoc equivalence cases.
# Reprove remove/map commutation by structural induction. Separate the
# replacement-head and removed-head cases, discharging impossible
# equivalence equations using the two unchanged separation hypotheses.
# Only the proof of the exact upstream proposition is replaced.
replace_line=$(grep -n "^    Lemma replace_all_remove_neq " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$replace_line"
proofline=$((replace_line + 7))
qedline=$((replace_line + 17))
test "$(sed -n "${proofline}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${qedline}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${proofline},${qedline}c\\    Proof.\\n      intros Hv Hn.\\n      induction l as [|a l IH]; simpl; [reflexivity |].\\n      destruct (eqdec a v) as [Hav | Havn].\\n      - unfold equiv in Hav; subst a.\\n        destruct (eqdec v v) as [_ | Hvv]; [|unfold equiv in Hvv; contradiction].\\n        destruct (eqdec v0 n) as [H0n | _]; [unfold equiv in H0n; congruence |].\\n        destruct (eqdec v0 v) as [H0v | _]; [unfold equiv in H0v; congruence |].\\n        simpl; rewrite IH.\\n        destruct (eqdec v v) as [_ | Hvv2]; [reflexivity |].\\n        unfold equiv in Hvv2; congruence.\\n      - destruct (eqdec v0 a) as [H0a | H0a].\\n        + unfold equiv in H0a; subst a.\\n          destruct (eqdec v0 v) as [H0v | _]; [unfold equiv in H0v; congruence |].\\n          exact IH.\\n        + destruct (eqdec a v) as [Hav2 | _]; [unfold equiv in Hav2; congruence |].\\n          destruct (eqdec v0 a) as [H0a2 | _]; [unfold equiv in H0a2; congruence |].\\n          simpl.\\n          destruct (eqdec a v) as [Hav3 | _]; [unfold equiv in Hav3; congruence |].\\n          f_equal; exact IH.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v
