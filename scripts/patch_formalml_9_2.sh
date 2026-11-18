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

# The following old list lemma assumed intuition would solve the inductive
# equality cases. Its premise v' not-in l makes the replacement target an
# exactly removable marker; the proof explicitly separates replaced and
# unchanged heads while reusing List.remove and the induction hypothesis.
nin_line=$(grep -n "^    Lemma remove_replace_all_nin l v v' :" rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$nin_line"
nin_start=$((nin_line + 4))
nin_end=$((nin_line + 11))
test "$(sed -n "${nin_start}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${nin_end}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${nin_start},${nin_end}c\\    Proof.\\n      induction l as [|a l IH]; intros Hnin; simpl; [reflexivity |].\\n      assert (Ha : a <> v') by (intro E; apply Hnin; simpl; now left).\\n      assert (Hl : ~ In v' l) by (intro E; apply Hnin; simpl; now right).\\n      specialize (IH Hl).\\n      destruct (eqdec a v) as [Hav | Havn].\\n      - unfold equiv in Hav; subst a; simpl.\\n        repeat match goal with\\n        | |- context [eqdec v v] =>\\n            destruct (eqdec v v) as [_ | Hbad]; [|unfold equiv in Hbad; contradiction]\\n        | |- context [eqdec v' v'] =>\\n            destruct (eqdec v' v') as [_ | Hbad]; [|unfold equiv in Hbad; contradiction]\\n        end.\\n        exact IH.\\n      - simpl.\\n        repeat match goal with\\n        | |- context [eqdec a v] =>\\n            destruct (eqdec a v) as [Hbad | _]; [unfold equiv in Hbad; congruence |]\\n        | |- context [eqdec v a] =>\\n            destruct (eqdec v a) as [Hbad | _]; [unfold equiv in Hbad; congruence |]\\n        | |- context [eqdec v' a] =>\\n            destruct (eqdec v' a) as [Hbad | _]; [unfold equiv in Hbad; congruence |]\\n        end.\\n        f_equal; exact IH.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v

# The upstream inclusion-of-append equivalence leaves a goal after
# intuition under Rocq 9.2. Reuse Stdlib's in_app_iff directly, with
# no new list inclusion definition and no strengthening of assumptions.
incl_line=$(grep -n "^    Lemma incl_app_iff " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$incl_line"
incl_start=$((incl_line + 2))
incl_end=$((incl_line + 6))
test "$(sed -n "${incl_start}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${incl_end}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${incl_start},${incl_end}c\\    Proof.\\n      unfold incl; split.\\n      - intros [Hl Hm] x Hx.\\n        apply in_app_iff in Hx.\\n        destruct Hx as [Hxl | Hxm]; [exact (Hl x Hxl) | exact (Hm x Hxm)].\\n      - intros Hall; split; intros x Hx; apply Hall; apply in_app_iff.\\n        + left; exact Hx.\\n        + right; exact Hx.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v

# The upstream not-included witness proof relies on intuition to supply
# the tail obstruction under Rocq 9.2. Use the maintained List.incl and
# in_dec APIs and construct the witness by explicit induction.
nincl_line=$(grep -n "^    Lemma nincl_exists " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$nincl_line"
nincl_start=$((nincl_line + 2))
nincl_end=$((nincl_line + 13))
test "$(sed -n "${nincl_start}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${nincl_end}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${nincl_start},${nincl_end}c\\    Proof.\\n      induction l1 as [|a l1 IH]; intros Hbad.\\n      - exfalso; apply Hbad; intros x Hx; inversion Hx.\\n      - destruct (in_dec dec a l2) as [Ha | Hna].\\n        + assert (Htail : ~ incl l1 l2).\\n          { intro Hsub; apply Hbad; intros x [Heq | Hin].\\n            - subst x; exact Ha.\\n            - apply Hsub; exact Hin. }\\n          destruct (IH Htail) as [x [Hin Hnotin]].\\n          exists x; split; [right; exact Hin | exact Hnotin].\\n        + exists a; split; [left; reflexivity | exact Hna].\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v

# The legacy Proper(set_inter) proof relied on intuition in a focused cut.
# Replace it with direct pointwise set-equivalence transport, reusing the
# already proved set_inter_intro/set_inter_elim and Proper infrastructure.
inter_line=$(grep -n "^    Global Instance set_inter_equivlist_proper " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$inter_line"
inter_start=$((inter_line + 1))
inter_end=$((inter_line + 8))
test "$(sed -n "${inter_start}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${inter_end}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${inter_start},${inter_end}c\\    Proof.\\n      unfold Proper, respectful, equivlist.\\n      intros a a' Ha b b' Hb x; split; intro Hx.\\n      - apply set_inter_elim in Hx.\\n        destruct Hx as [Hax Hbx]; apply set_inter_intro.\\n        + apply (proj1 (Ha x)); exact Hax.\\n        + apply (proj1 (Hb x)); exact Hbx.\\n      - apply set_inter_elim in Hx.\\n        destruct Hx as [Hax Hbx]; apply set_inter_intro.\\n        + apply (proj2 (Ha x)); exact Hax.\\n        + apply (proj2 (Hb x)); exact Hbx.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v

# The old NoDup/disjointness argument ended with unresolved intuition.
# Use the maintained NoDup_app_inv2 and in_split facts and explicitly
# contradict membership in the duplicate-free suffix.
nodup_line=$(grep -n "^    Lemma NoDup_app_dis " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$nodup_line"
nodup_start=$((nodup_line + 2))
nodup_end=$((nodup_line + 11))
test "$(sed -n "${nodup_start}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${nodup_end}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${nodup_start},${nodup_end}c\\    Proof.\\n      unfold disjoint; intros Hdup x Ha Hb.\\n      destruct (in_split x a Ha) as [a1 [a2 Heq]]; subst a.\\n      rewrite <- app_assoc in Hdup.\\n      apply NoDup_app_inv2 in Hdup.\\n      inversion Hdup as [|y ys Hnot Htail]; subst.\\n      apply Hnot; apply in_or_app; right; exact Hb.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v

# Reuse Stdlib List.in_seq rather than the upstream fragile intuition
# induction whose hypothesis numbering changed under Rocq 9.2.
seq_line=$(grep -n "^    Lemma seq_ge " rocq/lib_utils/LibUtilsListAdd.v | cut -d: -f1)
test -n "$seq_line"
seq_start=$((seq_line + 2))
seq_end=$((seq_line + 7))
test "$(sed -n "${seq_start}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Proof."
test "$(sed -n "${seq_end}p" rocq/lib_utils/LibUtilsListAdd.v)" = "    Qed."
sed -i "${seq_start},${seq_end}c\\    Proof.\\n      intros x Hx.\\n      apply in_seq in Hx.\\n      lia.\\n    Qed." \
  rocq/lib_utils/LibUtilsListAdd.v

# The substring-prefix theorem follows directly from two already proved
# upstream lemmas (substring_split and prefix_app). Avoid the old partial
# induction/intuition proof and preserve its exact quantified statement.
substring_line=$(grep -n "^  Lemma substring_le_prefix " rocq/lib_utils/LibUtilsStringAdd.v | cut -d: -f1)
test -n "$substring_line"
substring_start=$((substring_line + 3))
substring_end=$((substring_line + 8))
test "$(sed -n "${substring_start}p" rocq/lib_utils/LibUtilsStringAdd.v)" = "  Proof."
test "$(sed -n "${substring_end}p" rocq/lib_utils/LibUtilsStringAdd.v)" = "  Qed."
sed -i "${substring_start},${substring_end}c\\  Proof.\\n    intros Hle.\\n    replace m with (n + (m - n)) by lia.\\n    rewrite <- (substring_split s n (m-n) l).\\n    apply prefix_app.\\n  Qed." \
  rocq/lib_utils/LibUtilsStringAdd.v

# The legacy sorting-insertion witness proof does not completely close
# under Rocq 9.2. Reuse asymmetric_over_swap/cons_inv to reduce the
# recursive case, and use the asymmetry-comparability witness in the
# otherwise-dropping case. No algorithm or theorem statement is changed.
sort_line=$(grep -n "^    Lemma insertion_sort_insert_in_strong " rocq/lib_utils/LibUtilsSortingAdd.v | cut -d: -f1)
test -n "$sort_line"
sort_start=$((sort_line + 3))
sort_end=$((sort_line + 13))
test "$(sed -n "${sort_start}p" rocq/lib_utils/LibUtilsSortingAdd.v)" = "    Proof."
test "$(sed -n "${sort_end}p" rocq/lib_utils/LibUtilsSortingAdd.v)" = "    Qed."
sed -i "${sort_start},${sort_end}c\\    Proof.\\n      revert x a contr.\\n      induction l as [|b l IH]; intros x a0 contr Hin; simpl in *.\\n      - destruct Hin as [Heq | Hempty]; [subst x; simpl; auto | contradiction].\\n      - destruct (R_dec a0 b) as [Hab | Hab].\\n        + destruct Hin as [Heq | [Heq | Htail]]; subst; simpl; tauto.\\n        + destruct (R_dec b a0) as [Hba | Hba].\\n          * assert (Htailcontr : asymmetric_over R (a0::l)).\\n            { exact (asymmetric_over_cons_inv (asymmetric_over_swap R contr)). }\\n            destruct Hin as [Heq | [Heq | Htail]].\\n            -- right; apply (IH x a0 Htailcontr); left; exact Heq.\\n            -- subst x; left; reflexivity.\\n            -- right; apply (IH x a0 Htailcontr); right; exact Htail.\\n          * assert (Heq : a0 = b).\\n            { apply (contr a0 b); simpl; auto. }\\n            subst a0; simpl.\\n            destruct Hin as [Heq' | [Heq' | Htail]]; subst; simpl; tauto.\\n    Qed." \
  rocq/lib_utils/LibUtilsSortingAdd.v

# Insertion-sort membership under global comparability: the maintained
# asymmetric_asymmetric_over lemma supplies the exact local premise of
# insertion_sort_in_strong, rather than relying on intuition.
sortin_line=$(grep -n "^    Lemma insertion_sort_in {A R R_dec} " rocq/lib_utils/LibUtilsSortingAdd.v | cut -d: -f1)
test -n "$sortin_line"
sortin_start=$((sortin_line + 3))
sortin_end=$((sortin_line + 5))
test "$(sed -n "${sortin_start}p" rocq/lib_utils/LibUtilsSortingAdd.v)" = "    Proof."
test "$(sed -n "${sortin_end}p" rocq/lib_utils/LibUtilsSortingAdd.v)" = "    Qed."
sed -i "${sortin_start},${sortin_end}c\\    Proof.\\n      intro Hin.\\n      eapply insertion_sort_in_strong.\\n      - apply asymmetric_asymmetric_over; exact contr.\\n      - exact Hin.\\n    Qed." \
  rocq/lib_utils/LibUtilsSortingAdd.v

# FormalML's Hilbert parallelogram identity rewrites scalar negation
# while the negation is still hidden by the [minus] abbreviation.
# Expose the standard group subtraction before applying maintained
# module-space distribution/scalar-associativity equalities.
test "$(sed -n 689p rocq/CertRL/LM/hilbert.v)" = "rewrite scal_distr_l scal_opp_r scal_assoc."
sed -i "689c\\unfold minus; rewrite scal_distr_l scal_opp_r scal_assoc." \
  rocq/CertRL/LM/hilbert.v

# The exact normalization by Rinv_r already removes the only product
# by one in this Hilbert convexity side condition under Rocq 9.2.
# Preserve the source algebraic goal, making the now-redundant rewrite
# optional rather than aborting the valid proof.
test "$(sed -n 742p rocq/CertRL/LM/hilbert.v)" = "rewrite Rmult_1_r."
sed -i "742c\\try rewrite Rmult_1_r." rocq/CertRL/LM/hilbert.v

# D079: Under Rocq 9.2 the old Hilbert convexity tactic attempts to
# discharge a nonzero-divisor obligation with Rgt_not_eq, whose goal
# interface no longer matches. Discharge it immediately using Stdlib Lra.
# This preserves every statement and removes an obsolete proof branch.
test "$(sed -n 741p rocq/CertRL/LM/hilbert.v)" = "rewrite Rinv_r."
test "$(sed -n 745p rocq/CertRL/LM/hilbert.v)" = "apply Rgt_not_eq, Rlt_0_2."
sed -i "741c\\rewrite Rinv_r; [|lra]." rocq/CertRL/LM/hilbert.v
sed -i '745d' rocq/CertRL/LM/hilbert.v
sed -i '23a From Stdlib Require Import Lra.' rocq/CertRL/LM/hilbert.v

# D079: Derive association-list lookup existence by induction on the
# existing Stdlib list representation. Do not recreate a lookup function
# or assume a choice principle: the witness is the value in the matching
# pair and the recursion uses the maintained upstream lookup definition.
assoc_line=$(grep -n "^    Lemma in_dom_lookup_strong :" rocq/lib_utils/LibUtilsAssoc.v | cut -d: -f1)
test -n "$assoc_line"
assoc_start=$((assoc_line + 1))
assoc_end=$((assoc_line + 7))
test "$(sed -n "${assoc_start}p" rocq/lib_utils/LibUtilsAssoc.v)" = "    Proof."
test "$(sed -n "${assoc_end}p" rocq/lib_utils/LibUtilsAssoc.v)" = "    Qed."
sed -i "${assoc_start},${assoc_end}c\\    Proof.\\n      induction l as [|[key value] tail IH]; intros target Hin; simpl in *.\\n      - contradiction.\\n      - destruct (dec target key) as [Heq | Hneq].\\n        + exists value; reflexivity.\\n        + assert (Htail : In target (domain tail)).\\n          { destruct Hin as [Hhead | Hfound].\\n            - exfalso; apply Hneq; symmetry; exact Hhead.\\n            - exact Hfound. }\\n          exact (IH target Htail).\\n    Qed." \
  rocq/lib_utils/LibUtilsAssoc.v

# D084: Upstream NoDup proof used an incomplete decidable-equality
# automation. Construct the Boolean witness from in_domain_in and the
# maintained Stdlib existsb_exists lemma; no duplicate representation.
distinct_line=$(grep -n "^    Lemma bdistinct_domain_NoDup " rocq/lib_utils/LibUtilsAssoc.v | cut -d: -f1)
test -n "$distinct_line"
distinct_start=$((distinct_line + 2))
distinct_end=$((distinct_line + 15))
test "$(sed -n "${distinct_start}p" rocq/lib_utils/LibUtilsAssoc.v)" = "    Proof."
test "$(sed -n "${distinct_end}p" rocq/lib_utils/LibUtilsAssoc.v)" = "    Qed."
sed -i "${distinct_start},${distinct_end}c\\    Proof.\\n      induction l as [|[key value] tail IH]; simpl.\\n      - constructor.\\n      - destruct (existsb (fun z : A*B => key ==b fst z)\\n                    (bdistinct_domain tail)) eqn:Hmember.\\n        + exact IH.\\n        + constructor; [|exact IH].\\n          intros Hin.\\n          destruct (in_domain_in Hin) as [v Hv].\\n          assert (Hexists :\\n            existsb (fun z : A*B => key ==b fst z)\\n              (bdistinct_domain tail) = true).\\n          { apply existsb_exists.\\n            exists (key,v); split; [exact Hv |].\\n            simpl; unfold equiv_decb.\\n            destruct (equiv_dec key key) as [_ | Hbad].\\n            - reflexivity.\\n            - exfalso; apply Hbad; reflexivity. }\\n          rewrite Hmember in Hexists; discriminate.\\n    Qed." \
  rocq/lib_utils/LibUtilsAssoc.v

# D087: The two inclusion directions of domain-append restriction
# are immediate consequences of Stdlib in_app_iff; old intuition
# leaves an unsolved subgoal under current Rocq. Reuse the existing
# lookup_equiv_on predicate and prove both directions explicitly.
lookapp_line=$(grep -n "^    Lemma lookup_equiv_on_dom_app  " rocq/lib_utils/LibUtilsAssoc.v | cut -d: -f1)
test -n "$lookapp_line"
lookapp_start=$((lookapp_line + 5))
lookapp_end=$((lookapp_line + 7))
test "$(sed -n "${lookapp_start}p" rocq/lib_utils/LibUtilsAssoc.v)" = "    Proof."
test "$(sed -n "${lookapp_end}p" rocq/lib_utils/LibUtilsAssoc.v)" = "    Qed."
sed -i "${lookapp_start},${lookapp_end}c\\    Proof.\\n      unfold lookup_equiv_on.\\n      intro Hall; split; intros x Hx; apply Hall; apply in_app_iff.\\n      - left; exact Hx.\\n      - right; exact Hx.\\n    Qed." \
  rocq/lib_utils/LibUtilsAssoc.v

# D088: The standard constructors, rather than intuition over an
# inductive Prop, prove that nil is a sublist of every list.
subnil_line=$(grep -n "^    Lemma sublist_nil_l " rocq/lib_utils/LibUtilsSublist.v | cut -d: -f1)
test -n "$subnil_line"
subnil_start=$((subnil_line + 1))
subnil_end=$((subnil_line + 3))
test "$(sed -n "${subnil_start}p" rocq/lib_utils/LibUtilsSublist.v)" = "    Proof."
test "$(sed -n "${subnil_end}p" rocq/lib_utils/LibUtilsSublist.v)" = "    Qed."
sed -i "${subnil_start},${subnil_end}c\\    Proof.\\n      induction l as [|x l IH].\\n      - apply sublist_nil.\\n      - apply sublist_skip; exact IH.\\n    Qed." \
  rocq/lib_utils/LibUtilsSublist.v

# D088: Old FormalML Compat proof accidentally reused a B-valued
# lookup result x as the A-valued lookup key. Restore the original
# A-valued key y; no theorem statements or semantics are weakened.
grep -Fq "(@equiv_dec A (@eq A) equiv0 H) l' x); congruence." \
  rocq/lib_utils/LibUtilsCompat.v
sed -i "127s/l' x); congruence\\./l' y); congruence./" \
  rocq/lib_utils/LibUtilsCompat.v

# D089: The legacy PreOrder tactic accidentally consumes the transitivity
# goal under Rocq 9.2. Prove reflexivity with sublist_nil/sublist_cons
# and transitivity by induction on the existing second sublist proof.
subpre_line=$(grep -n "^    Global Instance sublist_pre : PreOrder sublist." rocq/lib_utils/LibUtilsSublist.v | cut -d: -f1)
test -n "$subpre_line"
subpre_start=$((subpre_line + 1))
subpre_end=$((subpre_line + 11))
test "$(sed -n "${subpre_start}p" rocq/lib_utils/LibUtilsSublist.v)" = "    Proof."
test "$(sed -n "${subpre_end}p" rocq/lib_utils/LibUtilsSublist.v)" = "    Qed."
sed -i "${subpre_start},${subpre_end}c\\    Proof.\\n      split.\\n      - intro l; induction l as [|x xs IH].\\n        + apply sublist_nil.\\n        + apply sublist_cons; exact IH.\\n      - intros u v w Huv Hvw.\\n        revert u Huv.\\n        induction Hvw as [|a s t Hst IH|a s t Hst IH]; intros u Hu.\\n        + apply sublist_nil_r in Hu; subst u; apply sublist_nil.\\n        + inversion Hu; subst.\\n          * apply sublist_cons; apply IH; assumption.\\n          * apply sublist_skip; apply IH; assumption.\\n        + apply sublist_skip; apply IH; assumption.\\n    Qed." \
  rocq/lib_utils/LibUtilsSublist.v
