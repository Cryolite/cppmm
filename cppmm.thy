theory Cppmm
imports Main
begin


(* N3132 6.3 Auxiliary definitions *)
definition relation_over where
  "relation_over s rel = ((Domain rel <= s) & (Range rel <= s))"

definition relation_int where
  "relation_int s rel = rel Int s <*> s"

definition strict_preorder where
  "strict_preorder ord = (irrefl ord & trans ord)"

definition total_over where
  "total_over s ord = total_on s ord"

definition strict_total_order_over where
  "strict_total_order_over s ord = (strict_preorder ord & total_over s ord)"

definition adjacent_less_pred where
  "adjacent_less_pred ord pred x y = ((pred x) & ord (x, y) & ~(EX z. (pred z) & ord (x, z) & ord (z, y)))"

definition adjacent_less where
  "adjacent_less ord x y = (ord (x, y) & ~(EX z. ord (x, z) & ord (z, y)))"


(* N3132 6.4 Memory actions: types *)
types action_id = string

types thread_id = string

types location  = string

types val       = string

datatype memory_order_enum =
    Mo_seq_cst
  | Mo_relaxed
  | Mo_release
  | Mo_acquire
  | Mo_consume
  | Mo_acq_rel

datatype action =
    Lock action_id thread_id location
  | Unlock action_id thread_id location
  | Atomic_load action_id thread_id memory_order_enum location val
  | Atomic_store action_id thread_id memory_order_enum location val
  | Atomic_rmw action_id thread_id memory_order_enum location val val
  | Load action_id thread_id location val
  | Store action_id thread_id location val
  | Fence action_id thread_id memory_order_enum


(* N3132 6.5 Memory actions: routine accessor functions *)
definition action_id_of where
  "action_id_of a ==
     case a of (Lock aid _ _)             => aid |
               (Unlock aid _ _)           => aid |
               (Atomic_load aid _ _ _ _)  => aid |
               (Atomic_store aid _ _ _ _) => aid |
               (Atomic_rmw aid _ _ _ _ _) => aid |
               (Load aid _ _ _)           => aid |
               (Store aid _ _ _)          => aid |
               (Fence aid _ _)            => aid"

definition thread_id_of where
  "thread_id_of a ==
     case a of (Lock _ tid _)             => tid |
               (Unlock _ tid _)           => tid |
               (Atomic_load _ tid _ _ _)  => tid |
               (Atomic_store _ tid _ _ _) => tid |
               (Atomic_rmw _ tid _ _ _ _) => tid |
               (Load _ tid _ _)           => tid |
               (Store _ tid _ _)          => tid |
               (Fence _ tid _)            => tid"

definition memory_order where
  "memory_order a ==
     case a of (Atomic_load _ _ mem_ord _ _)  => Some mem_ord |
               (Atomic_store _ _ mem_ord _ _) => Some mem_ord |
               (Atomic_rmw _ _ mem_ord _ _ _) => Some mem_ord |
               (Fence _ _ mem_ord)            => Some mem_ord |
               _                              => None"

definition location_of where
  "location_of a ==
     case a of (Lock _ _ l)             => Some l |
               (Unlock _ _ l)           => Some l |
               (Atomic_load _ _ _ l _)  => Some l |
               (Atomic_store _ _ _ l _) => Some l |
               (Atomic_rmw _ _ _ l _ _) => Some l |
               (Load _ _ l _)           => Some l |
               (Store _ _ l _)          => Some l |
               (Fence _ _ _)            => None"

definition value_read where
  "value_read a ==
     case a of (Atomic_load _ _ _ _ v)  => Some v |
               (Atomic_rmw _ _ _ _ v _) => Some v |
               (Load _ _ _ v)           => Some v |
               _                        => None"

definition value_written where
  "value_written a ==
     case a of (Atomic_store _ _ _ _ v) => Some v |
               (Atomic_rmw _ _ _ _ _ v) => Some v |
               (Store _ _ _ v)          => Some v |
               _                        => None"

definition is_lock where
  "is_lock a == (case a of (Lock _ _ _) => True | _ => False)"

definition is_unlock where
  "is_unlock a == (case a of (Unlock _ _ _) => True | _ => False)"

definition is_atomic_load where
  "is_atomic_load a == (case a of (Atomic_load _ _ _ _ _) => True | _ => False)"

definition is_atomic_store where
  "is_atomic_store a == (case a of (Atomic_store _ _ _ _ _) => True | _ => False)"

definition is_atomic_rmw where
  "is_atomic_rmw a == (case a of (Atomic_rmw _ _ _ _ _ _) => True | _ => False)"

definition is_load where
  "is_load a == (case a of (Load _ _ _ _) => True | _ => False)"

definition is_store where
  "is_store a == (case a of (Store _ _ _ _) => True | _ => False)"

definition is_fence where
  "is_fence a == (case a of (Fence _ _ _) => True | _ => False)"


(* N3132 6.6 Memory actions: useful collections of actions *)
definition is_lock_or_unlock where
  "is_lock_or_unlock a == (is_lock a | is_unlock a)"

definition is_atomic_action where
  "is_atomic_action a == (is_atomic_load a | is_atomic_store a | is_atomic_rmw a)"

definition is_load_or_store where
  "is_load_or_store a == (is_load a | is_store a)"

definition is_read where
  "is_read a == (is_atomic_load a | is_atomic_rmw a | is_load a)"

definition is_write where
  "is_write a == (is_atomic_store a | is_atomic_rmw a | is_store a)"

definition is_synchronization_action where
  "is_synchronization_action a == (is_lock_or_unlock a | is_atomic_action a)"

definition is_acquire where
  "is_acquire a ==
     (case memory_order a of
        Some mem_ord =>
          (((mem_ord : {Mo_acquire, Mo_acq_rel, Mo_seq_cst}) &
               (is_read a | is_fence a)) |
           ((mem_ord = Mo_consume) & is_fence a))
      | None => is_lock a)"

definition is_consume where
  "is_consume a == (is_read a & (memory_order a = Some Mo_consume))"

definition is_release where
  "is_release a ==
     (case memory_order a of
        Some mem_ord =>
          ((mem_ord : {Mo_release, Mo_acq_rel, Mo_seq_cst}) &
           (is_write a | is_fence a))
      | None => is_lock a)"

definition is_seq_cst where
  "is_seq_cst a == (memory_order a = Some Mo_seq_cst)"


(* N3132 6.7 Location kinds *)
datatype location_kind =
    Mutex
  | Non_atomic
  | Atomic


(* Candidate execution, additionally defined by Cryolite *)
types threads = "thread_id set"

types actions = "action set"

types location_typing = "location => location_kind"

types sequenced_before = "action * action => bool"

types additional_synchronized_with = "action * action => bool"

types data_dependency = "action * action => bool"

types control_dependency = "action * action => bool"

types reads_from = "action * action => bool"

types sequential_consistency = "action * action => bool"

types modification_order = "action * action => bool"

datatype "candidate_execution" =
  Candidate_execution "threads"
                      "actions"
                      "location_typing"
                      "sequenced_before"
                      "additional_synchronized_with"
                      "data_dependency"
                      "control_dependency"
                      "reads_from"
                      "sequential_consistency"
                      "modification_order"

(* Accessor functions for candidate execution*)
definition threads_of where
  "threads_of x ==
     (case x of Candidate_execution ts _ _ _ _ _ _ _ _ _ => ts)"

definition actions_of where
  "actions_of x ==
     (case x of Candidate_execution _ as _ _ _ _ _ _ _ _ => as)"

definition location_typing_of where
  "location_typing_of x ==
     (case x of Candidate_execution _ _ lt _ _ _ _ _ _ _ => lt)"

definition sequenced_before_of where
  "sequenced_before_of x ==
     (case x of Candidate_execution _ _ _ sb _ _ _ _ _ _ => sb)"

definition additional_synchronized_with_of where
  "additional_synchronized_with_of x ==
     (case x of Candidate_execution _ _ _ _ asw _ _ _ _ _ => asw)"

definition data_dependency_of where
  "data_dependency_of x ==
     (case x of Candidate_execution _ _ _ _ _ dd _ _ _ _ => dd)"

definition control_dependency_of where
  "control_dependency_of x ==
     (case x of Candidate_execution _ _ _ _ _ _ cd _ _ _ => cd)"

definition reads_from_of where
  "reads_from_of x ==
     (case x of Candidate_execution _ _ _ _ _ _ _ rf _ _ => rf)"

definition sequential_consistency_of where
  "sequential_consistency_of x ==
     (case x of Candidate_execution _ _ _ _ _ _ _ _ sc _ => sc)"

definition modification_order_of where
  "modification_order_of x ==
     (case x of Candidate_execution _ _ _ _ _ _ _ _ _ mo => mo)"


(* N3132 6.7 Location kinds (contd.) *)
definition actions_respect_location_kinds where
  "actions_respect_location_kinds ce ==
     (ALL a : (actions_of ce).
        (case location_of a of
           Some l =>
             (case (location_typing_of ce) l of
                Mutex => is_lock_or_unlock a
              | Non_atomic => is_load_or_store a
              | Atomic => (is_load_or_store a | is_atomic_action a))
         | None => True))"

definition is_at_location_kind where
  "is_at_location_kind ce a lk0 ==
     (case location_of a of
        Some l => (location_typing_of ce l = lk0)
      | None => False)"

definition is_at_mutex_location where
  "is_at_mutex_location ce a == is_at_location_kind ce a Mutex"

definition is_at_non_atomic_location where
  "is_at_non_atomic_location ce a == is_at_location_kind ce a Non_atomic"

definition is_at_atomic_location where
  "is_at_atomic_location ce a == is_at_location_kind ce a Atomic"


(* N3132 6.8 Well-formed threads *)
definition same_thread where
  "same_thread a b == (thread_id_of a = thread_id_of b)"

(* same_thread as a binary relation, added by Cryolite *)
definition same_thread_rel where
  "same_thread_rel == (%(a, b). same_thread a b)"

definition threadwise_relation_over where
  "threadwise_relation_over s rel ==
     (relation_over s rel & (ALL (a, b) : rel. (same_thread_rel (a, b))))"

definition same_location where
  "same_location a b == (location_of a = location_of b)"

(* same_location_rel as a binary relation, added by Cryolite *)
definition same_location_rel where
  "same_location_rel == (%(a, b). same_location a b)"

definition locations_of where
  "locations_of as ==
     {l. (EX a : as. (location_of a = Some l))}"

definition well_formed_action where
  "well_formed_action a ==
     (case a of
        Atomic_load _ _ mem_ord _ _
          => (mem_ord : {Mo_relaxed, Mo_acquire, Mo_seq_cst, Mo_consume})
      | Atomic_store _ _ mem_ord _ _
          => (mem_ord : {Mo_relaxed, Mo_release, Mo_seq_cst})
      | Atomic_rmw _ _ mem_ord _ _ _
          => (mem_ord : {Mo_relaxed, Mo_release, Mo_acquire, Mo_acq_rel, Mo_seq_cst, Mo_consume})
      | _ => True)"

definition well_formed_threads where
  "well_formed_threads ce ==
     (inj_on action_id_of (actions_of ce) &
      (ALL a : (actions_of ce). well_formed_action a) &
      threadwise_relation_over (actions_of ce) (sequenced_before_of ce) &
      threadwise_relation_over (actions_of ce) (data_dependency_of ce) &
      threadwise_relation_over (actions_of ce) (control_dependency_of ce) &
      strict_preorder (sequenced_before_of ce) &
      strict_preorder (data_dependency_of ce) &
      strict_preorder (control_dependency_of ce) &
      relation_over (actions_of ce) (additional_synchronized_with_of ce) &
      (ALL a : (actions_of ce). (thread_id_of a : (threads_of ce))) &
      actions_respect_location_kinds ce &
      (data_dependency_of ce) <= (sequenced_before_of ce))"

lemma same_thread_equiv: "equiv UNIV same_thread_rel"
proof
  have 10: "ALL a : UNIV. thread_id_of a = thread_id_of a" by blast
  hence 20: "ALL a : UNIV. same_thread a a" by (unfold same_thread_def) blast
  hence 30: "ALL a : UNIV. same_thread_rel (a, a)" by (unfold same_thread_rel_def) force
  hence 40: "ALL a : UNIV. (a, a) : same_thread_rel" by (unfold mem_def)
  have 50: "same_thread_rel <= UNIV" by blast
  have 60: "UNIV <= UNIV <*> UNIV" by (unfold UNIV_Times_UNIV) blast
  with 50 have 70: "same_thread_rel <= UNIV <*> UNIV" by blast
  with 40 show 80: "refl_on UNIV same_thread_rel" by (unfold refl_on_def) blast
next
  have 90: "ALL a b. (thread_id_of a = thread_id_of b) --> (thread_id_of b = thread_id_of a)" by force
  hence 100: "ALL a b. same_thread a b --> same_thread b a" by (unfold same_thread_def) blast
  hence 110: "ALL a b. same_thread_rel (a, b) --> same_thread_rel (b, a)" by (unfold same_thread_rel_def) force
  hence 120: "ALL a b. ((a, b) : same_thread_rel) --> ((b, a) : same_thread_rel)" by (unfold mem_def) blast
  thus 130: "sym same_thread_rel" by (unfold sym_def) blast
next
  have 140: "ALL a b c. (thread_id_of a = thread_id_of b) -->
                        (thread_id_of b = thread_id_of c) --> (thread_id_of a = thread_id_of c)" by force
  hence 150: "ALL a b c. same_thread a b --> same_thread b c --> same_thread a c" by (unfold same_thread_def) blast
  hence 160: "ALL a b c. same_thread_rel (a, b) --> same_thread_rel (b, c) --> same_thread_rel (a, c)"
    by (unfold same_thread_rel_def) force
  hence 170: "ALL a b c. ((a, b) : same_thread_rel) --> ((b, c) : same_thread_rel) --> ((a, c) : same_thread_rel)"
    by (unfold mem_def) blast
  thus 180: "trans same_thread_rel" by (unfold trans_def) blast
qed


(* N3132 6.9 Well-formed reads-from mapping *)

definition well_formed_reads_from_mapping where
  "well_formed_reads_from_mapping ce ==
     (relation_over (actions_of ce) (reads_from_of ce) &
      (ALL a. ALL aa. ALL b. reads_from_of ce (a, b) & reads_from_of ce (aa, b) --> (a = aa)) &
      (ALL (a, b) : (reads_from_of ce).
         (same_location_rel (a, b) &
          (value_read b = value_written a) &
          (a ~= b) &
          (is_at_mutex_location ce a --> (is_unlock a & is_lock b)) &
          (is_at_non_atomic_location ce a --> (is_store a & is_load b)) &
          (is_at_atomic_location ce a -->
             ((is_atomic_store a | is_atomic_rmw a | is_store a)
              & (is_atomic_load b | is_atomic_rmw b | is_load b))))))"

(* `read_by', which is the converse of `reads_from', added by Cryolite *)
definition read_by_of where "read_by_of ce == converse (reads_from_of ce)"

lemma read_by_is_single_valued: "well_formed_reads_from_mapping ce --> single_valued (read_by_of ce)"
proof
  assume 10: "well_formed_reads_from_mapping ce"
  hence 20: "ALL a. ALL aa. ALL b. reads_from_of ce (a, b) & reads_from_of ce (aa, b) --> (a = aa)"
    by (unfold well_formed_reads_from_mapping_def) blast
  have 30: "((reads_from_of ce)^-1)^-1 = reads_from_of ce" by (rule converse_converse)
  with 20 have 40: "ALL a. ALL aa. ALL b.
                    (((reads_from_of ce)^-1)^-1) (a, b) & (((reads_from_of ce)^-1)^-1) (aa, b) --> (a = aa)"
    by (unfold 30) blast
  hence 60: "ALL a. ALL aa. ALL b.
             (((a, b) : (((reads_from_of ce)^-1)^-1)) & ((aa, b) : (((reads_from_of ce)^-1)^-1))) --> (a = aa)"
    by (unfold mem_def) blast
  hence 60: "ALL a. ALL aa. ALL b.
             (((b, a) : ((reads_from_of ce)^-1)) & ((b, aa) : ((reads_from_of ce)^-1))) --> (a = aa)"
    by blast
  hence 70: "ALL a. ALL aa. ALL b. (((b, a) : (read_by_of ce)) & ((b, aa) : (read_by_of ce))) --> (a = aa)"
    by (unfold read_by_of_def) blast
  hence 80: "ALL b. ALL a. ALL aa. (((b, a) : (read_by_of ce)) & ((b, aa) : (read_by_of ce))) --> (a = aa)" by blast
  hence 90: "ALL b. ALL a. ALL aa. ((b, a) : (read_by_of ce)) --> ((b, aa) : (read_by_of ce)) --> (a = aa)" by blast
  hence 100: "ALL b. ALL a. ((b, a) : (read_by_of ce)) --> (ALL aa. ((b, aa) : (read_by_of ce)) --> (a = aa))"
    by blast
  thus 110: "single_valued (read_by_of ce)" by (unfold single_valued_def) blast
qed


(* N3132 6.10 Consistent locks *)
definition all_lock_or_unlock_actions_at where
  "all_lock_or_unlock_actions_at lopt as ==
     {a : as. (is_lock_or_unlock a & (location_of a = lopt))}"

definition consistent_locks where
  "consistent_locks ce ==
     (ALL l : locations_of (actions_of ce). ((location_typing_of ce l = Mutex) --> (
        let lock_unlock_actions = all_lock_or_unlock_actions_at(Some l) (actions_of ce) in
        let lock_order = relation_int lock_unlock_actions (sequential_consistency_of ce) in
        strict_total_order_over lock_unlock_actions lock_order &
        (ALL au : lock_unlock_actions. (is_unlock au -->
           (EX al : lock_unlock_actions.
              (adjacent_less lock_order al au & same_thread_rel (al, au) & is_lock al)))) &
        (ALL al : lock_unlock_actions. (is_lock al -->
           (ALL au : lock_unlock_actions.
              (adjacent_less lock_order au al --> is_unlock au)))))))"


(* N3132 6.11 Release sequences *)
definition rs_element where
  "rs_element rs_head a == (same_thread_rel (a, rs_head) | is_atomic_rmw a)"

definition release_sequence where
  "release_sequence ce ==
     (%(arel, b).
      (is_at_atomic_location ce b &
       is_release arel & (
         (b = arel) |
         (rs_element arel b & modification_order_of ce (arel, b) &
            (ALL c. ((modification_order_of ce (arel, c) & modification_order_of ce (c, b)) -->
               rs_element arel c))))))"

definition hypothetical_release_sequence where
  "hypothetical_release_sequence ce ==
     (%(a, b).
      (is_at_atomic_location ce b & (
         (b = a) |
         (rs_element a b & modification_order_of ce (a, b) &
            (ALL c. ((modification_order_of ce (a, c) & modification_order_of ce (c, b)) --> rs_element a c))))))"


(* N3132 6.12 Synchronizes-with *)
definition synchronizes_with where
  "synchronizes_with ce ==
     (%(a, b).
      (additional_synchronized_with_of ce (a, b) |
       (same_location_rel (a, b) & (a : (actions_of ce)) & (b : (actions_of ce)) & (
          (is_unlock a & is_lock b & sequenced_before_of ce (a, b))                          |

          (is_release a & is_acquire b & ~(same_thread_rel (a, b)) &
             (EX c. release_sequence ce (a, c) & reads_from_of ce (c, b)))                  |

          (is_fence a & is_release a & is_fence b & is_acquire b &
             (EX x. EX y. same_location_rel (x, y) &
                is_atomic_action x & is_atomic_action y & is_write x &
                sequenced_before_of ce (a, x) & sequenced_before_of ce (y, b) &
                (EX z. hypothetical_release_sequence ce (x, z) & reads_from_of ce (z, y)))) |

          (is_fence a & is_release a & is_atomic_action b & is_acquire b &
             (EX x. same_location_rel (x, b) &
                is_atomic_action x & is_write x &
                sequenced_before_of ce (a, x) &
                (EX z. hypothetical_release_sequence ce (x, z) & reads_from_of ce (z, b)))) |

          (is_atomic_action a & is_release a & is_fence b & is_acquire b &
             (EX x. same_location_rel (a, x) & is_atomic_action x &
                sequenced_before_of ce (x, b) &
                (EX z. release_sequence ce (a, z) & reads_from_of ce (z, x))))))))"


(* N3132 6.13 Carries-a-dependency-to *)
definition carries_a_dependency_to where
  "carries_a_dependency_to ce ==
     (%(a, b).
      ((((reads_from_of ce) Int (sequenced_before_of ce)) Un (data_dependency_of ce))^*) (a, b))"


(* N3132 6.14 Dependency-ordered-before *)
definition dependency_ordered_before where
  "dependency_ordered_before ce ==
     (%(a, d).
      (a : (actions_of ce)) & (d : (actions_of ce)) &
        (EX b. (is_release a & is_consume b &
           (EX e. (release_sequence ce (a, e) & reads_from_of ce (e, b))) &
           (carries_a_dependency_to ce (b, d) | (b = d)))))"


(* N3132 6.15 Inter-thread-happens-before and happens-before *)
definition inter_thread_happens_before where
  "inter_thread_happens_before ce ==
     (%(a, b).
      let r = (synchronizes_with ce) Un
              (dependency_ordered_before ce) Un
              ((synchronizes_with ce) O (sequenced_before_of ce)) in
      ((r Un ((sequenced_before_of ce) O r))^*) (a, b))"

definition consistent_inter_thread_happens_before where
  "consistent_inter_thread_happens_before ce ==
     irrefl (inter_thread_happens_before ce)"

definition happens_before where
  "happens_before ce == (sequenced_before_of ce) O (inter_thread_happens_before ce)"


(* N3132 6.16 Consistent SC order *)
definition all_sc_actions where
  "all_sc_actions ce == {a : (actions_of ce). (is_seq_cst a | is_lock a | is_unlock a)}"

definition consistent_sc_order where
  "consistent_sc_order ce as lk sb asw dd rf sc mo ==
     strict_total_order_over (all_sc_actions ce) (sequential_consistency_of ce) &
     (relation_int (all_sc_actions as) (happens_before ce)) <= (sequential_consistency_of ce) &
     (relation_int (all_sc_actions ce) (modification_order_of ce)) <= (sequential_consistency_of ce)"


(* N3132 6.17 Consistent modification order *)
definition consistent_modification_order where
  "consistent_modification_order ce ==
     ((ALL a. ALL b. (modification_order_of ce (a, b) --> same_location_rel (a, b))) &
      (ALL l : locations_of (actions_of ce). case (location_typing_of ce) l of
         Atomic => (
           let as_at_l = {a. (location_of a = Some l)} in
           let writes_at_l = {a : as_at_l. (is_store a | is_atomic_store a | is_atomic_rmw a)} in
           (strict_total_order_over writes_at_l (relation_int as_at_l (modification_order_of ce))) &
           ((relation_int writes_at_l (happens_before ce)) <= (modification_order_of ce)) &
           (((sequenced_before_of ce) O (relation_int is_fence (sequential_consistency_of ce)) O
             (relation_int writes_at_l (sequenced_before_of ce))) <= (modification_order_of ce)))
       | _ => (
           let as_at_l = {a. (location_of a = Some l)} in
           ((relation_int as_at_l (modification_order_of ce)) = {}))))"


(* TODO *)
(* N3132 6.18 Visible side effects and visible sequences of side effects *)
definition visible_side_effect where
  "visible_side_effect ce ==
     (%(a, b).
      happens_before ce (a, b) &
      is_write a & is_read b & same_location_rel (a, b) &
      ~(EX c. (c ~= a) & (c~= b) &
          is_write c & same_location_rel (c, b) &
          happens_before ce (a, c) & happens_before ce (c, b)))"

definition visible_sequence_of_side_effects_tail where
  "visible_sequence_of_side_effects_tail ce vsse_head b ==
     {c. modification_order_of ce (vsse_head, c) &
        ~(happens_before ce (b, c)) &
        (ALL a. (modification_order_of ce (vsse_head, a) & modification_order_of ce (a, c))
           --> ~(happens_before ce (b, a)))}"

definition visible_sequences_of_side_effects where
  "visible_sequences_of_side_effects ce b ==
     setsum
       (%vsse_head. if (is_at_atomic_location ce b) then
                       ({vsse_head} Un
                          visible_sequence_of_side_effects_tail ce vsse_head b)
                    else {})
       {vsse_head : (actions_of ce). visible_side_effect ce (vssed_head, b)}"


(* N3132 6.19 Consistent reads-from mapping *)
definition consistent_reads_from_mapping where
  "consistent_reads_from_mapping ce ==
     ((ALL b. (is_read b & is_at_non_atomic_location ce b) -->
              (if (EX avse. visible_side_effect ce (avse, b))
               then (EX avse. visible_side_effect ce (avse, b) & reads_from_of ce (avse, b))
               else ~(EX a. reads_from_of ce (a, b)))) &

      (ALL b. (is_read b & is_at_atomic_location ce b) -->
              (if (EX (bb, vsse) : (visible_sequences_of_side_effects ce). (bb = b))
               then (EX (bb, vsse) : (visible_sequences_of_side_effects ce).
                     (bb = b) & (EX c : vsse. reads_from_of ce (c, b)))
               else ~(EX a. reads_from_of ce (a, b))))   )"(* &

      (ALL (x, a) : (reads_from_of ce).
         ALL (y, b) : (reads_from_of ce).
           (happens_before ce (a, b) &
              same_location_rel (a, b) & is_at_atomic_location ce b)
                --> ((x = y) | modification_order_of ce (x, y))) &

      (ALL (a, b) : (happens_before ce).
         ALL c.
           (reads_from_of ce (c, b) &
              is_write a & same_location_rel (a, b) & is_at_atomic_location ce b)
                --> ((c = a) | modification_order_of ce (a, c))) &

      (ALL (a, b) : (happens_before ce).
         ALL c.
           (reads_from_of ce (c, a) &
              is_write b & same_location_rel (a, b) & is_at_atomic_location ce a)
                --> modification_order_of ce (c, b)) &

      (ALL (a, b) : (reads_from_of ce). is_atomic_rmw b
         --> modification_order_of (a, b)) &

      (ALL (a, b) : (reads_from_of ce). is_seq_cst b
         --> (~(is_seq_cst a))
             | (relation_int (%c. is_write c & same_location_rel (b, c)) sequential_consistency_of ce (a, b)))   )"
*)
