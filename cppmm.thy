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

definition actions_respect_location_kinds where
  "actions_respect_location_kinds actions location_kind_of ==
     (ALL a : actions.
        (case location_of a of
           Some l =>
             (case location_kind_of l of
                Mutex => is_lock_or_unlock a
              | Non_atomic => is_load_or_store a
              | Atomic => (is_load_or_store a | is_atomic_action a))
         | None => True))"

definition is_at_location_kind where
  "is_at_location_kind a (lk0::location_kind) location_kind_of ==
     (case location_of a of
        Some l => (location_kind_of l = lk0)
      | None => False)"

definition is_at_mutex_location where
  "is_at_mutex_location a location_kind_of == is_at_location_kind a Mutex location_kind_of"

definition is_at_non_atomic_location where
  "is_at_non_atomic_location a location_kind_of == is_at_location_kind a Non_atomic location_kind_of"

definition is_at_atomic_location where
  "is_at_atomic_location a location_kind_of == is_at_location_kind a Atomic location_kind_of"


(* N3132 6.8 Well-formed threads *)
definition same_thread where
  "same_thread a b == (thread_id_of a = thread_id_of b)"

definition threadwise_relation_over where
  "threadwise_relation_over s rel == (relation_over s rel & (ALL (a, b) : rel. (same_thread a b)))"

definition same_location where
  "same_location a b == (location_of a = location_of b)"

definition locations_of where
  "locations_of actions == {l. (EX a : actions. (location_of a = Some l))}"

definition well_formed_action where
  "well_formed_action a ==
     (case a of
        (Atomic_load _ _ mem_ord _ _) => (mem_ord : {Mo_relaxed, Mo_acquire, Mo_seq_cst, Mo_consume})
      | (Atomic_store _ _ mem_ord _ _) => (mem_ord : {Mo_relaxed, Mo_release, Mo_seq_cst})
      | (Atomic_rmw _ _ mem_ord _ _ _) => (mem_ord : {Mo_relaxed, Mo_release, Mo_acquire, Mo_acq_rel, Mo_seq_cst, Mo_consume})
      | _ => True)"

definition well_formed_threads where
  "well_formed_threads threads actions location_kind_of sb asw dd cd ==
     (inj_on action_id_of actions &
      (ALL a : actions. well_formed_action a) &
      threadwise_relation_over actions sb &
      threadwise_relation_over actions dd &
      threadwise_relation_over actions cd &
      strict_preorder sb &
      strict_preorder dd &
      strict_preorder cd &
      relation_over actions asw &
      (ALL a : actions. (thread_id_of a : threads)) &
      actions_respect_location_kinds actions location_kind_of &
      dd <= sb)"


(* N3132 6.9 Well-formed reads-from mapping *)
definition well_formed_reads_from_mapping where
  "well_formed_reads_from_mapping actions location_kind_of rf ==
     (relation_over actions rf &
      (ALL a : actions. (ALL aa : actions. (ALL b : actions. ((rf (a, b) & rf (aa, b)) --> (a = aa))))) &
      (ALL (a, b) : rf.
         (same_location a b &
          (value_read b = value_written a) &
          (a ~= b) &
          (is_at_mutex_location a location_kind_of --> (is_unlock a & is_lock b)) &
          (is_at_non_atomic_location a location_kind_of --> (is_store a & is_load b)) &
          (is_at_atomic_location a location_kind_of -->
             ((is_atomic_store a | is_atomic_rmw a | is_store a)
              & (is_atomic_load b | is_atomic_rmw b | is_load b))))))"


(* N3132 6.10 Consistent locks *)
definition all_lock_or_unlock_actions_at where
  "all_lock_or_unlock_actions_at lopt as ==
     {a : as. (is_lock_or_unlock a & (location_of a = lopt))}"

definition consistent_locks where
  "consistent_locks actions location_kind_of sc ==
     (ALL l : locations_of actions. ((location_kind_of l = Mutex) --> (
        let lock_unlock_actions = all_lock_or_unlock_actions_at(Some l) actions in
        let lock_order = relation_int lock_unlock_actions sc in
        strict_total_order_over lock_unlock_actions lock_order &
        (ALL au : lock_unlock_actions. (is_unlock au -->
           (EX al : lock_unlock_actions.
              (adjacent_less lock_order al au & same_thread al au & is_lock al)))) &
        (ALL al : lock_unlock_actions. (is_lock al -->
           (ALL au : lock_unlock_actions.
              (adjacent_less lock_order au al --> is_unlock au)))))))"


(* N3132 6.11 Release sequences *)
definition rs_element where
  "rs_element rs_head a == (same_thread a rs_head | is_atomic_rmw a)"

definition release_sequence where
  "release_sequence ap location_kind_of mo ==
     let (arel, b) = ap in
     (is_at_atomic_location b location_kind_of &
      is_release arel & (
        (b = arel) |
        (rs_element arel b & mo (arel, b) &
           (ALL c. ((mo (arel, c) & mo (c, b)) -->
              rs_element arel c)))))"

definition hypothetical_release_sequence where
  "hypothetical_release_sequence ap location_kind_of mo ==
     let (a, b) = ap in
     (is_at_atomic_location b location_kind_of & (
        (b = a) |
        (rs_element a b & mo (a, b) &
           (ALL c. ((mo (a, c) & mo (c, b)) --> rs_element a c)))))"


(* N3132 6.12 Synchronizes-with *)
definition synchronizes_with where
  "synchronizes_with ap actions location_kind_of sb asw rf sc mo ==
     let (a, b) = ap in
     (asw (a, b) |
      (same_location a b & (a : actions) & (b : actions) & (
         (is_unlock a & is_lock b & sc (a, b))                                                |

         (is_release a & is_acquire b & ~(same_thread a b) &
            (EX c. release_sequence (a, c) location_kind_of mo & rf (c, b)))                  |

         (is_fence a & is_release a & is_fence b & is_acquire b &
            (EX x. EX y. same_location x y &
               is_atomic_action x & is_atomic_action y & is_write x &
               sb (a, x) & sb (y, b) &
               (EX z. hypothetical_release_sequence (x, z) location_kind_of mo & rf (z, y)))) |

         (is_fence a & is_release a & is_atomic_action b & is_acquire b &
            (EX x. same_location x b &
               is_atomic_action x & is_write x &
               sb (a, x) &
               (EX z. hypothetical_release_sequence (x, z) location_kind_of mo & rf (z, b)))) |

         (is_atomic_action a & is_release a & is_fence b & is_acquire b &
            (EX x. same_location a x & is_atomic_action x &
               sb (x, b) &
               (EX z. release_sequence (a, z) location_kind_of mo & rf (z, x)))))))"


(* N3132 6.13 Carries-a-dependency-to *)
definition carries_a_dependency_to where
  "carries_a_dependency_to ap sb dd rf ==
     let ((a::action), b) = ap in
     (((rf Int sb) Un dd)^*) (a, b)"


(* N3132 6.14 Dependency-ordered-before *)
definition dependency_ordered_before where
  "dependency_ordered_before ap actions location_kind_of sb dd rf mo ==
     let (a, d) = ap in
     ((a : actions) & (d : actions) &
       (EX b. (is_release a & is_consume b &
          (EX e. (release_sequence (a, e) location_kind_of mo & rf (e, b))) &
          (carries_a_dependency_to (b, d) sb dd rf | (b = d)))))"


(* N3132 6.15 Inter-thread-happens-before and happens-before *)
definition inter_thread_happens_before where
  "inter_thread_happens_before ap as lk sb asw dd rf sc mo ==
     let (a, b) = ap in
     let sw = (%app. synchronizes_with app as lk sb asw rf sc mo) in
     let dob = (%app. dependency_ordered_before app as lk sb dd rf mo) in
     let r = sw Un dob Un (sw O sb) in
     ((r Un (sb O r))^*) (a, b)"

definition consistent_inter_thread_happens_before where
  "consistent_inter_thread_happens_before as lk sb asw dd rf sc mo ==
     let ithb = (%ap. inter_thread_happens_before ap as lk sb asw dd rf sc mo) in
     irrefl ithb"

definition happens_before where
  "happens_before ap as lk sb asw dd rf sc mo ==
     let ithb = (%app. inter_thread_happens_before ap as lk sb asw dd rf sc mo) in
     (sb O ithb) ap"


(* N3132 6.16 Consistent SC order *)
definition all_sc_actions where
  "all_sc_actions as == {a : as. (is_seq_cst a | is_lock a | is_unlock a)}"

definition consistent_sc_order where
  "consistent_sc_order as lk sb asw dd rf sc mo ==
     let hb = (%ap. happens_before ap as lk sb asw dd rf sc mo) in
     let sc_happens_before = (relation_int (all_sc_actions as) hb) in
     let sc_mod_order = relation_int (all_sc_actions as) mo in
     strict_total_order_over (all_sc_actions as) sc &
     sc_happens_before <= sc &
     sc_mod_order <= sc"


(* N3132 6.17 Consistent modification order *)
definition consistent_modification_order where
  "consistent_modification_order as lk sb asw dd rf sc mo ==
     let hb = (%ap. happens_before ap as lk sb asw dd rf sc mo) in
     ((ALL a : as. ALL b : as. (mo (a, b) --> same_location a b)) &
      (ALL l : locations_of as. case lk l of
         Atomic => (
           let as_at_l = {a. (location_of a = Some l)} in
           let writes_at_l = {a : as_at_l. (is_store a | is_atomic_store a | is_atomic_rmw a)} in
           (strict_total_order_over writes_at_l (relation_int as_at_l mo)) &
           ((relation_int writes_at_l hb) <= mo) &
           ((sb O (relation_int is_fence sc) O (relation_int writes_at_l sb)) <= mo))
       | _ => (
           let as_at_l = {a. (location_of a = Some l)} in
           ((relation_int as_at_l mo) = {}))))"


(* TODO *)
(* N3132 6.18 Visible side effects and visible sequences of side effects *)
definition visible_side_effect where
  "visible_side_effect ap as lk sb asw dd rf sc mo ==
     let (a, b) = ap in
     let hb = (%app. happens_before app as lk sb asw dd rf sc mo) in
     (hb (a, b) &
      is_write a & is_read b & same_location a b &
      ~(EX c : as. (c ~= a) & (c~= b) &
          is_write c & same_location c b &
          hb (a, c) & hb (c, b)))"

definition visible_sequence_of_side_effects_tail where
  "visible_sequence_of_side_effects_tail vsse_head b as lk sb asw dd rf sc mo ==
     let hb = (%ap. happens_before ap as lk sb asw dd rf sc mo) in
     {c : as. mo (vsse_head, c) &
        ~(hb (b, c)) &
        (ALL a : as. (mo (vsse_head, a) & mo (a, c)) --> ~(hb (b, a)))}"

definition visible_sequences_of_side_effects where
  "visible_sequences_of_side_effects ==
     (%(vsse_head, b). %as. %lk. %sb. %asw. %dd. %rf. %sc. %mo.
        (b, if (is_at_atomic_location b lk) then
              ({vsse_head} Un
               visible_sequence_of_side_effects_tail vsse_head b as lk sb asw dd rf sc mo)
            else {}))"


(* N3132 6.19 Consistent reads-from mapping *)
definition consistent_reads_from_mapping where
  "consistent_reads_from_mapping as lk sb asw dd rf sc mo ==
     let hb = (%ap. happens_before ap as lk sb asw dd rf sc mo) in
     let vse = (%ap. visible_side_effect ap as lk sb asw dd rf sc mo) in
     let vsose = (%(vsse_head, b). visible_sequences_of_side_effects (vsse_head, b) as lk sb asw dd rf sc mo) in
     ((ALL b : as. (is_read b & is_at_non_atomic_location b lk) -->
                   (if (EX avse. vse (avse, b))
                    then (EX avse. vse (avse, b) & rf (avse, b))
                    else ~(EX a. rf (a, b)))) &

      (ALL b : as. (is_read b & is_at_atomic_location b lk) -->
                   (if (EX (bb, vsse) : vsose. (bb = b))
                    then (EX (bb, vsse) : vsose.
                          (bb = b) & (EX c : vsse. rf (c, b)))
                    else ~(EX a. rf (a, b))))   )"(* &

      (ALL (x, a) : rf.
         ALL (y, b) : rf.
           (hb (a, b) &
              same_location a b & is_at_atomic_location b lk)
                --> ((x = y) | mo (x, y))) &

      (ALL (a, b) : hb.
         ALL c.
           (rf (c, b) &
              is_write a & same_location a b & is_at_atomic_location b lk)
                --> ((c = a) | mo (a, c))) &

      (ALL (a, b) : hb.
         ALL c.
           (rf (c, a) &
              is_write b & same_location a b & is_at_atomic_location a lk)
                --> mo (c, b)) &

      (ALL (a, b) : rf. is_atomic_rmw b
         --> mo (a, b)) &

      (ALL (a, b) : rf. is_seq_cst b
         --> (~(is_seq_cst a)) | (relation_int (%c. is_write c & same_location b c) sc (a, b)))   )"
*)
