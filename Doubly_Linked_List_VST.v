(** You should verify a doubly linked list library using VST. You may use
    programs that we provided, or write those programs-to-verify by yourself.
    This library should include the following functions and two extra
    applications:

    struct node;
    struct list;
    struct list *list_new();
    void list_free(struct list *l);
    struct node *begin(struct list *l);
    struct node *end(struct list *l);
    struct node *rbegin(struct list *l);
    struct node *rend(struct list *l);
    struct node *next(struct node *p);
    struct node *rnext(struct node *p);
    unsigned int get_val(struct node *p);
    
    void insert_before(struct list *l, struct node *p, unsigned int v);
    void insert_after(struct list *l, struct node *p, unsigned int v);
    void merge(struct list *l1, struct list *l2);

    You may change the definition below if your version is better. *)

Require Import VST.floyd.proofauto.
Require Import EV.dlinklist.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_node : type := Tstruct _node noattr.
Definition t_struct_list : type := Tstruct _list noattr.

(** Concrete memory representation of a dlinklist, which does not only include
    value but also include addresses. *)

Fixpoint dlrep (l : list (Z * val)) (head tail prev next : val) : mpred :=
  match l with
  | (x, p) :: l' =>
      EX head' : val,
        !! (p = head) &&
        data_at Tsh t_struct_node (Vint (Int.repr x), (prev, head')) head *
        dlrep l' head' tail head next
  | nil => !! (tail = prev /\ head = next) && emp
  end.

(* Some basic properties about dlrep. *)

Lemma dlrep_singleton:
  forall x y head tail prev next,
    dlrep [(x, y)] head tail prev next |--
    !! (head = tail /\ head = y) &&
    data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next)) y.
Proof.
  intros.
  unfold dlrep.
  Intros head'.
  entailer!.
Qed.

Lemma singleton_dlrep:
  forall x y head tail prev next,
    !! (head = tail /\ head = y) &&
    data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next)) y |--
    dlrep [(x, y)] head tail prev next.
Proof.
  intros.
  unfold dlrep.
  Exists next.
  entailer!.
Qed.

Lemma dlrep_left_elem:
  forall l x p head tail prev next,
    dlrep ((x, p) :: l) head tail prev next |-- 
    EX next',
      !!(p = head) && emp * 
      dlrep l next' tail p next *
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next')) p.
Proof.
  intros.
  destruct l.
  + sep_apply dlrep_singleton.
    unfold dlrep; fold dlrep.
    Exists next.
    entailer!.
  + unfold dlrep; fold dlrep.
    Intros head'.
    Exists head'.
    entailer!.
Qed.

Lemma elem_left_dlrep:
  forall l x p head tail prev next next',
    !! (p = head) && emp * 
    dlrep l next' tail p next *
    data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next')) p |--
    dlrep ((x, p) :: l) head tail prev next.
Proof.
  intros.
  entailer!.
  destruct l.
  + unfold dlrep; fold dlrep.
    Exists next.
    entailer!.
  + unfold dlrep; fold dlrep.
    destruct p.
    Intros head'.
    Exists next'.
    Exists head'.
    entailer!.
Qed.

Lemma dlrep_right_elem:
  forall l x p head tail (prev: val) next,
    dlrep (l ++ [(x, p)]) head tail prev next |-- 
    EX p',
      !!(p = tail) && emp * 
      dlrep l head p' prev p *
      data_at Tsh t_struct_node (Vint (Int.repr x), (p', next)) p.
Proof.
  intros.
  revert head tail prev next.
  induction l; intros.
  + autorewrite with sublist.
    sep_apply dlrep_singleton.
    Exists prev.
    unfold dlrep; fold dlrep.
    entailer!.
  + unfold dlrep; fold dlrep.
    destruct a.
    simpl.
    Intros head'.
    specialize (IHl head' tail head next).
    sep_apply IHl.
    Intros p'.
    Exists p' head'.
    entailer!.
Qed.

Lemma elem_right_dlrep:
  forall l x p head tail prev next prev',
    !! (p = tail) && emp * 
      dlrep l head prev' prev p *
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next)) p
    |-- dlrep (l ++ [(x, p)]) head tail prev next.
Proof.
  intros.
  revert head tail prev next prev'.
  induction l; intros.
  + simpl.
    Exists next.
    entailer!.
  + unfold dlrep; fold dlrep.
    destruct a.
    Intros head'.
    specialize (IHl head' tail head next prev').

    assert_PROP (dlrep l head' prev' head p *
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next)) p |--
      !! (p = tail) && emp * dlrep l head' prev' head p *
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next)) p).
    { entailer!. }

    sep_apply H1.
    sep_apply IHl.
    { exact H. }

    simpl.
    Exists head'.
    entailer!.
Qed.

Lemma dlrep_middle_elem:
  forall l1 x p l2 head tail prev next, 
    dlrep (l1 ++ (x, p) :: l2) head tail prev next |-- EX prev' next',
      dlrep l1 head prev' prev p * 
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next')) p *
      dlrep l2 next' tail p next.
Proof.
  intros.
  revert head tail prev next.
  induction l1, l2; intros; autorewrite with sublist; unfold dlrep; fold dlrep.
  + Intros next'.
    Exists prev next.
    entailer!.
  + Intros next'.
    Exists prev next'.
    entailer!.
  + assert ((a :: l1) ++ [(x, p)] = a :: (l1 ++ [(x, p)])).
    list_solve.
    rewrite H.
    pose proof dlrep_left_elem.
    destruct a.
    specialize (H0 (l1 ++ [(x, p)]) z v head tail prev next).
    sep_apply H0.
    Intros next'.
    specialize (IHl1 next' tail v next).
    sep_apply IHl1.
    Intros prev' next'0.
    Exists prev' next'0.
    Exists next'.
    unfold dlrep; fold dlrep.
    entailer!.
  + pose proof dlrep_left_elem.
    destruct a.
    assert (((z, v) :: l1) ++ (x, p) :: p0 :: l2 = (z, v) :: l1 ++ (x, p) :: p0 :: l2).
    list_solve.
    rewrite H0; clear H0.
    specialize (H (l1 ++ (x, p) :: p0 :: l2) z v head tail prev next).
    sep_apply H.
    Intros next'.
    specialize (IHl1 next' tail v next).
    sep_apply IHl1.
    Intros prev' next'0.
    Exists prev' next'0.
    Exists next'.
    destruct p0.
    pose proof dlrep_left_elem.
    specialize (H1 l2 z0 v0 next'0 tail p next).
    sep_apply H1.
    Intros next'1.
    Exists next'1.
    entailer!.
Qed.

Lemma elem_middle_dlrep:
  forall l1 l2 x p head tail prev next prev' next',
    dlrep l1 head prev' prev p * 
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next')) p *
      dlrep l2 next' tail p next
    |-- dlrep (l1 ++ (x, p) :: l2) head tail prev next.
Proof.
  intros.
  revert head tail prev next prev' next' p x.
  induction l1, l2; intros; autorewrite with sublist; unfold dlrep; fold dlrep.
  + Exists next'.
    entailer!.
  + destruct p.
    Intros head'.
    Exists next' head'.
    entailer!.
  + assert ((a :: l1) ++ [(x, p)] = a :: (l1 ++ [(x, p)])).
    list_solve.
    rewrite H.
    destruct a.
    pose proof elem_left_dlrep.
    specialize (H0 (l1 ++ [(x, p)]) z v head tail prev next).
    Intros head'.
    specialize (H0 head').
    assert_PROP (data_at Tsh t_struct_node (Vint (Int.repr z), (prev, head')) head *
      dlrep l1 head' prev' head p *
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next')) p * emp |--
      !! (v = head) && emp * dlrep (l1 ++ [(x, p)]) head' tail v next *
      data_at Tsh t_struct_node (Vint (Int.repr z), (prev, head')) v).
    - entailer!.
      cancel.
      specialize (IHl1 head' p head next prev' next p x).
      assert_PROP (dlrep l1 head' prev' head p *
        data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next)) p |--
        dlrep l1 head' prev' head p *
        data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next)) p *
        dlrep [] next p p next).
      * unfold dlrep; fold dlrep.
        entailer!.
        entailer!. 
      * sep_apply H1.
        sep_apply IHl1.
        entailer!.
    - sep_apply H4.
      sep_apply H0.
      exact H3.
      entailer!.
  + destruct a, p.
    assert (((z, v) :: l1) ++ (x, p0) :: (z0, v0) :: l2 = (z, v) :: l1 ++ (x, p0) :: (z0, v0) :: l2).
    list_solve.
    rewrite H; clear H.
    pose proof elem_left_dlrep.
    Intros l1_head l2_head.
    specialize (H (l1 ++ (x, p0) :: (z0, v0) :: l2) z v head tail prev next l1_head).
    assert_PROP (data_at Tsh t_struct_node (Vint (Int.repr z), (prev, l1_head)) head *
      dlrep l1 l1_head prev' head p0 *
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev', next')) p0 *
      (data_at Tsh t_struct_node (Vint (Int.repr z0), (p0, l2_head)) next' *
        dlrep l2 l2_head tail next' next) |--
      !! (v = head) && emp *
      dlrep (l1 ++ (x, p0) :: (z0, v0) :: l2) l1_head tail v next *
      data_at Tsh t_struct_node (Vint (Int.repr z), (prev, l1_head)) v).
    - entailer!.
      pose proof elem_left_dlrep.
      specialize (H0 l2 z0 next' next' tail p0 next l2_head).
      assert_PROP (data_at Tsh t_struct_node (Vint (Int.repr z0), (p0, l2_head)) next' *
        dlrep l2 l2_head tail next' next |--
        !! (next' = next') && emp * dlrep l2 l2_head tail next' next *
        data_at Tsh t_struct_node (Vint (Int.repr z0), (p0, l2_head)) next').
      * entailer!.
        entailer!.
      * sep_apply H1.
        sep_apply H0.
        { reflexivity. }

        entailer!.
        specialize (IHl1 l1_head tail head next prev' next' p0 x).
        sep_apply IHl1.
        entailer!.
    - sep_apply H2.
      sep_apply H.
      { exact H0. }
      entailer!.
Qed.

Lemma dlrep_local_facts_head:
  forall l head tail,
    dlrep l head tail nullval nullval |--
    !! (is_pointer_or_null head) && emp * dlrep l head tail nullval nullval.
Proof.
  intros.
  destruct l.
  + unfold dlrep.
    entailer!.
  + unfold dlrep; fold dlrep.
    destruct p. 
    Intros head'.
    Exists head'.
    entailer!.
Qed.

Lemma dlrep_local_facts_head_empty:
  forall head tail prev, 
    dlrep [] head tail prev nullval |--
    !! (is_pointer_or_null head) && emp * dlrep [] head tail prev nullval.
Proof. 
  intros. 
  unfold dlrep. 
  entailer!. 
Qed.

Lemma dlrep_local_facts_head_not_empty (l: list (Z * val)):
  forall head tail prev next, 
    (l <> @nil (Z*val))->
      dlrep l head tail prev next |--
      !! (is_pointer_or_null head) && emp * dlrep l head tail prev next.
Proof.
  intros.
  destruct l.
  + contradiction.
  + unfold dlrep; fold dlrep.
    destruct p.
    Intros head'; Exists head'.
    entailer!.
Qed.  

Lemma dlrep_local_facts_head_not_empty2 (l: list (Z * val)):
  forall head tail prev next, 
    (@nil (Z*val) <> l)->
      dlrep l head tail prev next |--
      !! (is_pointer_or_null head) && emp * dlrep l head tail prev next.
Proof.
  intros.
  destruct l.
  + contradiction.
  + unfold dlrep; fold dlrep.
    destruct p.
    Intros head'; Exists head'.
    entailer!.
Qed.  

Lemma dlrep_local_facts_tail_empty:
  forall head tail,
    dlrep (@nil (Z*val)) head tail nullval nullval |--
    !! (is_pointer_or_null tail ) && emp * dlrep (@nil (Z*val)) head tail nullval nullval.
Proof.
  unfold dlrep.
  { entailer!. }
Qed.

Require Import PL.Imp.
  
Lemma dlrep_local_facts_tail_not_empty (l: list (Z * val)):
forall head tail prev next, 
  l <> (@nil (Z*val)) ->
    dlrep l head tail prev next |--
    !! (is_pointer_or_null tail) && emp * dlrep l head tail prev next.
Proof.
  intros.
  revert head tail prev next.
  induction l.
  + contradiction.
  + destruct a.
    unfold dlrep; fold dlrep.
    intros.
    Intros head'.
    Exists head'.
    pose proof classic (l <> []).
    destruct H1.
    - 
      assert (forall head tail prev next : val,
        dlrep l head tail prev next
        |-- !! is_pointer_or_null tail && emp * dlrep l head tail prev next).
      tauto.
      specialize (H2 head' tail head next).
      sep_apply H2.
      entailer. entailer!.
    - assert (l = []).
      tauto.
      rewrite H2.
      unfold dlrep. 
      entailer!.
Qed.

(** Memory representation of a mathematical list. Cursors mean places to
    insert. *)
Definition list_rep_with_cursor (l : list (Z * val)) (p : val) : mpred :=
  EX (head tail : val),
    data_at Tsh t_struct_list (head, tail) p *
      dlrep l head tail nullval nullval.

Definition list_rep (l : list Z) (p : val) : mpred :=
  EX l0: list (Z * val),
    !! (map fst l0 = l) && list_rep_with_cursor l0 p.

(** Head pointer and tail pointer *)
Definition head_with_default {A: Type} (l: list A) (default: A): A :=
  match l with
  | a :: _ => a
  | nil => default
  end.

Definition head_ptr (l : list (Z * val)): val :=
  head_with_default (map snd l) nullval.
  
Definition tail_ptr (l : list (Z * val)): val :=
  head_with_default (rev (map snd l)) nullval.

Lemma tail_ptr_push_front (z: Z) (v: val) (l: list (Z*val)):
  l <> (@nil (Z*val))-> 
    tail_ptr((z, v)::l) = tail_ptr l.
Proof.
  revert z v.
  induction l; intros.
  (* TODO: Prove this useful and correct lemma. *)
Admitted.

Lemma dlrep_head_ptr:
  forall l head tail,
    dlrep l head tail nullval nullval |--
    !!(head_ptr l = head) && emp * dlrep l head tail nullval nullval.
Proof.
  intros.
  destruct l.
  unfold dlrep.
  unfold head_ptr, head_with_default, map.
  entailer!.
  unfold dlrep; fold dlrep.
  destruct p.
  Intros head'.
  Exists head'.
  unfold head_ptr.
  unfold head_with_default, map, snd.
  entailer!.
Qed.

Lemma dlrep_head_ptr_not_empty:
  forall l head tail prev next,
    l <> (@nil (Z*val)) ->
      dlrep l head tail prev next |--
        !! (head_ptr l = head) && emp * dlrep l head tail prev next.
Proof.
  intros.
  destruct l.
  unfold dlrep, head_with_default, map. entailer!.
  unfold dlrep; fold dlrep.
  destruct p.
  Intros head'; Exists head'.
  unfold head_ptr, head_with_default, map, snd.
  entailer!.
Qed.

Lemma dlrep_tail_ptr_empty:
  forall head tail next,
    dlrep [] head tail nullval next |--
    !!(tail_ptr [] = tail) && emp * dlrep [] head tail nullval next.
Proof.
  intros.
  unfold dlrep.
  entailer!.
Qed.

Lemma dlrep_tail_ptr_not_empty:
  forall l head tail prev next,
    l <> (@nil (Z*val)) -> 
    dlrep l head tail prev next |--
      !!(tail_ptr l = tail) && emp * dlrep l head tail prev next.
Proof.
  intros.
  revert head tail prev next.
  induction l; intros.
  + contradiction.
  + pose proof classic (l <> []).
    destruct a.
    destruct H0.
    - assert (forall head tail prev next : val,
          dlrep l head tail prev next
          |-- !! (tail_ptr l = tail) && emp * dlrep l head tail prev next).
      tauto.
      unfold dlrep; fold dlrep.
      Intros head'; Exists head'.
      specialize (H1 head' tail head next).
      sep_apply H1.
      entailer!.
      eapply tail_ptr_push_front.
      exact H0.
    - assert (l = []).
      tauto.
      rewrite (H1).
      unfold dlrep.
      Intros head'; Exists head'.
      unfold tail_ptr, head_with_default, rev, map, snd.
      assert ([] ++ [v] = [v]).
      list_solve.
      rewrite H5.
      entailer!.
Qed.

(** Specifications about memory operations *)

(* mallocN *)
Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [tint]
    PROP (4 <= n <= Int.max_unsigned)
    PARAMS (Vint (Int.repr n))
    GLOBALS ()
    SEP ()
  POST [ tptr tvoid ]
    EX v: val,
      PROP (malloc_compatible n v)
      RETURN (v)
      SEP (memory_block Tsh n v).

(* freeN *)
Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ tptr tvoid , tint ]
    PROP()
    PARAMS (p; Vint (Int.repr n))
    GLOBALS ()
    SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () RETURN () SEP ().

(** Functions to be verified. *)

(* list_new *)
Definition list_new_spec :=
 DECLARE _list_new
  WITH u : unit
  PRE  [  ]
       PROP() PARAMS () GLOBALS () SEP ()
  POST [ tptr t_struct_list ]
    EX v: val,
      PROP ()
      RETURN (v)
      SEP (list_rep nil v).

Definition Gprog_list_new : funspecs :=
            ltac:(with_library prog [list_new_spec; mallocN_spec]).

Check memory_block_zero.
Check memory_block_isptr.
Check memory_block_split.
Check memory_block_data_at_.

Theorem body_list_new: semax_body Vprog Gprog_list_new
                         f_list_new list_new_spec.
Proof.
  start_function.
  
  forward_call ((sizeof (Tstruct _list noattr))%expr).
  {
    simpl.
    rep_lia.
  }

  Intros vert.
  pose proof memory_block_data_at_ Tsh (Tstruct _list noattr) vert.
  pose proof malloc_compatible_field_compatible. 
  assert_PROP (complete_legal_cosu_type (Tstruct _list noattr) = true).
  { entailer!. }

  assert_PROP (natural_aligned natural_alignment (Tstruct _list noattr) = true).
  { entailer!. }

  specialize (H1 _ (Tstruct _list noattr) vert).
  assert (field_compatible (Tstruct _list noattr) [] vert).
  { tauto. }

  assert (memory_block Tsh (sizeof (Tstruct _list noattr)) vert =
      data_at_ Tsh (Tstruct _list noattr) vert).
  { tauto. }

  rewrite H5.
  forward.
  forward.
  forward.
  Exists vert.
  entailer!.

  unfold list_rep.
  Exists (@nil (Z * val)).
  entailer!.
  unfold list_rep_with_cursor.
  Exists nullval nullval.
  unfold dlrep.
  entailer!.
Qed.

(* list_free *)
Definition list_free_spec :=
 DECLARE _list_free
  WITH p : val, l : list Z
  PRE  [ tptr t_struct_list ]
    PROP () 
    PARAMS (p) 
    SEP (list_rep l p)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP ().

Definition Gprog_list_free : funspecs :=
            ltac:(with_library prog [list_free_spec; freeN_spec]).

Theorem body_list_free: semax_body Vprog Gprog_list_new
                          f_list_free list_free_spec.
Proof.
  start_function.

  unfold list_rep, list_rep_with_cursor.
  Intros l0 head tail.
  forward.
  sep_apply dlrep_local_facts_head.
  entailer!.
  (* TODO: Find the loop invariant. *)
Admitted.

(* begin *)
Definition begin_spec :=
 DECLARE _begin
  WITH p : val, l : list (Z * val)
  PRE  [ tptr t_struct_list ]
    PROP () 
    PARAMS (p)
    GLOBALS ()
    SEP (list_rep_with_cursor l p)
  POST [ tptr t_struct_node ]
    PROP ()
    RETURN (head_ptr l)
    SEP (list_rep_with_cursor l p).

Definition Gprog_begin : funspecs :=
            ltac:(with_library prog [begin_spec]).

Theorem body_begin: semax_body Vprog Gprog_begin
                      f_begin begin_spec.
Proof.
  start_function.
  unfold list_rep_with_cursor.
  Intros head tail.
  forward.
  sep_apply dlrep_local_facts_head.
  entailer!.
  forward.
  unfold list_rep_with_cursor.
  sep_apply dlrep_head_ptr.
  Exists head tail.
  entailer!.
Qed.

(* end *)
Definition end_spec :=
 DECLARE _end
  WITH p : val, l : list (Z * val)
  PRE  [ tptr t_struct_list ]
    PROP () 
    PARAMS (p) 
    GLOBALS ()
    SEP (list_rep_with_cursor l p)
  POST [ tptr t_struct_node ]
    PROP ()
    RETURN (nullval)
    SEP (list_rep_with_cursor l p).

Definition Gprog_end : funspecs :=
            ltac:(with_library prog [end_spec]).

Theorem body_end: semax_body Vprog Gprog_end
                    f_end end_spec.
Proof.
  start_function.
  unfold list_rep_with_cursor.
  Intros head tail.
  forward.
  unfold list_rep_with_cursor.
  Exists head tail.
  entailer!.
Qed.

(* rbegin *)
Definition rbegin_spec :=
 DECLARE _rbegin
  WITH p : val, l : list (Z * val)
  PRE  [ tptr t_struct_list ]
    PROP () 
    PARAMS (p) 
    GLOBALS ()
    SEP (list_rep_with_cursor l p)
  POST [ tptr t_struct_node ]
    PROP ()
    RETURN (tail_ptr l)
    SEP (list_rep_with_cursor l p).

Definition Gprog_rbegin : funspecs :=
            ltac:(with_library prog [rbegin_spec]).

Theorem body_rbegin: semax_body Vprog Gprog_rbegin
                       f_rbegin rbegin_spec.
Proof.
  start_function.
  unfold list_rep_with_cursor.
  Intros head tail.
  forward.
  pose proof classic (l <> []).
  destruct H.
  + sep_apply dlrep_local_facts_tail_not_empty.
    entailer!. 
  + assert (l = []).
    tauto.
    rewrite H0.
    sep_apply dlrep_local_facts_tail_empty.
    entailer!.
  + forward.
    unfold list_rep_with_cursor.
    Exists head tail.
    pose proof classic (l <> []).
    destruct H1.
    -
      sep_apply dlrep_tail_ptr_not_empty.
      entailer!.
    - assert (l = []).
      tauto.
      rewrite H2.
      sep_apply dlrep_tail_ptr_empty.
      entailer!.   
Qed.
(* rend *)
Definition rend_spec :=
 DECLARE _rend
  WITH p : val, l : list (Z * val)
  PRE  [ tptr t_struct_list ]
    PROP () 
    PARAMS (p) 
    GLOBALS ()
    SEP (list_rep_with_cursor l p)
  POST [ tptr t_struct_node ]
    PROP ()
    RETURN (nullval)
    SEP (list_rep_with_cursor l p).

Definition Gprog_rend : funspecs :=
            ltac:(with_library prog [rend_spec]).

Theorem body_rend: semax_body Vprog Gprog_rend
                     f_rend rend_spec.
Proof.
  start_function.
  unfold list_rep_with_cursor.
  Intros head tail.
  forward.
  unfold list_rep_with_cursor.
  Exists head tail.
  entailer!.
Qed.

(* next *)
Definition next_spec :=
 DECLARE _next
  WITH l1 : list (Z * val), v: Z, p: val, l2 : list (Z * val), x: val
  PRE  [ tptr t_struct_node ]
    PROP () 
    PARAMS (p)
    GLOBALS ()
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
  POST [ tptr t_struct_node ]
    PROP ()
    RETURN (head_ptr l2)
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x).

Definition Gprog_next : funspecs :=
            ltac:(with_library prog [next_spec]).

Theorem body_next: semax_body Vprog Gprog_next
                     f_next next_spec.
Proof.
  start_function.
  unfold list_rep_with_cursor.
  Intros head tail.
  sep_apply dlrep_middle_elem.
  Intros pv nx.
  forward.
  pose proof classic (l2 <> []).
  destruct H.
  + pose proof dlrep_local_facts_head_not_empty l2 nx tail p nullval.
    sep_apply H0. 
    entailer!.
  + assert (l2 = []).
    tauto.
    rewrite H0.
    unfold dlrep at 2.
    entailer!.
  + forward.
    unfold list_rep_with_cursor.
    Exists head tail.
    pose proof classic (l2 <> []).
    destruct H3.
    - pose proof dlrep_head_ptr_not_empty l2 nx tail p nullval. intuition.
      sep_apply H5.
      cancel. 
      pose proof elem_middle_dlrep.
      specialize (H4 l1 l2 v p head tail nullval nullval pv nx).
      sep_apply H4.
      entailer!.
    - assert (l2 = []).
      tauto.
      rewrite H4.
      unfold dlrep at 2.
      cancel.
      entailer!.
      pose proof elem_right_dlrep.
      specialize (H4 l1 v p head p nullval nullval pv).
      sep_apply H4.
      reflexivity.
      entailer!.
Qed.

(* rnext *)
Definition rnext_spec :=
 DECLARE _rnext
  WITH l1 : list (Z * val), v: Z, p: val, l2 : list (Z * val), x: val
  PRE  [ tptr t_struct_node ]
    PROP () 
    PARAMS (p)
    GLOBALS ()
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
  POST [ tptr t_struct_node ]
    PROP ()
    RETURN (tail_ptr l1)
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x).

Definition Gprog_rnext : funspecs :=
            ltac:(with_library prog [rnext_spec]).

Theorem body_rnext: semax_body Vprog Gprog_rnext
               f_rnext rnext_spec.
Proof.
  start_function.
  unfold list_rep_with_cursor.
  Intros head tail.
  sep_apply dlrep_middle_elem.
  Intros pv nx.
  pose proof classic (l1<>[]).
  destruct H.
  + forward. 
Admitted.

(* get_val *)
Definition get_val_spec :=
 DECLARE _get_val
  WITH l1 : list (Z * val), v: Z, p: val, l2 : list (Z * val), x: val
  PRE  [ tptr t_struct_node ]
    PROP () 
    PARAMS (p)
    GLOBALS ()
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr v))
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x).

Definition Gprog_get_val : funspecs :=
            ltac:(with_library prog [get_val_spec]).

Theorem body_get_val: semax_body Vprog Gprog_get_val
                        f_get_val get_val_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS, abbreviate.
  unfold list_rep_with_cursor.
  Intros head tail.
  unfold dlrep. fold dlrep.
  pose proof dlrep_middle_elem.
  specialize (H l1 v p l2 head tail nullval nullval).
  sep_apply H.
  Intros prev next.
  forward.
  forward.
  unfold list_rep_with_cursor.
  Exists head tail.
  sep_apply elem_middle_dlrep.
  entailer!.
Qed.

(* insert_before *)

(* insert_after *)

(* merge *)

(** Functions to be verified. *)

(* sum *)

(* delta *)

(* 2021-04-27 01:16 *)
