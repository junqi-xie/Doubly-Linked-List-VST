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
  forall head tail p,
    dlrep (@nil (Z*val)) head tail nullval p |--
    !! (is_pointer_or_null tail ) && emp * dlrep (@nil (Z*val)) head tail nullval p.
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
  Lemma rev_app_eq (l: list (Z*val)):
  forall a : (Z*val),
    rev (a::l) = rev l ++ a :: (@nil (Z*val)).
Proof.
  intros.
  unfold rev at 1.
  assert (rev l = (fix rev (l0 : list (Z * val)) : list (Z * val) :=
  match l0 with
  | [] => []
  | x :: l' => rev l' ++ [x]
  end) l).
  unfold rev; reflexivity.
  rewrite <- H.
  reflexivity.
Qed.

Lemma rev_not_nil(l : list (Z*val)):
  l <> (@nil (Z*val)) -> rev l <> (@nil (Z*val)).
Proof.
  intros.
  induction l.
  { contradiction. }
  pose proof classic (l = []).
  destruct H0.
  + rewrite H0.
    unfold rev.
    autorewrite with sublist.
    intuition.
    discriminate H1.
  + apply IHl in H0.
    pose proof rev_app_eq l a.
    rewrite H1.
    clear H1.
    remember (rev l) as w.
    clear IHl H Heqw.
    intuition.
    destruct w.
    - intuition.
    - discriminate H. 
Qed.

Lemma rev_app_eq_val (l: list val):
forall a : val,
  rev (a::l) = rev l ++ a :: (@nil val).
Proof.
intros.
unfold rev at 1.
assert (rev l = (fix rev (l0 : list val) : list val :=
match l0 with
| [] => []
| x :: l' => rev l' ++ [x]
end) l).
unfold rev; reflexivity.
rewrite <- H.
reflexivity.
Qed.

Lemma rev_not_nil_val(l : list val):
  l <> (@nil val) -> rev l <> [].
Proof.
  intros. induction l.
  { contradiction. }
  pose proof classic (l = []).
  destruct H0.
  + rewrite H0.
    unfold rev.
    autorewrite with sublist.
    intuition.
    discriminate H1.
  + apply IHl in H0.
    pose proof rev_app_eq_val l a.
    rewrite H1.
    clear H1.
    remember (rev l) as w.
    clear IHl H Heqw.
    intuition.
    destruct w.
    - intuition.
    - discriminate H.
Qed. 

Lemma map_snd_extract(l : list(Z*val)):
  forall a: (Z*val),
    map snd (a :: l) = snd(a) :: (map snd l).
Proof.
  intros.
  pose proof classic (l = []).
  destruct H.
  + rewrite H.
    unfold map, snd.
    reflexivity.
  + unfold map.
    reflexivity.
Qed. 

Lemma map_snd_not_nil(l : list(Z*val)):
  l <> [] -> map snd l <> [].
Proof.
  intros.
  induction l. contradiction.
  unfold map.
  remember (snd a) as vv.
  remember ((fix map (l0 : list (Z * val)) : list val :=
  match l0 with
  | [] => []
  | a0 :: t => snd a0 :: map t
  end) l) as vvvv.
  intuition.
  discriminate H0.
Qed.

Lemma tail_ptr_push_front(l : list (Z*val)):
  forall a,
    l <> (@nil (Z*val)) ->
      tail_ptr(a :: l) = tail_ptr l.
Proof.
  intros.
  induction (rev l).
  + unfold tail_ptr.
    pose proof map_snd_extract l a.
    rewrite H0.
    pose proof map_snd_not_nil l.
    apply H1 in H. clear H1.
    remember (map snd l) as msl.
    remember (snd a) as sa.
    pose proof rev_app_eq_val msl sa.
    rewrite H1.
    remember (rev msl) as rmsl.
    unfold head_with_default.
    assert (rmsl <> []).
    pose proof rev_not_nil_val msl.
    apply H2 in H. rewrite <- Heqrmsl in H.
    exact H.
    destruct rmsl.
    contradiction.
    reflexivity.
  + exact IHl0.
Qed.
  
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

Theorem body_list_free: semax_body Vprog Gprog_list_free
                          f_list_free list_free_spec.
Proof.
  start_function. 

  unfold list_rep, list_rep_with_cursor.
  Intros l0 head tail.
  forward.
  sep_apply dlrep_local_facts_head.
  entailer!.
  unfold LOOP_BODY, abbreviate.
  Print memory_block.
  Print List.length.
  Print Datatypes.length.

  (*
    设：原来的双向链表可以用dlrep l0 head tail nullval nullval表示；
    再设：l1为已经被free掉的元素构成的列表，l2为还没有被free掉的元素构成的列表
    则有：l0 = l1 ++ l2.
  
    循环不变量：
      PROP: l0 = l1 ++ l2.
      SEP:
        首先是局部变量p: data_at Tsh t_struct_list (head, tail) p
        然后是剩下的(还没有被释放的)链表：dlrep l2 head' tail nullval nullval.
        被释放掉的部分，则表现为一个memory block，大小为：(结构体的size)*length(l1), 起始位置为：head
  *)
  forward_while(
    EX l1 l2: list (Z*val),
    EX head': val,
    PROP (l0 = l1 ++ l2)
    LOCAL (temp _tmp head'; temp _l p)
    SEP ( (dlrep l2 head' tail nullval nullval) *
           data_at Tsh t_struct_list (head, tail) p *
          (memory_block Tsh (((sizeof(Tstruct _node noattr))%expr) * (Z.of_nat (List.length l1))) head)  
    )
  )%assert.
  + Exists (@nil (Z*val)) (l0) head.
    unfold Datatypes.length.
    assert (sizeof (Tstruct _node noattr) * Z.of_nat 0 = 0).
    lia.
    rewrite H0. 
    autorewrite with sublist.
    pose proof memory_block_zero Tsh head. rewrite H1.
    entailer!.
    (* isptr head: ??? *)
    admit.
  + entailer!.
    simpl.
    admit.
  + admit. 
  (* TODO: I dont know whether this is correct or not :( . *)
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
    - pose proof dlrep_local_facts_tail_not_empty l1 head pv nullval p.
      apply H0 in H.
      sep_apply H.
      entailer!.
    - forward.
      sep_apply dlrep_tail_ptr_not_empty.
      entailer!.
      unfold list_rep_with_cursor.
      Exists head tail .
      sep_apply elem_middle_dlrep.
      entailer!.
  + assert (l1 = []).
    tauto.
    rewrite H0.
    forward.
    sep_apply dlrep_local_facts_tail_empty.
    entailer!.
    forward.
    sep_apply dlrep_tail_ptr_empty.
    sep_apply elem_middle_dlrep.
    unfold list_rep_with_cursor. 
    Exists head tail.
    entailer!.
Qed.

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
Definition insert_before_spec :=
 DECLARE _insert_before
  WITH l1 : list (Z * val), v : Z, v': Z, p : val, p': val, l2 : list (Z * val), x: val
  PRE  [ tptr t_struct_list, tptr t_struct_node, tuint ]
    PROP () 
    PARAMS (x; p; Vint (Int.repr v'))
    GLOBALS ()
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (list_rep_with_cursor (l1 ++ [(v', p')] ++ [(v, p)] ++ l2) x).

Definition Gprog_insert_before : funspecs :=
            ltac:(with_library prog [insert_before_spec; mallocN_spec]).

Theorem body_insert_before: semax_body Vprog Gprog_insert_before
                              f_insert_before insert_before_spec.
Proof.
  
Admitted.

(* insert_after *)
Definition insert_after_spec :=
 DECLARE _insert_after
  WITH l1 : list (Z * val), v : Z, v': Z, p : val, p': val, l2 : list (Z * val), x: val
  PRE  [ tptr t_struct_list, tptr t_struct_node, tuint ]
    PROP () 
    PARAMS (x; p; Vint (Int.repr v'))
    GLOBALS ()
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (list_rep_with_cursor (l1 ++ [(v', p')] ++ [(v, p)] ++ l2) x).

Definition Gprog_insert_after : funspecs :=
            ltac:(with_library prog [insert_after_spec; mallocN_spec]).

Theorem body_insert_after: semax_body Vprog Gprog_insert_after
                              f_insert_after insert_after_spec.
Proof.

Admitted.

(* merge *)
Definition merge_spec :=
 DECLARE _merge
  WITH l1 : list Z, p1 : val, l2 : list Z, p2: val
  PRE  [ tptr t_struct_list, tptr t_struct_list ]
    PROP () 
    PARAMS (p1; p2)
    GLOBALS ()
    SEP (list_rep l1 p1 * list_rep l2 p2)
  POST [ Tvoid ]
    PROP ()
    RETURN ()
    SEP (list_rep (l1 ++ l2) p1).

Definition Gprog_merge : funspecs :=
            ltac:(with_library prog [merge_spec]).

Theorem body_merge: semax_body Vprog Gprog_merge
                      f_merge merge_spec.
Proof.

Admitted.

(** Functions to be verified. *)

(* sum *)
Fixpoint sum_list (l: list Z): Z :=
  match l with
  | nil => 0
  | h :: hs =>
    h + sum_list hs
  end.

Definition sum_spec :=
 DECLARE _sum
  WITH l : list Z, p: val
  PRE  [ tptr t_struct_list ]
    PROP () 
    PARAMS (p)
    GLOBALS ()
    SEP (list_rep l p)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (sum_list l)))
    SEP (list_rep l p).

Definition Gprog_sum : funspecs :=
            ltac:(with_library prog [sum_spec]).

Theorem body_sum: semax_body Vprog Gprog_sum
                    f_sum sum_spec.
Proof.

Admitted.

(*
  开始：dlrep l0 p q nullval nullval
  

  while (p != q)
  {
      s = s + get_val(p);
      p = next(p);
  }

  口胡出来的循环不变量：
    EX prev l1 l2 begin,
    PROP:
      l0 = l1 ++ l2.
      s = (sum_list l1).
    SEP:
      dlrep l2 p q prev nullval
      dlrep l1 begin prev nullval p
  解释：
    原双向链表l可以用dlrep l0 head tail nullval nullval 表示
    我们把l分为l1和l2两个部分，前者是从begin到p的前一个，即：prev，后者是p到end，即：
    begin <-> element_1 <-> element_2 <-> element_3 <-> ... <-> prev <-> p <-> ... <-> end
    |------------------------  l1 ----------------------------------|   |-------l2--------|
    那么s的值就是l1的所有元素的和，
    l也显然是l1 ++ l2

  不过这样写好像不太容易做... 还涉及到了一个sum_list函数，不过
  我想不到有什么能避开这样的操作的方法。
*)

(* delta *)
Definition delta_spec :=
 DECLARE _delta
 l1 : list (Z * val), v: Z, p: val, l2 : list (Z * val), x: val
  PRE  [ tptr t_struct_node ]
    PROP () 
    PARAMS (x; p)
    GLOBALS ()
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (sum_list (map fst l1 ++ [(v, p)]) - sum_list (map fst l2))))
    SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x).

(* 此处 RETURN 中的参数表达有一些问题，不过意思应当是明确的。不知如何在 VST 中对这一性质进行描述。 *)

Definition Gprog_delta : funspecs :=
            ltac:(with_library prog [delta_spec]).

Theorem body_delta: semax_body Vprog Gprog_delta
                      f_delta delta_spec.
Proof.

Admitted.

(*
  while (p != r)
  {
      s = s + get_val(p);
      p = next(p);
  }
  while (p != q)
  {
      s = s - get_val(p);
      p = next(p);
  }
  口胡出来的循环不变量：
    前一个循环不变量：和sum类似，不多说了
    前面一个循环出来后：
      EX prev_r l1 l2 begin
        l0 = l1 ++ l2.
        dlrep l1 begin prev_r nullval r
        dlrep l2 r q prev nullval
    l1 表示了 双向链表从begin到r的前面一个(这里定义成了prev)
    l2 表示了 双向链表从r到结尾
    这些里面涉及到的"EX"应该可以用Intros提到外面去

    后一个循环不变量：
      EX prev l2l l2r begin next_r, 
      PROP: 
        l0 = l1 ++ l2l ++ l2r
        l2 = l2l ++ l2r
        s = (sum_list l1) - (sum_list l2l)
      SEP:
        dlrep l2l r prev p nullval
        dlrep l1 begin prev_v nullval r
        dlrep l2r p q prev nullval
    解释：
      此处 l1含义同上
      l2可以进一步分为l2l和l2r: 前者是从r到p的前一个，后者是p到q
      然后s的值也就是l1的所有元素和再减去l2l的所有元素的和了。

    同样的，感觉不太容易进行下去，可能整个思路都还需要一些修改..

*)

(* 2021-04-27 01:16 *)
