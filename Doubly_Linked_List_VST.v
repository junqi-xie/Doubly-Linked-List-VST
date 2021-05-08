(** You should verify a doubly linked list library using VST. You may use
    programs that we provided, or write those programs-to-verify by yourself.
    This library should include the following functions and two extra
    applications:

    struct node;
    struct list;
    struct node * begin(struct list * );
    struct node * end(struct list * );
    struct node * next(struct node * );
    struct node * rbegin(struct list * );
    struct node * rend(struct list * );
    struct node * rnext(struct node * );
    unsigned int get_val(struct node * );
    void insert_before (struct list *, struct node *; unsigned int )
    void insert_after (struct list *, struct node *; unsigned int )

    You may change the definition below if your version is better. *)
    Require Import EV.dlinklist.
    Require Import VST.floyd.proofauto.
    
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
      
    
    
    (** Memory representation of a mathematical list. Cursors mean places to
        insert. *)
    Definition list_rep_with_cursor (l : list (Z * val)) (p : val) : mpred :=
      EX (head tail : val),
        data_at Tsh t_struct_list (head, tail) p *
          dlrep l head tail nullval nullval.
    
    Definition list_rep (l : list Z) (p : val) : mpred :=
      EX l0: list (Z * val),
        !! (map fst l0 = l) && list_rep_with_cursor l0 p.
        
        
    Fixpoint dlseg (sigma: list (Z * val)) (head tail: val) : mpred :=
      match sigma with
      | nil => !! (head = tail) && emp
      | (x,p)::hs => EX prev next:val, !!(p=head) && data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next)) head * dlseg hs next tail
      end.
      
    (*
      dlrep_singleton: for a dlist with only one element (x, y), it's equivalent to 
                       data_at y. 
    *)
    Lemma dlrep_singleton: forall x y head tail prev next,
      
        dlrep [(x,y)] head tail prev next |-- !! (head = tail /\ head = y) && data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next)) y .
    Proof.
      intros.
      unfold dlrep.
      Intros head'.
      entailer!.
    Qed.
    
    Lemma singleton_dlrep (x : Z) ( y head tail prev next : val):
      !! (head = tail /\ head = y) && data_at Tsh t_struct_node (Vint (Int.repr x), (prev, next)) y |-- dlrep [(x,y)] head tail prev next.
    Proof.
      intros.
      unfold dlrep.
      Exists next.
      entailer!.
    Qed.
    
    Lemma dlrep_left_elem (l2: list (Z * val)) (v:Z) (p head tail pv nx: val): 
      dlrep ((v,p) :: l2) head tail pv nx |-- 
      EX next,
        !!(p = head) && emp * 
        dlrep l2 next tail p nx *
        data_at Tsh t_struct_node (Vint (Int.repr v), (pv, next)) p.
          
    Proof.
      intros.
      destruct l2.
      sep_apply (dlrep_singleton).
      unfold dlrep; fold dlrep.
      Exists nx.
      entailer!.
      
      unfold dlrep. fold dlrep.
      Intros head'.
      Exists head'.
      entailer!.
    Qed.
    
    Lemma elem_left_dlrep (l2: list (Z * val)) (v:Z) (p head tail pv nx next: val):
      !! (p = head) && emp * 
        dlrep l2 next tail p nx *
        data_at Tsh t_struct_node (Vint (Int.repr v), (pv, next)) p |-- dlrep ((v,p) :: l2) head tail pv nx.
    Proof.
      intros.
      entailer!.
      destruct l2.
      unfold dlrep.
      Exists next.
      entailer!.
      
      unfold dlrep; fold dlrep.
      destruct p.
      Intros head'.
      Exists next.
      Exists head'.
      entailer!.
    Qed.
      
    
    Require Import Coq.Classes.RelationClasses.
    Require Import Coq.Classes.Morphisms.
    Require Import PL.Imp.
       
    Check data_at.
    (* goal: represent dlrep l head tail nullval nullval with data_at ... *)
    
    
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
      
    Lemma dlrep_right_elem: forall l2 v p head tail pv nx, 
      dlrep ( l2 ++ [(v,p)]) head tail pv nx |-- 
      EX prev,
        !!(p = tail) && emp * 
        dlrep l2 head prev pv p *
        data_at Tsh t_struct_node (Vint (Int.repr v), (prev, nx)) p.
          
    Proof.
      intros.
      revert head tail pv nx.
      induction l2; intros.
      autorewrite with sublist.
      sep_apply (dlrep_singleton).
      Exists pv.
      unfold dlrep; fold dlrep.
      entailer!.
      
      unfold dlrep. fold dlrep.
      autorewrite with norm.
      destruct a.
      simpl.
      Intros  headof_l2.
      
      specialize (IHl2 headof_l2 tail head nx).
      sep_apply IHl2.
      simpl.
      Intros prev.
      Exists prev headof_l2.
      entailer!.   
    Qed.
    
    Lemma elem_middle_dlrep (l1 l2 : list (Z * val)) (v : Z) (p head tail pv nx prev next: val):
      dlrep l1 head prev pv p * 
            data_at Tsh t_struct_node (Vint (Int.repr v), (prev, next)) p *
            dlrep l2 next tail p nx |-- dlrep (l1 ++ (v,p) :: l2) head tail pv nx.
    Proof.
      revert head tail pv nx prev next p v.
      induction l1, l2; intros; autorewrite with sublist; unfold dlrep; fold dlrep.
      + Exists next.
      entailer!.
      + destruct p.
        Intros head'.
        Exists next head'.
        entailer!.
      + assert ((a :: l1) ++ [(v,p)] = a :: (l1 ++ [(v,p)])).
        list_solve.
        rewrite H.
        destruct a.
        pose proof elem_left_dlrep.
        specialize (H0 (l1++[(v,p)]) z v0 head tail pv nx).
        Intros head'.
        specialize (H0 head').
        assert_PROP ( data_at Tsh t_struct_node (Vint (Int.repr z), (pv, head')) head *
    dlrep l1 head' prev head p *
    data_at Tsh t_struct_node (Vint (Int.repr v), (prev, next)) p * emp|--!! (v0 = head) && emp * dlrep (l1 ++ [(v, p)]) head' tail v0 nx *
         data_at Tsh t_struct_node (Vint (Int.repr z), (pv, head')) v0).
         entailer!.
         cancel.
         specialize (IHl1 head' p head nx prev nx p v).
         assert_PROP(dlrep l1 head' prev head p *
    data_at Tsh t_struct_node (Vint (Int.repr v), (prev, nx)) p|--dlrep l1 head' prev head p *
           data_at Tsh t_struct_node (Vint (Int.repr v), (prev, nx)) p *
           dlrep [] nx p p nx).
         unfold dlrep; fold dlrep. entailer!. entailer!. 
         sep_apply H1. sep_apply IHl1. entailer!.
         sep_apply H4.
         sep_apply H0.
         exact H3.
         entailer!.
       + destruct a, p.
         assert (((z, v0) :: l1) ++ (v, p0) :: (z0,v1) :: l2 = (z, v0) :: l1 ++ (v, p0) :: (z0,v1) :: l2).
        list_solve.
        rewrite H; clear H.
        pose proof elem_left_dlrep.
        Intros l1_head l2_head.
        specialize (H (l1 ++ (v, p0) :: (z0, v1) :: l2) z v0 head tail pv nx l1_head).
        
        assert_PROP (data_at Tsh t_struct_node (Vint (Int.repr z), (pv, l1_head)) head *
    dlrep l1 l1_head prev head p0 *
    data_at Tsh t_struct_node (Vint (Int.repr v), (prev, next)) p0 *
    (data_at Tsh t_struct_node (Vint (Int.repr z0), (p0, l2_head)) next *
     dlrep l2 l2_head tail next nx) |-- !! (v0 = head) && emp *
        dlrep (l1 ++ (v, p0) :: (z0, v1) :: l2) l1_head tail v0 nx *
        data_at Tsh t_struct_node (Vint (Int.repr z), (pv, l1_head)) v0).
        - entailer!.
          pose proof elem_left_dlrep.
          specialize (H0 l2 z0 next next tail p0 nx l2_head).
          assert_PROP (data_at Tsh t_struct_node (Vint (Int.repr z0), (p0, l2_head)) next *
     dlrep l2 l2_head tail next nx |-- !! (next = next) && emp * dlrep l2 l2_head tail next nx *
         data_at Tsh t_struct_node (Vint (Int.repr z0), (p0, l2_head)) next).
          entailer!. entailer!.
          sep_apply H1; clear H1.
          sep_apply H0; clear H0.
          reflexivity.
          entailer!.
          specialize (IHl1 l1_head tail head nx prev next p0 v).
          sep_apply IHl1; clear IHl1.
          entailer!.
        - sep_apply H2; clear H2. sep_apply H; clear H. exact H0.
        entailer!.
    Qed.
        
      
    Lemma dlrep_middle_elem: forall l1 v p l2 head tail pv nx, 
      
          dlrep (l1 ++ (v,p) :: l2) head tail pv nx |-- EX prev next,
            dlrep l1 head prev pv p * 
            data_at Tsh t_struct_node (Vint (Int.repr v), (prev, next)) p *
            dlrep l2 next tail p nx.
       
    Proof.
      intros.
      
      revert head tail pv nx.
      induction l1, l2; intros; autorewrite with sublist; unfold dlrep; fold dlrep.
      + 
        Intros next.
        Exists pv nx.
        entailer!.
      +  
       Intros next.
        Exists pv next.
        entailer!.
      + 
        assert ((a :: l1) ++ [(v,p)] = a :: (l1 ++ [(v,p)])).
        list_solve.
        rewrite H.
        pose proof dlrep_left_elem.
        destruct a.
        specialize (H0 (l1++[(v,p)]) z v0 head tail pv nx).
        sep_apply H0.
        clear  H0.
        Intros next.
        specialize (IHl1 next tail v0 nx).
        sep_apply IHl1.
        Intros prev next0.
        Exists prev next0.
        Exists next.
        unfold dlrep; fold dlrep.
        entailer!.
      + pose proof dlrep_left_elem.
        destruct a.
        assert (((z, v0) :: l1) ++ (v, p) :: p0 :: l2 = (z, v0) :: l1 ++ (v, p) :: p0 :: l2).
        list_solve.
        rewrite H0; clear H0.
        specialize (H (l1 ++ (v, p) :: p0 :: l2) z v0 head tail pv nx).
        sep_apply H.
        Intros next.
        specialize (IHl1 next tail v0 nx).
        sep_apply IHl1.
        Intros prev next0.
        Exists prev next0.
        Exists next.
        destruct p0.
        pose proof dlrep_left_elem.
        specialize (H1 l2 z0 v1 next0 tail p nx).
        sep_apply H1.
        Intros next1.
        Exists next1.
        entailer!.
    Qed.
    
    (* mallocN *)
    Definition mallocN_spec :=
     DECLARE _mallocN
      WITH n: Z
      PRE [tint]
        PROP ( 4 <= n <= Int.max_unsigned )
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
          
    Definition Gprog_list_new : funspecs := ltac:(with_library prog [list_new_spec; mallocN_spec]).
    
    Check memory_block_zero.
    Check memory_block_isptr.
    Check memory_block_split.
    Check memory_block_data_at_.
    
    Lemma body_list_new: semax_body Vprog Gprog_list_new f_list_new list_new_spec.
    Proof.
      start_function.
      
      forward_call ((sizeof(Tstruct _list noattr))%expr).
      {
        simpl.
        rep_lia.
      }
      Intros vert.
      pose proof memory_block_data_at_ Tsh (Tstruct _list noattr) vert.
      pose proof malloc_compatible_field_compatible. 
      assert_PROP (complete_legal_cosu_type (Tstruct _list noattr) = true).
      entailer!.
      assert_PROP (natural_aligned natural_alignment (Tstruct _list noattr) = true).
      entailer!.
      specialize (H1 _ (Tstruct _list noattr) vert).
      assert (field_compatible (Tstruct _list noattr) [] vert).
      tauto.
      assert (memory_block Tsh (sizeof (Tstruct _list noattr)) vert =
         data_at_ Tsh (Tstruct _list noattr) vert).
      tauto.
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
        
    Definition Gprog_list_free : funspecs := ltac:(with_library prog [list_free_spec; freeN_spec]).
    
    Lemma body_list_free: semax_body Vprog Gprog_list_new f_list_free list_free_spec.
    Proof.
      start_function.
      unfold list_rep. unfold list_rep_with_cursor.
      Intros l0 head tail.
      forward.
      entailer!.
      
    Abort.
      
        
    
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
        
    Definition Gprog_get_val : funspecs := ltac:(with_library prog [get_val_spec]).
    
    (* dlrep (l1 ++ (v, p) :: l2) head tail
         nullval nullval))
       ==> convert to: dlrep l1 head tail' nullval nullval * data_at (v, p) * dlrep l2 head' tail nullval nullval *)
    
        
    
    Lemma body_get_val: semax_body Vprog Gprog_get_val f_get_val get_val_spec.
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
    
    (* 2021-04-27 01:16 *)
    