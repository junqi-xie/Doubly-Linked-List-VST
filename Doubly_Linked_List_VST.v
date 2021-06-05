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

    (* A patch of VST provided by Qinxiang Cao *)

Ltac field_address_solver :=
  match goal with
  | |- @eq val ?p (field_address _ _ ?p) => idtac
  | |- @eq val (offset_val _ ?p) (field_address _ _ ?p) => idtac
  | |- @eq val (field_address _ _ ?p) ?p => idtac
  | |- @eq val (field_address _ _ ?p) (offset_val _ ?p) => idtac
  | _ => fail 1 "The proof goal is not in a form of (p = field_address _ _ p) or (offset_val _ p = field_address _ _ p)"
  end;
  unfold field_address; simpl;
  (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
  rewrite ? isptr_offset_val_zero; auto.

Ltac check_vl_eq_args ::=
first [ 
   cbv beta; go_lower;
   repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
   gather_prop;
   repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
 repeat erewrite unfold_reptype_elim in * by reflexivity;
   try autorewrite with entailer_rewrite in *;
   simpl; auto;
   saturate_local;
 apply prop_right;
 match goal with
 | |- ?A = ?B =>
    unify (Datatypes.length A) (Datatypes.length B)
 | |- @eq (list val) _ _ =>
    fail 100 "Length of PARAMS list is not equal to the number of formal parameters of the funsig"
 | |- _ => fail 100 "Mysterious error in check_vl_eq_args"
 end;    
 repeat match goal with |- _ :: _ = _ :: _ => f_equal end;
 normalize;
 unfold field_address, field_address0;
 rewrite if_true; auto;
 auto with field_compatible;
 match goal with |- ?G => 
  match G with
  | field_compatible0 _ _ _ => idtac
  | field_compatible _ _ _ => idtac
  end;
  fail 100 "Before forward_call, assert and prove" G
 end
  | idtac (*alternative: fail 99 "Fail in tactic check_vl_eq_args"*)] .

Ltac handle_force_val :=
  match goal with
  | |- context [force_val ?A] => simpl (force_val A)
  | |- context [firstn ?A ?B] => simpl (firstn A B)
  | _ => idtac
  end.

Ltac entbang ::=
 intros;
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 match goal with
 | |- local _ && ?P |-- _ => clean_up_stackframe; go_lower; try apply empTrue
 | |- ?P |-- _ =>
    match type of P with
    | ?T => unify T mpred; pull_out_props
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ |-- _ "
 end;
 repeat match goal with
        | |- context [force_val (sem_binary_operation' ?op ?t1 ?t2 ?v1 ?v2)] =>
          progress 
              simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
                (force_val (sem_binary_operation' op t1 t2 v1 v2))
        end;
 simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
        sem_cast;
 saturate_local;
 ent_iter;
 repeat change (mapsto_memory_block.spacer _ _ _ _) with emp;
 first [ contradiction
        | simple apply prop_right; handle_force_val; my_auto
        | match goal with |- ?Q |-- !! _ && ?Q' => constr_eq  Q Q';
                      simple apply prop_and_same_derives'; handle_force_val; my_auto
          end
        | simple apply andp_right;
            [apply prop_right; handle_force_val; my_auto 
            | cancel; rewrite <- ?sepcon_assoc; autorewrite with norm ]
        | seplog_tactics.normalize; cancel; rewrite <- ?sepcon_assoc
        ].

Ltac data_at_conflict :=
  sep_apply data_at_conflict; [auto; try (solve [ simpl; computable ]) | apply FF_left].

(* TODO: the following lemmas and tactics for pointer comparison should be eliminated after
   porting to new VST. *)

Lemma true_Cne_neq: 
  forall x y, 
    typed_true tint (force_val (sem_cmp_pp Cne x y)) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H.
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?;
    try destruct (Int.eq i i0) eqn:?;
    simpl in H; try inversion H.
    intro. 
    inversion H0. subst i. 
    try pose proof (Int64.eq_spec i0 i0). 
    try pose proof (Int.eq_spec i0 i0). 
    rewrite Heqb in *.
    contradiction. 
  - intro. inversion H0.
  - intro. inversion H0.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. inversion H.  
      * intro. inversion H0.
        subst i.
        pose proof (Ptrofs.eq_spec i0 i0). rewrite Heqb1 in H2.
        contradiction.  
    + intro. inversion H0. subst b. contradiction.
Qed.

Lemma true_Ceq_eq: 
  forall x y, 
    typed_true tint (force_val (sem_cmp_pp Ceq x y)) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?; 
    try destruct (Int.eq i i0) eqn:?; 
    simpl in H; try inversion H.
    f_equal.
    try pose proof (Int64.eq_spec i i0).
    try pose proof (Int.eq_spec i i0).
    rewrite Heqb in *. auto.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i Int64.zero) eqn:?; 
    try destruct (Int.eq i Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i0 Int64.zero) eqn:?; 
    try destruct (Int.eq i0 Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0) eqn:E.
    + subst b. 
      destruct (Ptrofs.eq i i0) eqn:E'.
      * pose proof (Ptrofs.eq_spec i i0). rewrite E' in H0. subst i.
        reflexivity.
      * simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma false_Cne_neq: 
  forall x y, 
    typed_false tint (force_val (sem_cmp_pp Cne x y)) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?; 
    try destruct (Int.eq i i0) eqn:?; 
    simpl in H; try inversion H.
    f_equal.
    try pose proof (Int64.eq_spec i i0).
    try pose proof (Int.eq_spec i i0).
    rewrite Heqb in *. auto.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i Int64.zero) eqn:?; 
    try destruct (Int.eq i Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H;
    destruct Archi.ptr64 eqn:Hp; simpl in H;
    try destruct (Int64.eq i0 Int64.zero) eqn:?; 
    try destruct (Int.eq i0 Int.zero) eqn:?; 
    simpl in H; try inversion H.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. reflexivity.  
      * simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma false_Ceq_eq: 
  forall x y, 
    typed_false tint (force_val (sem_cmp_pp Ceq x y)) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; try inversion H. 
  - unfold sem_cmp_pp, strict_bool_val, Val.cmplu_bool, Val.cmpu_bool in H.
    destruct Archi.ptr64 eqn:Hp; simpl in H; 
    try destruct (Int64.eq i i0) eqn:?;
    try destruct (Int.eq i i0) eqn:?;
    simpl in H; try inversion H.
    intro. 
    inversion H0. subst i. 
    try pose proof (Int64.eq_spec i0 i0). 
    try pose proof (Int.eq_spec i0 i0). 
    rewrite Heqb in *.
    contradiction. 
  - intro. inversion H0.
  - intro. inversion H0.
  - unfold sem_cmp_pp in H. simpl in H.
    destruct (eq_block b b0).
    + destruct (Ptrofs.eq i i0) eqn:? .
      * simpl in H. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0.
        subst b i. inversion H.
      * intro. inversion H0. subst b i. pose proof (Ptrofs.eq_spec i0 i0). 
        rewrite Heqb1 in H2. contradiction.
    + intro. inversion H0. contradiction. 
Qed.

Ltac pointer_destructor :=
  repeat match goal with
  | x : typed_false tint (force_val (sem_cmp_pp Ceq ?Y ?Z)) |- _  =>
    try apply false_Ceq_eq in x; try contradiction
  | x : typed_true tint (force_val (sem_cmp_pp Ceq ?Y ?Z)) |- _ =>
    try apply true_Ceq_eq in x; try subst Y; try (assert_PROP False; entailer!)
  | x : typed_true tint (force_val (sem_cmp_pp Cne ?Y ?Z)) |- _ =>
    try apply true_Cne_neq in x; try contradiction
  | x : typed_false tint (force_val (sem_cmp_pp Cne ?Y ?Z)) |- _ =>
    try apply false_Cne_neq in x; try subst Y; try (assert_PROP False; entailer!)
  | _   => idtac
  end.

Ltac forward_if_wrp := forward_if; try pointer_destructor.
    
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
    
    Lemma elem_left_dlrep (l: list (Z*val)) (x:Z) (p head tail prev next next' : val):
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


    Lemma dlrep_head_neq_next (l : list (Z*val)):
      forall tail prev hn, 
          dlrep l hn tail prev hn |-- !!(l = []) && emp * dlrep l hn tail prev hn .
    Proof.
      induction l.
      {
        unfold dlrep.
        intros.
        entailer!.
      }
      intros.

      unfold dlrep.
      fold dlrep.
      destruct a.
      Intros head'. Exists head'. subst.
      unfold dlrep  at 1.
      destruct l.
      {
        unfold dlrep.
        entailer!.
      }
    Abort.



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
      forall l head tail prev,
        dlrep l head tail prev nullval |--
        !! (is_pointer_or_null head) && emp * dlrep l head tail prev nullval.
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
    
    Lemma dlrep_null_tail(l : list (Z*val)):
      forall head,
        dlrep l head nullval nullval nullval |-- (!! (l = [] /\ head=nullval)).
    Proof.
      intros.
      pose proof classic (l <> []).
      destruct H.
      + pose proof exists_last.
        specialize (X _ l).
        apply X in H.
        clear X.
        destruct H. destruct s.
        rewrite e.
        destruct x0.
        sep_apply dlrep_right_elem.
        Intros p'.
        subst.
        entailer!.
      + assert (l=[]).
        tauto.
        rewrite H0.
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

    Definition head_val (l : list (Z * val)): Z := 
      head_with_default (map fst l) 0.
      
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
      assert (rev l = 
        (fix rev (l0 : list val) : list val :=
          match l0 with
            | [] => []
            | x :: l' => rev l' ++ [x]
         end) l
      ).
      unfold rev; reflexivity.
      rewrite H.
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
          autorewrite with sublist.
          subst.
          entailer!.
    Qed.
      
  Lemma dlrep_head_eq_next(l:list(Z*val)):
    forall head tail prev,
      dlrep l head tail prev head |-- emp.
  Proof.
    induction l.
    unfold dlrep. entailer!.
    destruct a.
    intros.
    sep_apply dlrep_left_elem.
    Intros next'. subst.
  Abort.
    
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
      forward_while(
        EX head' tail' prev': val,
        EX l2 : list (Z*val),
        PROP ()
        LOCAL (temp _tmp head'; temp _l p)
        SEP ( (dlrep l2 head' tail' prev' nullval) *
               data_at Tsh t_struct_list (head', tail) p )
      )%assert.
      { 
        Exists head tail nullval l0.
        entailer!.
      }
      {
        destruct l2. unfold dlrep. entailer!.
        destruct p0. sep_apply dlrep_left_elem. Intros next'. entailer!.
      }
      {
        destruct l2.
        { 
          unfold dlrep.
          assert_PROP(head'=nullval).
          entailer!.
          contradiction.
        }
        destruct p0.
        sep_apply dlrep_left_elem.
        Intros next'. subst.
        forward.
        {
          sep_apply dlrep_local_facts_head.
          entailer!.
        }
        forward.
        unfold MORE_COMMANDS, abbreviate.
        sep_apply data_at_memory_block.
    
        forward_call ((head'),((sizeof(Tstruct _node noattr))%expr)).
        forward.
        Exists (next', tail', head', l2).
        unfold fst, snd.
        entailer!.
      }
          
      + sep_apply data_at_memory_block.
        forward_call (p,((sizeof(Tstruct _list noattr))%expr)).
        entailer!.
        destruct l2.
        unfold dlrep.
        entailer!.
        unfold dlrep. fold dlrep. 
        destruct p0. Intros head'.
        rewrite <- H.
        assert_PROP (v <> nullval).
        entailer!.
        contradiction.
    Qed.
    
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

    Search ret_temp.
    
    (* insert_before *)
    Definition insert_before_spec :=
     DECLARE _insert_before
      WITH l1 : list (Z*val), v : Z, p : val, l2 : list (Z*val), x: val,
           y : val, v' : Z
      PRE  [ tptr t_struct_list, tptr t_struct_node, tuint ]
        PROP () 
        PARAMS (x; p; Vint (Int.repr v'))
        GLOBALS ()
        SEP (list_rep_with_cursor (l1 ++ [(v,p)] ++ l2) x)
      POST [ Tvoid ] 
        PROP ()
        RETURN ()
        SEP (list_rep ((map fst l1) ++ [v'] ++ [v] ++ (map fst l2)) x).
    
    Definition Gprog_insert_before : funspecs :=
                ltac:(with_library prog [insert_before_spec; mallocN_spec]).

    Theorem body_insert_before: semax_body Vprog Gprog_insert_before
                                  f_insert_before insert_before_spec.
    Proof.
      start_function.
      unfold list_rep_with_cursor.
      Intros head tail.
      forward_call (sizeof(Tstruct _node noattr))%expr.
      { 
        simpl.
        rep_lia.
      }
      Intros vert.
      pose proof memory_block_data_at_ Tsh (Tstruct _node noattr) vert.
      pose proof malloc_compatible_field_compatible. 
      assert_PROP (complete_legal_cosu_type (Tstruct _node noattr) = true).
      { entailer!. }
    
      assert_PROP (natural_aligned natural_alignment (Tstruct _node noattr) = true).
      { entailer!. }
    
      specialize (H1 _ (Tstruct _node noattr) vert).
    
      assert (memory_block Tsh (sizeof (Tstruct _node noattr)) vert =
          data_at_ Tsh (Tstruct _node noattr) vert).
      { tauto. }
    
      rewrite H4.
      clear H H0 H1 H2 H3 H4.
      forward.
      forward.
      sep_apply dlrep_middle_elem.
      Intros prev' next'.
      forward.
      {
        pose proof classic (l1=[]).
        destruct H.
        + rewrite H. unfold dlrep at 1. entailer!.
        + sep_apply dlrep_local_facts_tail_not_empty.
          entailer!.
      }
      
      forward.
      forward.
      forward.
      {
        destruct l1.
        unfold dlrep at 1.
          
        entailer!.
        destruct p0.
        sep_apply dlrep_left_elem .
        Intros _______________________.
        entailer!.
      }
      forward_if_wrp.
      {
        destruct l1.
        unfold dlrep at 1.
        entailer!.
        destruct p0. sep_apply dlrep_left_elem.
        Intros __0000oooooOOOooOO__'''__''. subst. entailer!.
      }
      * 
        assert_PROP(isptr p).
        entailer!.
        assert_PROP(isptr head).
        destruct l1.
        unfold dlrep at 1. entailer!.
        destruct p0. sep_apply dlrep_left_elem. Intros sdfkjlfds. entailer!.

        
        
            forward.
            entailer!.
            assert(l1=[]). admit.
            pose proof elem_left_dlrep l2 v p p tail vert nullval next'.
            
            entailer!.
            assert_PROP(
              dlrep l2 next' tail p nullval * 
              data_at Tsh (Tstruct _node noattr) (Vint (Int.repr v), (vert, next')) p
              |-- !! (p = p) && emp * dlrep l2 next' tail p nullval *
              data_at Tsh t_struct_node (Vint (Int.repr v), (vert, next')) p
            ).
            entailer!. unfold t_struct_node. entailer!.
            sep_apply H2. clear H2. 
            cancel.
            autorewrite with sublist.
            unfold dlrep at 2.

            entailer!.

            unfold list_rep.
            
            autorewrite with sublist.
            Exists ([(v',vert)]++[(v,p)]++l2).
            entailer!.
            unfold list_rep_with_cursor.
            Exists vert tail.
            pose proof elem_left_dlrep l2 v p p tail vert nullval next'.
            sep_apply H2. reflexivity. cancel.
            assert ([(v,p)]++l2 = (v,p)::l2).
            list_solve. rewrite H11.
            remember ((v,p)::l2) as l3.
            pose proof elem_left_dlrep.
            pose proof elem_left_dlrep l3 v' vert vert tail nullval nullval p.
            assert_PROP (
              dlrep l3 p tail vert nullval * data_at Tsh (Tstruct _node noattr) (Vint (Int.repr v'), (nullval, p)) vert
              |--  !! (vert = vert) && emp * dlrep l3 p tail vert nullval *
              data_at Tsh t_struct_node (Vint (Int.repr v'), (nullval, p)) vert  
            ).
            entailer!. entailer!.
            sep_apply H13. reflexivity.
            assert((v',vert)::l3=[(v',vert)]++l3).
            list_solve.
            rewrite H15. entailer!.
          *
          assert_PROP(isptr p).
        entailer!.
        assert_PROP(isptr head).
        destruct l1.
        unfold dlrep at 1. entailer!.
        destruct p0. sep_apply dlrep_left_elem. Intros sdfkjlfds. entailer!.      
            forward.
            assert (l1<>[]). admit.
            pose proof exists_last. specialize (X _ l1). destruct X. tauto.
            destruct s. rewrite e. destruct x1.
            sep_apply dlrep_right_elem. Intros p'. subst.
            forward.
            entailer!.
            unfold list_rep.
            Exists (x0 ++ [(z, prev')] ++ [(v', vert)] ++ [(v,p)] ++ l2).
            unfold list_rep_with_cursor. Exists head tail. entailer!.
            pose proof map_app.
            specialize (H12 _ _ fst (x0 ++ [(z, prev')] ++ [(v', vert)] ++ [(v, p)]) l2).
            assert(x0 ++ [(z, prev')] ++ [(v', vert)] ++ [(v, p)] ++ l2 = (x0 ++ [(z, prev')] ++ [(v', vert)] ++ [(v, p)]) ++ l2).
            list_solve.
            rewrite H13.
            rewrite H12.
            pose proof map_app.
            specialize (H14 _ _ fst (x0 ++ [(z, prev')] ++ [(v', vert)]) ([(v,p)])).
            assert(x0 ++ [(z, prev')] ++ [(v', vert)] ++ [(v, p)]=(x0 ++ [(z, prev')] ++ [(v', vert)]) ++ [(v, p)])%assert.
            list_solve.
            rewrite H15.
            rewrite H14.
            pose proof map_app.
            specialize (H16 _ _ fst (x0 ++ [(z, prev')]) ([(v',vert)])).
            assert(x0 ++ [(z, prev')] ++ [(v', vert)]=(x0 ++ [(z, prev')]) ++ [(v', vert)]).
            list_solve.
            rewrite H17. rewrite H16.
            unfold map at 2 3,  fst at 2 3.
            list_solve.
            pose proof elem_right_dlrep x0 z prev' head prev' nullval vert p'.
            sep_apply H12. reflexivity.
            cancel.
            pose proof elem_left_dlrep l2 v p p tail vert nullval next'.
            sep_apply H13. reflexivity.
            assert((v,p)::l2=[(v,p)]++l2). list_solve. rewrite H14.
            assert( (x0 ++ [(z, prev')]) ++  [(v', vert)] ++ [(v, p)] ++ l2 = 
               x0 ++ [(z, prev')] ++ [(v', vert)] ++ [(v, p)] ++ l2).
             list_solve. rewrite <- H15.
            remember (x0++[(z,prev')]) as ll.
            remember ([(v,p)]++l2) as lr.
            cancel.
            pose proof elem_middle_dlrep ll lr v' vert head tail nullval nullval prev' p.
            sep_apply H16.
            assert(ll ++ (v', vert) :: lr = ll ++ [(v', vert)] ++ lr).
            list_solve.
            rewrite H17.
            entailer!.
    Admitted.
    
    (* insert_after *)
    Definition insert_after_spec :=
     DECLARE _insert_after
      WITH l1 : list (Z*val), v : Z, v': Z, p : val, p': val, l2 : list (Z*val), x: val
      PRE  [ tptr t_struct_list, tptr t_struct_node, tuint ]
        PROP () 
        PARAMS (x; p; Vint (Int.repr v'))
        GLOBALS ()
        SEP (list_rep_with_cursor (l1++[(v,p)]++l2) x)
      POST [ Tvoid ]
        PROP ()
        RETURN ()
        SEP (list_rep ((map fst l1) ++ [v] ++ [v'] ++ (map fst l2)) x).
    
    Definition Gprog_insert_after : funspecs :=
                ltac:(with_library prog [insert_after_spec; mallocN_spec]).
    
    Theorem body_insert_after: semax_body Vprog Gprog_insert_after
                                  f_insert_after insert_after_spec.
    Proof.
      start_function.
      forward_call (sizeof(Tstruct _node noattr)%expr) .
      {
        simpl.
        rep_lia.
      }
      Intros vert.

      pose proof memory_block_data_at_ Tsh (Tstruct _node noattr) vert.
      pose proof malloc_compatible_field_compatible. 
      assert_PROP (complete_legal_cosu_type (Tstruct _node noattr) = true).
      { entailer!. }
    
      assert_PROP (natural_aligned natural_alignment (Tstruct _node noattr) = true).
      { entailer!. }
    
      specialize (H1 _ (Tstruct _node noattr) vert).
    
      assert (memory_block Tsh (sizeof (Tstruct _node noattr)) vert =
          data_at_ Tsh (Tstruct _node noattr) vert).
      { tauto. }
      rewrite H4. clear H0 H1 H2 H3 H4.
      forward.
      forward.
      unfold list_rep_with_cursor.
      Intros head tail.
      sep_apply dlrep_middle_elem.
      Intros pv nx.
      forward.
      {
        pose proof dlrep_local_facts_head l2.
        sep_apply H0.
        entailer!.
      }
      forward.
      forward.
      forward.
      {
        pose proof classic (l2=[]).
        destruct H0.
        rewrite H0.
        unfold dlrep at 2. entailer!.
        pose proof dlrep_local_facts_tail_not_empty l2.
        sep_apply H1.
        entailer!.  
      }
      forward_if_wrp.
      {
        pose proof classic (l2=[]).
        destruct H7.
        rewrite H7.
        unfold dlrep at 2.
        entailer!.
        pose proof exists_last.
        specialize (X _ l2). destruct X. tauto. destruct s. destruct x1.
        rewrite e.
        sep_apply dlrep_right_elem.
        Intros __.
        entailer!.
      }
      + forward.
        entailer!.
        unfold list_rep.
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
                ltac:(with_library prog [merge_spec; freeN_spec]).
                
    
    Theorem body_merge: semax_body Vprog Gprog_merge
                          f_merge merge_spec.
    Proof.
      start_function.
      unfold list_rep.
      Intros vl1 vl2.
      unfold list_rep_with_cursor.
      Intros head1 tail1 head2 tail2.
      forward.
      {
        pose proof dlrep_local_facts_head vl2 head2 tail2 nullval.
        sep_apply H1.
        entailer!.
      }
      forward_if.
      {
        destruct vl2.
        + 
          unfold dlrep at 2.
          entailer!.
        + destruct p.
          sep_apply dlrep_left_elem.
          Intros next'.
          entailer!.
      }
      {
        forward.
        forward.
        pose proof classic (vl1 <> []).
        destruct H2.
        + sep_apply dlrep_local_facts_tail_not_empty.
          entailer!.
        + assert (vl1=[]). tauto. rewrite H3.
          sep_apply dlrep_local_facts_tail_empty.
          entailer!.
        + destruct vl2.
          -
            unfold dlrep at 2.
            assert_PROP(head2=nullval).
            entailer!.
            contradiction.
          - destruct p.
            sep_apply dlrep_left_elem.
            Intros next'.
            subst.
            forward.
            forward.
            forward_if(
              EX newL1Head  : val,
              PROP()
              LOCAL(temp _l1 p1; temp _l2 p2)
              SEP(
                data_at Tsh t_struct_list (newL1Head, tail1) p1;
                dlrep (vl1++[(z,head2)]++vl2) newL1Head tail2 nullval nullval;
                data_at Tsh t_struct_list (head2, tail2) p2)
            )%assert.
            {
              pose proof classic (vl1 = []).
              destruct H7.
              * rewrite H7.
                sep_apply dlrep_local_facts_tail_empty.
                unfold  dlrep at 1.
                entailer!.
              * pose proof exists_last.
                rename X into eL.
                specialize (eL _ vl1).
                apply eL in H7.
                destruct H7. destruct s.
                rewrite e.
                destruct x0.
                sep_apply dlrep_right_elem.
                Intros Ooo0oooOOoOOoo000oOooOOOoooOOOoO00OO'0'0''oO0__0oo___OO.
                entailer!.   
            }
            * forward.
              forward.
              pose proof classic (vl1 = []).
              destruct H0.
              ++ rewrite H0. unfold dlrep at 2.
                 assert_PROP (tail1=nullval).
                 entailer!.
                 contradiction.
              ++ pose proof exists_last.
                 rename X into eL.
                 specialize (eL _ vl1).
                 apply eL in H0. 
                 destruct H0. destruct s. destruct x0. rewrite e.
                 sep_apply dlrep_right_elem.
                 Intros p'. subst. 
                 forward.
                 Exists head1.
                 entailer!.
                 pose proof elem_right_dlrep x z0 tail1 head1 tail1 nullval head2 p'.
                 assert_PROP(
                  dlrep x head1 p' nullval tail1 *
                  data_at Tsh t_struct_node (Vint (Int.repr z0), (p', head2)) tail1 |--
                  !! (tail1 = tail1) && emp * dlrep x head1 p' nullval tail1 *
                  data_at Tsh t_struct_node (Vint (Int.repr z0), (p', head2)) tail1
                 ).
                 entailer!.
                 sep_apply H10.
                 sep_apply H9.
                 reflexivity.
                 entailer!.
                 remember (x ++ [(z0, tail1)]) as vl3.
                 pose proof elem_middle_dlrep vl3 vl2 z 
                            head2 head1 tail2 nullval nullval tail1 next'.
                 sep_apply H11.
                 entailer!.
            * forward.
              forward.
              Exists head2.
              rewrite H.
              entailer!.
              assert_PROP(vl1=[]).
              { sep_apply dlrep_null_tail; entailer!. }
              rewrite H.
              autorewrite with sublist.
              unfold dlrep at 2.
              pose proof elem_left_dlrep.
              pose proof elem_left_dlrep vl2 z head2 head2 tail2 nullval nullval next'.
              sep_apply H8.
              reflexivity.
              assert ( (z,head2)::vl2 = [(z,head2)]++vl2).
              list_solve.
              rewrite H9.
              entailer!.
            * Intros newL1Head. 
              forward.
              assert (vl1 ++ [(z,head2)] ++ vl2 = vl1 ++ (z,head2) :: vl2).
              list_solve.
              rewrite H.
              sep_apply dlrep_middle_elem.
              Intros prev' next'0.
              pose proof classic (vl2 = []).
              destruct H0.
              {
                rewrite H0.
                unfold dlrep at 2.
                entailer!.
              }
              {
                pose proof exists_last.
                specialize (X _ vl2).
                apply X in H0. destruct H0. destruct s.
                rewrite e.
                destruct x0.
                sep_apply dlrep_right_elem.
                Intros p'. subst.
                entailer!.
              }
              forward.
              pose proof data_at_memory_block.
              specialize (H Tsh t_struct_list (head2, tail2) p2).
              sep_apply H.
              forward_call( p2, (sizeof(Tstruct _list noattr))%expr ).
              entailer!.
              unfold list_rep.
              unfold list_rep_with_cursor.
              Exists (vl1 ++ [(z,head2)] ++ vl2).
              Exists (newL1Head) (tail2).
              entailer!.
              pose proof map_app.
              specialize (H3 _ _ (fst) vl1 ([(z,head2)]++vl2)).
              rewrite H3.
              pose proof map_app.
              specialize (H4 _ _ fst [(z,head2)] vl2).
              rewrite H4.
              unfold map at 2, fst at 2.
              list_solve.
      } 
      subst.
      destruct vl2.
      + unfold dlrep at 2.
    
        assert_PROP(tail2=nullval).
        entailer!.
        rewrite H.
    
        assert (
          data_at Tsh t_struct_list (nullval, nullval) p2 |--
          memory_block Tsh (sizeof t_struct_list) p2
        ).
    
        sep_apply data_at_memory_block. entailer!.
        sep_apply H0.
    
        forward_call (p2, (sizeof(Tstruct _list noattr))%expr).
        forward.
        unfold list_rep.
        Exists vl1.
        autorewrite with sublist.
        unfold list_rep_with_cursor.
        Exists head1 tail1.
        entailer!.
      + destruct p. sep_apply dlrep_left_elem.
        Intros next'.
        assert_PROP (v <> nullval).
        entailer!.
        contradiction.
    Qed.
    
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
                ltac:(with_library prog [sum_spec; begin_spec; end_spec; get_val_spec; next_spec]).
    
    Theorem body_sum: semax_body Vprog Gprog_sum
                        f_sum sum_spec.
    Proof.
      start_function.
      unfold list_rep.
      Intros l0.
      forward.
      forward_call (p, l0).
      forward_call (p, l0).
      unfold list_rep_with_cursor.
      Intros head tail.
      unfold LOOP_BODY, abbreviate.
      (*
        要求：具备p0的信息：能够说明判定p0==nullval是合法的，不是垂悬指针
             SEP部分不能太强：不能强于list_rep_with_cursor，否则next出来之后就没法往下了; 
             在循环出来之后能有办法证明l2是[]
             
      *)

      forward_while (
        EX p0,
        EX l1 l2: list(Z*val),
        PROP(l0 = l1 ++ l2 /\ p0 = (head_ptr l2))
        LOCAL(temp _q nullval; temp _p p0; temp _s (Vint (Int.repr (sum_list (map fst l1)))))
        SEP(
          list_rep_with_cursor (l1 ++ l2) p
        )
      ).
      + Exists (head_ptr l0) (@nil (Z*val)) l0.
        autorewrite with sublist. entailer!.
        unfold list_rep_with_cursor. Exists head tail. entailer!.
      + entailer!.
        destruct H0.
        destruct l2. unfold head_ptr, head_with_default,map,snd in H0.
        rewrite H0.
        entailer!.
        destruct p1. unfold head_ptr,head_with_default,map,snd in H0. subst.
        unfold list_rep_with_cursor.
        Intros hd tl.
        sep_apply dlrep_middle_elem.
        Intros pv nx. entailer!.
      + unfold list_rep_with_cursor. 
        Intros hd tl. admit.
      + forward.
        unfold list_rep.
        unfold list_rep_with_cursor.
        Intros h t. Exists (l1++l2) h t. entailer!.
        destruct
        unfold head_ptr, head_with_default in H0. 
        destruct l2. 

      
      
      forward_while (
        EX prev p0: val,
        EX l1 l2 : list(Z*val),
        PROP(l0 = l1 ++ l2 /\ p0 = (head_ptr l2))
        LOCAL(temp _q nullval; temp _p p0; temp _s (Vint (Int.repr (sum_list (map fst l1)))))
        SEP(
          dlrep l2 p0 tail prev nullval * 
          dlrep l1 head prev nullval p0 *
          data_at Tsh t_struct_list (head, tail) p
        )
      )%assert.
      {

        Exists nullval (head_ptr l0)  (@nil (Z*val)) l0.
        entailer!.
        sep_apply dlrep_head_ptr.
        unfold dlrep at 3.
        entailer!.
      }
      {
        entailer!.
        destruct l2.
        + unfold dlrep. entailer.
        + destruct p1. sep_apply dlrep_left_elem. Intros dfsdfjk. entailer!.  
      }
      {
        destruct l2.
        {
          unfold dlrep at 1.
          assert_PROP(p0=nullval).
          entailer!.
          contradiction.
        }
        destruct p1.
        sep_apply dlrep_left_elem.
        Intros next'. subst.
        forward_call (l1,z,p0,l2,p).
        {
          unfold list_rep_with_cursor.
          Exists head tail.
          pose proof elem_middle_dlrep l1 l2 z p0 head tail nullval nullval prev next'.
          sep_apply H.
          assert (l1++(z,p0)::l2=l1++[(z,p0)]++l2).
          list_solve.
          rewrite H1.
          entailer!.
        }
        forward.
        forward_call (l1,z,p0,l2,p).
        forward.
        Exists (nullval, p0, l1 ++ [(z,p0)], l2).
        entailer!.
        2: {
          unfold list_rep_with_cursor
        }
        {
          destruct H0.
          rewrite H0.

          split. list_solve.
          split. unfold head_ptr, head_with_default. admit.
          pose proof map_app.
          specialize (H1 _ _ fst l1 [(z,p0)]).
          rewrite H1.
          unfold map at 2, fst at 2.
          pose proof map_app.
          admit.
        }
        admit.
      }
      forward.
      destruct l2.
      unfold dlrep at 1.
      autorewrite with sublist. entailer!.
      unfold list_rep. Exists l1. unfold list_rep_with_cursor. entailer!.
      Exists head prev.
      entailer!.
      destruct p0.
      sep_apply dlrep_left_elem.
      Intros next'.
      subst.
      entailer!.
      unfold list_rep.
      Exists (l1 ++ (z,nullval) :: l2).
      unfold list_rep_with_cursor.
      entailer!.
      Exists head tail.
      pose proof elem_middle_dlrep l1 l2 z nullval head tail nullval nullval prev next'.
      sep_apply H3.
      entailer!.
      *)
    Admitted.
    
    (* delta *)
    Definition delta_spec :=
     DECLARE _delta
     WITH l1 : list (Z * val), v: Z, p: val, l2 : list (Z * val), x: val
      PRE  [ tptr t_struct_node ]
        PROP () 
        PARAMS (x; p)
        GLOBALS ()
        SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x)
      POST [ tuint ]
        PROP ()
        RETURN (Vint (Int.repr ((sum_list (map fst (l1 ++ [(v, p)]))) - (sum_list (map fst l2)))))
        SEP (list_rep_with_cursor (l1 ++ [(v, p)] ++ l2) x).
    
    (* RETURN parameters fixed *)
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
