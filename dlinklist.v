From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "dlinklist.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 16%positive.
Definition ___builtin_annot_intval : ident := 17%positive.
Definition ___builtin_bswap : ident := 9%positive.
Definition ___builtin_bswap16 : ident := 11%positive.
Definition ___builtin_bswap32 : ident := 10%positive.
Definition ___builtin_bswap64 : ident := 8%positive.
Definition ___builtin_clz : ident := 42%positive.
Definition ___builtin_clzl : ident := 43%positive.
Definition ___builtin_clzll : ident := 44%positive.
Definition ___builtin_ctz : ident := 45%positive.
Definition ___builtin_ctzl : ident := 46%positive.
Definition ___builtin_ctzll : ident := 47%positive.
Definition ___builtin_debug : ident := 58%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fmadd : ident := 50%positive.
Definition ___builtin_fmax : ident := 48%positive.
Definition ___builtin_fmin : ident := 49%positive.
Definition ___builtin_fmsub : ident := 51%positive.
Definition ___builtin_fnmadd : ident := 52%positive.
Definition ___builtin_fnmsub : ident := 53%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 18%positive.
Definition ___builtin_memcpy_aligned : ident := 14%positive.
Definition ___builtin_read16_reversed : ident := 54%positive.
Definition ___builtin_read32_reversed : ident := 55%positive.
Definition ___builtin_sel : ident := 15%positive.
Definition ___builtin_va_arg : ident := 20%positive.
Definition ___builtin_va_copy : ident := 21%positive.
Definition ___builtin_va_end : ident := 22%positive.
Definition ___builtin_va_start : ident := 19%positive.
Definition ___builtin_write16_reversed : ident := 56%positive.
Definition ___builtin_write32_reversed : ident := 57%positive.
Definition ___compcert_i64_dtos : ident := 27%positive.
Definition ___compcert_i64_dtou : ident := 28%positive.
Definition ___compcert_i64_sar : ident := 39%positive.
Definition ___compcert_i64_sdiv : ident := 33%positive.
Definition ___compcert_i64_shl : ident := 37%positive.
Definition ___compcert_i64_shr : ident := 38%positive.
Definition ___compcert_i64_smod : ident := 35%positive.
Definition ___compcert_i64_smulh : ident := 40%positive.
Definition ___compcert_i64_stod : ident := 29%positive.
Definition ___compcert_i64_stof : ident := 31%positive.
Definition ___compcert_i64_udiv : ident := 34%positive.
Definition ___compcert_i64_umod : ident := 36%positive.
Definition ___compcert_i64_umulh : ident := 41%positive.
Definition ___compcert_i64_utod : ident := 30%positive.
Definition ___compcert_i64_utof : ident := 32%positive.
Definition ___compcert_va_composite : ident := 26%positive.
Definition ___compcert_va_float64 : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 23%positive.
Definition ___compcert_va_int64 : ident := 24%positive.
Definition _begin : ident := 65%positive.
Definition _delta : ident := 83%positive.
Definition _end : ident := 66%positive.
Definition _freeN : ident := 60%positive.
Definition _get_val : ident := 78%positive.
Definition _head : ident := 5%positive.
Definition _insert_after : ident := 74%positive.
Definition _insert_before : ident := 73%positive.
Definition _l : ident := 61%positive.
Definition _l1 : ident := 75%positive.
Definition _l2 : ident := 76%positive.
Definition _list : ident := 7%positive.
Definition _list_free : ident := 64%positive.
Definition _list_new : ident := 62%positive.
Definition _main : ident := 84%positive.
Definition _mallocN : ident := 59%positive.
Definition _merge : ident := 77%positive.
Definition _nd : ident := 72%positive.
Definition _next : ident := 4%positive.
Definition _node : ident := 2%positive.
Definition _p : ident := 69%positive.
Definition _prev : ident := 3%positive.
Definition _q : ident := 80%positive.
Definition _r : ident := 82%positive.
Definition _rbegin : ident := 67%positive.
Definition _rend : ident := 68%positive.
Definition _rnext : ident := 70%positive.
Definition _s : ident := 79%positive.
Definition _sum : ident := 81%positive.
Definition _tail : ident := 6%positive.
Definition _tmp : ident := 63%positive.
Definition _v : ident := 71%positive.
Definition _val : ident := 1%positive.
Definition _t'1 : ident := 85%positive.
Definition _t'2 : ident := 86%positive.
Definition _t'3 : ident := 87%positive.
Definition _t'4 : ident := 88%positive.
Definition _t'5 : ident := 89%positive.
Definition _t'6 : ident := 90%positive.
Definition _t'7 : ident := 91%positive.
Definition _t'8 : ident := 92%positive.

Definition f_list_new := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _list noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _list noattr) tuint) :: nil))
    (Sset _l
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr)))
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _l (tptr (Tstruct _list noattr))))))))
|}.

Definition f_list_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tmp, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _tmp
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
  (Ssequence
    (Swhile
      (Ebinop One (Etempvar _tmp (tptr (Tstruct _node noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _tmp (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
            (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Scall None
            (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                           tvoid cc_default))
            ((Etempvar _tmp (tptr (Tstruct _node noattr))) ::
             (Esizeof (Tstruct _node noattr) tuint) :: nil))
          (Sset _tmp
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))))))
    (Scall None
      (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid
                     cc_default))
      ((Etempvar _l (tptr (Tstruct _list noattr))) ::
       (Esizeof (Tstruct _list noattr) tuint) :: nil))))
|}.

Definition f_begin := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_end := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition f_rbegin := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_rend := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition f_next := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_rnext := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_insert_before := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nd, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _node noattr) tuint) :: nil))
    (Sset _nd
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _val tuint) (Etempvar _v tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
        (Etempvar _p (tptr (Tstruct _node noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr)))
            (Etempvar _t'4 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr)))
            (Etempvar _nd (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _head
                (tptr (Tstruct _node noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                           (Etempvar _p (tptr (Tstruct _node noattr))) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _head
                  (tptr (Tstruct _node noattr)))
                (Etempvar _nd (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _next
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _nd (tptr (Tstruct _node noattr))))))))))))
|}.

Definition f_insert_after := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nd, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _node noattr) tuint) :: nil))
    (Sset _nd
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _val tuint) (Etempvar _v tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr)))
        (Etempvar _p (tptr (Tstruct _node noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
            (Etempvar _t'4 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
            (Etempvar _nd (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _node noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                           (Etempvar _p (tptr (Tstruct _node noattr))) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _node noattr)))
                (Etempvar _nd (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _next
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _nd (tptr (Tstruct _node noattr))))))))))))
|}.

Definition f_merge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l1, (tptr (Tstruct _list noattr))) ::
                (_l2, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
    (Sifthenelse (Ebinop One (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _t'7 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr)))
            (Etempvar _t'8 (tptr (Tstruct _node noattr))))))
      (Ssequence
        (Scall None
          (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                         tvoid cc_default))
          ((Etempvar _l2 (tptr (Tstruct _list noattr))) ::
           (Esizeof (Tstruct _list noattr) tuint) :: nil))
        (Sreturn None))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
      (Sifthenelse (Ebinop One (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _head
                (tptr (Tstruct _node noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _next
                (tptr (Tstruct _node noattr)))
              (Etempvar _t'5 (tptr (Tstruct _node noattr))))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
            (Etempvar _t'3 (tptr (Tstruct _node noattr)))))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr)))
          (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
      (Scall None
        (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid
                       cc_default))
        ((Etempvar _l2 (tptr (Tstruct _list noattr))) ::
         (Esizeof (Tstruct _list noattr) tuint) :: nil)))))
|}.

Definition f_get_val := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _val tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_sum := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tuint) :: (_p, (tptr (Tstruct _node noattr))) ::
               (_q, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _begin (Tfunction (Tcons (tptr (Tstruct _list noattr)) Tnil)
                       (tptr (Tstruct _node noattr)) cc_default))
        ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil))
      (Sset _p (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _end (Tfunction (Tcons (tptr (Tstruct _list noattr)) Tnil)
                       (tptr (Tstruct _node noattr)) cc_default))
          ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil))
        (Sset _q (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
      (Ssequence
        (Swhile
          (Ebinop One (Etempvar _p (tptr (Tstruct _node noattr)))
            (Etempvar _q (tptr (Tstruct _node noattr))) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _get_val (Tfunction
                                 (Tcons (tptr (Tstruct _node noattr)) Tnil)
                                 tuint cc_default))
                ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
              (Sset _s
                (Ebinop Oadd (Etempvar _s tuint) (Etempvar _t'3 tuint) tuint)))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _next (Tfunction
                              (Tcons (tptr (Tstruct _node noattr)) Tnil)
                              (tptr (Tstruct _node noattr)) cc_default))
                ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
              (Sset _p (Etempvar _t'4 (tptr (Tstruct _node noattr)))))))
        (Sreturn (Some (Etempvar _s tuint)))))))
|}.

Definition f_delta := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) ::
                (_r, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tuint) :: (_p, (tptr (Tstruct _node noattr))) ::
               (_q, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _begin (Tfunction (Tcons (tptr (Tstruct _list noattr)) Tnil)
                       (tptr (Tstruct _node noattr)) cc_default))
        ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil))
      (Sset _p (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _end (Tfunction (Tcons (tptr (Tstruct _list noattr)) Tnil)
                       (tptr (Tstruct _node noattr)) cc_default))
          ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil))
        (Sset _q (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
      (Ssequence
        (Swhile
          (Ebinop One (Etempvar _p (tptr (Tstruct _node noattr)))
            (Etempvar _r (tptr (Tstruct _node noattr))) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _get_val (Tfunction
                                 (Tcons (tptr (Tstruct _node noattr)) Tnil)
                                 tuint cc_default))
                ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
              (Sset _s
                (Ebinop Oadd (Etempvar _s tuint) (Etempvar _t'3 tuint) tuint)))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _next (Tfunction
                              (Tcons (tptr (Tstruct _node noattr)) Tnil)
                              (tptr (Tstruct _node noattr)) cc_default))
                ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
              (Sset _p (Etempvar _t'4 (tptr (Tstruct _node noattr)))))))
        (Ssequence
          (Swhile
            (Ebinop One (Etempvar _p (tptr (Tstruct _node noattr)))
              (Etempvar _q (tptr (Tstruct _node noattr))) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _get_val (Tfunction
                                   (Tcons (tptr (Tstruct _node noattr)) Tnil)
                                   tuint cc_default))
                  ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
                (Sset _s
                  (Ebinop Osub (Etempvar _s tuint) (Etempvar _t'5 tuint)
                    tuint)))
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _next (Tfunction
                                (Tcons (tptr (Tstruct _node noattr)) Tnil)
                                (tptr (Tstruct _node noattr)) cc_default))
                  ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
                (Sset _p (Etempvar _t'6 (tptr (Tstruct _node noattr)))))))
          (Sreturn (Some (Etempvar _s tuint))))))))
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   ((_val, tuint) :: (_prev, (tptr (Tstruct _node noattr))) ::
    (_next, (tptr (Tstruct _node noattr))) :: nil)
   noattr ::
 Composite _list Struct
   ((_head, (tptr (Tstruct _node noattr))) ::
    (_tail, (tptr (Tstruct _node noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tint Tnil))
     tvoid cc_default)) :: (_list_new, Gfun(Internal f_list_new)) ::
 (_list_free, Gfun(Internal f_list_free)) ::
 (_begin, Gfun(Internal f_begin)) :: (_end, Gfun(Internal f_end)) ::
 (_rbegin, Gfun(Internal f_rbegin)) :: (_rend, Gfun(Internal f_rend)) ::
 (_next, Gfun(Internal f_next)) :: (_rnext, Gfun(Internal f_rnext)) ::
 (_insert_before, Gfun(Internal f_insert_before)) ::
 (_insert_after, Gfun(Internal f_insert_after)) ::
 (_merge, Gfun(Internal f_merge)) :: (_get_val, Gfun(Internal f_get_val)) ::
 (_sum, Gfun(Internal f_sum)) :: (_delta, Gfun(Internal f_delta)) :: nil).

Definition public_idents : list ident :=
(_delta :: _sum :: _get_val :: _merge :: _insert_after :: _insert_before ::
 _rnext :: _next :: _rend :: _rbegin :: _end :: _begin :: _list_free ::
 _list_new :: _freeN :: _mallocN :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


(* 2021-04-27 01:16 *)
