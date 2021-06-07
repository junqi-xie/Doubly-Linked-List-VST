# Doubly-Linked-List-VST

This repository contains the final project for CS2603 (2021 Spring). This project aims to verify a doubly linked list library using VST.

## Environment Setup

* This repository was tested with Coq Version 8.12.2, Windows 10.
* This repository also requires the VST submodule from [PrincetonUniversity/VST](https://github.com/PrincetonUniversity/VST/tree/release-v2.6). Please install it according to the instructions.

## Proof Introductions

### Verified Library

The following doubly-linked list library is proved in this project:

```
// Structure Definitions
struct node;
struct list;

// Basic Properties
struct list *list_new();
void list_free(struct list *l);
struct node *begin(struct list *l);
struct node *end(struct list *l);
struct node *rbegin(struct list *l);
struct node *rend(struct list *l);
struct node *next(struct node *p);
struct node *rnext(struct node *p);
unsigned int get_val(struct node *p);

// Insertions and Deletions
void insert_before(struct list *l, struct node *p, unsigned int v);
void insert_after(struct list *l, struct node *p, unsigned int v);
void merge(struct list *l1, struct list *l2);

// Applications (to demonstrate the usage of the library)
unsigned int sum(struct list *l)
unsigned int delta(struct list *l, struct node *r)
```

The C source is in `dlinklist.c`. The compiled definitions are in `dlinklist.v`.

### Definitions and Specifications

The definitions of the doubly-linked list are layered as follows:

* Concrete memory representation of a doubly-linked list with values and addresses
  ```
  Fixpoint dlrep (l : list (Z * val)) (head tail prev next : val) : mpred :=
  match l with
  | (x, p) :: l' =>
    EX head' : val,
      !! (p = head) &&
      data_at Tsh t_struct_node (Vint (Int.repr x), (prev, head')) head *
      dlrep l' head' tail head next
  | nil => !! (tail = prev /\ head = next) && emp
  end.
  ```
* Memory representation of a doubly-linked list with addresses
  ```
  Definition list_rep_with_cursor (l : list (Z * val)) (p : val) : mpred :=
  EX (head tail : val),
    data_at Tsh t_struct_list (head, tail) p *
    dlrep l head tail nullval nullval.
  ```
* Memory representation of a doubly-linked list without addresses
  ```
  Definition list_rep (l : list Z) (p : val) : mpred :=
  EX l0: list (Z * val),
    !! (map fst l0 = l) && list_rep_with_cursor l0 p.
  ```

Most specifications are provided by instructor `@QinxiangCao` except the following:

* `next` (modified to use `dlrep` explicitly)
* `get_val` (modified to use `dlrep` explicitly)
* `insert_before`
* `insert_after`
* `merge`

Note that the specifications about memory operations are not verified.

## License

* My codes are provided under GNU General Public License v3.0. See `LICENSE` for more information.
