#define NULL ((void *) 0)
#define DEFAULT 0u

extern void *mallocN (int n); 
extern void freeN (void *p, int n);

struct node{
    unsigned int val;
    // for convenience, do not use signed int
    struct node * prev;
    struct node * next;
};

struct list{
    struct node * head;
    struct node * tail;
};

struct list * list_new (){
    struct list * l = (struct list *) mallocN(sizeof (struct list));
    l->head = NULL;
    l->tail = NULL;
    return l;
}

void list_free (struct list * l){
    struct node * tmp = l->head;
    while (tmp != NULL){
        l->head = tmp->next;
        freeN(tmp, sizeof (struct node));
        tmp = l->head;
    }
    freeN(l, sizeof (struct list));
}

struct node * begin (struct list * l){
    return l->head;
}

struct node * end (struct list * l){
    return NULL;
}

struct node * rbegin (struct list * l){
    return l->tail;
}

struct node * rend (struct list * l){
    return NULL;
}

struct node * next (struct node * p){
    return p->next;
}

struct node * rnext (struct node * p){
    return p->prev;
}

void insert_before (struct list * l, struct node * p, unsigned int v){
    struct node * nd = (struct node *) mallocN(sizeof (struct node));
    nd->val = v;
    nd->next = p;
    nd->prev = p->prev;
    p->prev = nd;
    if (l->head == p) {
        l->head = nd;
    }else {
        nd->prev->next = nd;
    }
}

void insert_after (struct list * l, struct node * p, unsigned int v){
    struct node * nd = (struct node *) mallocN(sizeof (struct node));
    nd->val = v;
    nd->prev = p;
    nd->next = p->next;
    p->next = nd;
    if (l->tail == p) {
        l->tail = nd;
    }else {
        nd->next->prev = nd;
    }
}

void merge (struct list * l1, struct list * l2){
    if (l2->head != NULL){
        l2->head->prev = l1->tail;
    }else {
        freeN(l2, sizeof (struct list));
        return ;
    }
    if (l1->tail != NULL){
        l1->tail->next = l2->head;
    }else {
        l1->head = l2->head;
    }
    l1->tail = l2->tail;
    freeN(l2, sizeof (struct list));
}

unsigned int get_val (struct node * p){
    return p->val;
}

// These are two applications:

// sum of all:

unsigned int sum (struct list * l){
    unsigned int s = 0;
    struct node * p = begin(l);
    struct node * q = end(l);
    while (p != q){
        s = s + get_val(p);
        p = next(p);
    }
    return s;
}

// sum of left (excluding r) minus sum of right (including r):

unsigned int delta (struct list * l, struct node * r){
    unsigned int s = 0;
    struct node * p = begin(l);
    struct node * q = end(l);
    while (p != r){
        s = s + get_val(p);
        p = next(p);
    }
    while (p != q){
        s = s - get_val(p);
        p = next(p);
    }
    return s;
}
