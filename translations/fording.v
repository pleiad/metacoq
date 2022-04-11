From MetaCoq.Template Require Import utils All Checker.
Import MCMonadNotation.

(** * Plugin *)

Class TslIdent := { tsl_ident : ident -> ident }.

Local Instance prime_tsl_ident : TslIdent
  := {| tsl_ident := fun id => id ^ "'" |}.

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

Fixpoint split_prod (t : term) (n : nat)
  {struct n} : (term * (term -> term)) :=
  match t , n with
  | tProd na A B , S n => let r := split_prod B n
                         in (r.1 , fun x => (tProd na A (r.2 x)))
  | t , _ => (t , fun x => x)
  end.

Fixpoint add_indices_as_params (t : term) (indices : context)
  {struct indices} : term :=
  match indices with
  | i :: is => tProd i.(decl_name) i.(decl_type) (add_indices_as_params t is)
  | [] => t
  end.

Definition x := 1.
Definition y := 2.
MetaCoq Quote Definition foo := (nat).
Print foo.
Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.
MetaCoq Run (printInductive "list").

(* t1 = t2 , with t1, t2 : A *)
Definition mkEq (A t1 t2 : term) : term :=
  (tApp
    (tInd
      {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
         inductive_ind := 0 |} [])
    [A; t1; t2]).

Fixpoint ind_args' (from length : nat) {struct length} : list term :=
  match from , length with
  | S n , S m => tRel (S n) :: ind_args' n m
  | _ , _ => []
  end.

Fixpoint add_constraints (t : term) (n : nat) (ind_indices : context) (ctor_indices : list term)
  {struct ind_indices} : term :=
  match ind_indices , ctor_indices with
  | ii :: iis , ci :: cis =>
    tProd nAnon (mkEq ii.(decl_type) (tRel n) ci) (add_constraints t n iis cis)
  | _ , _ => t
  end.

Fixpoint add_indices (indices : context) (t : term) {struct indices} : term :=
  match indices with
  | ii :: iis => tProd ii.(decl_name) ii.(decl_type) (add_indices iis t)
  | [] => t
  end.

Definition get_ind (t : term) : term :=
  match t with
  | tApp ind _ => ind
  | t => t
  end.

Definition tsl_cstr_type (c : constructor_body) (params : context) (indices : context) : term :=
  let (t, add_ctor_params) := split_prod c.(cstr_type) (List.length params) in
  let (t', add_ctor_args) := split_prod t (List.length c.(cstr_args)) in
  let from := List.length params + (2 * List.length indices) + List.length c.(cstr_args) in
  let length := List.length params + List.length indices in
  let ind' := tApp (get_ind t') (ind_args' from length) in
  add_ctor_params (add_indices indices (add_ctor_args (add_constraints ind' (List.length c.(cstr_args)) indices c.(cstr_indices)))).

Definition tsl_mind_body (mind : mutual_inductive_body) : mutual_inductive_body.
  refine {| ind_npars := mind.(ind_npars);
            ind_params := mind.(ind_params);
            ind_bodies := _;
            ind_universes := mind.(ind_universes);
            ind_variance := mind.(ind_variance)|}.
  - exact mind.(ind_finite).
  - refine (mapi _ mind.(ind_bodies)).
    intros i ind.
    refine {| ind_name := tsl_ident ind.(ind_name);
              ind_indices := []; (* Remove indices. *)
              ind_sort := ind.(ind_sort);
              ind_type := ind.(ind_type);
              ind_kelim := ind.(ind_kelim);
              ind_ctors := _;
              ind_projs := [];
              ind_relevance := ind.(ind_relevance) |}.
    + (* constructors *)
      refine (mapi _ ind.(ind_ctors)).
      intros k c.
      refine {| cstr_name := tsl_ident c.(cstr_name);
                cstr_args := c.(cstr_args) ++ ind.(ind_indices);
                cstr_indices := [];
                cstr_type := tsl_cstr_type c mind.(ind_params) ind.(ind_indices);
                cstr_arity := c.(cstr_arity) + List.length (c.(cstr_indices)) |}%nat.
Defined.

Definition ford (tm : Ast.term) : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       let ind' := tsl_mind_body decl in
       tmMkInductive' ind'
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.

Inductive Vec (A : Type) : nat -> Type :=
  | vnil : Vec A 0
  | vcons : forall (n : nat), A -> Vec A n -> Vec A (S n).

MetaCoq Run (ford <% list %>).
Print natᵗ.