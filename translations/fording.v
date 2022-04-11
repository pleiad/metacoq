From MetaCoq.Template Require Import utils All Checker.
From MetaCoq.Translations Require Import translation_utils.
Import MCMonadNotation.

(** * Plugin *)

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

Definition ford_type (t : term) (ind_indices : context) : term :=
    match t with
    | tApp ind args => tApp ind ()
Fixpoint add_ford_args (t : term) (ind_indices : context) (ctor_indices : list term)
  {struct ind_indices} : term :=
  match ind_indices , ctor_indices with
  | ii :: iis , ci :: cis =>
    tProd nAnon (mkEq ii.(decl_type) (tRel 0) ci) (add_ford t iis cis)
  | iis , cis => t
  end.


Definition tsl_cstr_type (c : constructor_body) (params : context) (ind_indices : context) : term :=
  let (t, ctor_params) := split_prod c.(cstr_type) (List.length params) in
  let (t', ctor_args) := split_prod t' (List.length c.(cstr_args)) in
  match t with
  | tProd na A B => tProd na (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | _ => t
  end.

Fixpoint tsl_cstr_type (t : term) (ind_indices : context) (ctor_indices : list term) 
  {struct t} : term :=
  match t with
  | tProd na A B => tProd na (tsl_rec0 n A) (tsl_rec0 (n+1) B)
  | _ => t
  end.


Definition tsl_mind_body (E : tsl_table) (mp : modpath) (kn : kername)
           (mind : mutual_inductive_body) : tsl_table * list mutual_inductive_body.
  refine (_, [{| ind_npars := mind.(ind_npars);
                 ind_params := mind.(ind_params);
                 ind_bodies := _;
                 ind_universes := mind.(ind_universes);
                 ind_variance := mind.(ind_variance)|}]).
- refine (let kn' : kername := (mp, tsl_ident kn.2) in
            fold_left_i (fun E i ind => _ :: _ ++ E) mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd kn i), tInd (mkInd kn' i) []).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, tConstruct (mkInd kn' i) k []).
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
                cstr_arity := c.(cstr_arity) + List.length (c.(cstr_indices)) |}%nat.
      refine (subst_app _ [tConstruct (mkInd kn i) k []]).
      refine (fold_left_i (fun t0 i u  => t0 {S i := u}) _ (tsl_rec1 E c.(cstr_type))).
      (* [I_n-1; ... I_0] *)
      refine (rev (mapi (fun i _ => tInd (mkInd kn i) [])
                              mind.(ind_bodies))).
Defined.