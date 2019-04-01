(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega String Lia.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Asymmetric Patterns.

Notation "'∃' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Existing Instance config.default_checker_flags.

Derive NoConfusion for term.
Derive Subterm for term.

Section ListSize.
  Context {A} (size : A -> nat).

  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons a v) := S (size a + list_size v).
  Global Transparent list_size.

  Lemma list_size_app (l l' : list A) : list_size (l ++ l') = list_size l + list_size l'.
  Proof.
    funelim (list_size l); simpl; rewrite ?H; auto with arith.
  Defined.

  Lemma list_size_rev (l : list A) : list_size (List.rev l) = list_size l.
  Proof.
    funelim (list_size l); simpl; rewrite ?H ?list_size_app; simpl; auto; try lia.
  Defined.

End ListSize.

Section ListSizeMap.
  Context {A} (sizeA : A -> nat).
  Context {B} (sizeB : B -> nat).

  Lemma list_size_mapi_rec_eq (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi_rec f l k) = list_size sizeA l.
  Proof.
    revert k.
    funelim (list_size sizeA l); simpl; intros; rewrite ?H ?list_size_app; simpl; auto; try lia.
  Defined.

  Lemma list_size_mapi_eq (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi f l) = list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_eq.
  Defined.

  Lemma list_size_map_eq (l : list A) (f : A -> B) :
    (forall x, sizeA x = sizeB (f x)) ->
    list_size sizeB (map f l) = list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto.
  Defined.

  Lemma list_size_mapi_rec_le (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi_rec f l k) <= list_size sizeA l.
  Proof.
    intros Hf. revert k.
    apply_funelim (list_size sizeA l); simpl; intros; rewrite ?H ?list_size_app;
      simpl; auto; try lia.
    specialize (Hf k a).
    specialize (H (S k)). lia.
  Defined.

  Lemma list_size_mapi_le (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi f l) <= list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_le.
  Defined.

  Lemma list_size_map_le (l : list A) (f : A -> B) :
    (forall x, sizeB (f x) <= sizeA x) ->
    list_size sizeB (map f l) <= list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto. specialize (H a).
    lia.
  Defined.

End ListSizeMap.

Lemma list_size_map_hom {A} (size : A -> nat) (l : list A) (f : A -> A) :
  (forall x, size x = size (f x)) ->
  list_size size (map f l) = list_size size l.
Proof.
  intros.
  induction l; simpl; auto.
Defined.

Definition def_size (size : term -> nat) (x : def term) := size (dtype x) + size (dbody x).
Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (size p + size c + list_size (fun x => size (snd x)) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (mfixpoint_size size mfix)
  | tCoFix mfix idx => S (mfixpoint_size size mfix)
  | x => 1
  end.

Lemma size_lift n k t : size (lift n k t) = size t.
Proof.
  revert n k t.
  fix size_list 3.
  destruct t; simpl; rewrite ?list_size_map_hom; try lia.
  elim leb_spec_Set; simpl; auto. intros. auto.
  now rewrite !size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  intros.
  destruct x. simpl. now rewrite size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  unfold mfixpoint_size.
  rewrite list_size_map_hom. intros.
  simpl. destruct x. simpl. unfold def_size. simpl.
  now rewrite !size_list.
  reflexivity.
  unfold mfixpoint_size.
  rewrite list_size_map_hom. intros.
  simpl. destruct x. unfold def_size; simpl.
  now rewrite !size_list.
  reflexivity.
Qed.

Require Import RelationClasses Arith.

Arguments All {A} P%type _.

Lemma All_pair {A} (P Q : A -> Type) l :
  All (fun x => P x * Q x)%type l <~> (All P l * All Q l).
Proof.
  split. induction 1; intuition auto.
  move=> [] Hl Hl'. induction Hl; depelim Hl'; intuition auto.
Qed.

Definition on_local_decl (P : context -> term -> Type)
           (Γ : context) (t : term) (T : option term) :=
  match T with
  | Some T => (P Γ t * P Γ T)%type
  | None => P Γ t
  end.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type),

    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat), P Γ (tMeta n)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : name) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ (s : String.string) (u : list Level.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : list Level.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : list Level.t), P Γ (tConstruct i n u)) ->
    (forall Γ (p : inductive * nat) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Γ) l -> P Γ (tCase p t t0 l)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros.
  revert Γ t. set(foo:=Tactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size). simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr0 ->
                                                            All (fun x => P Γ (f x)) l).
  { induction l; constructor. eapply aux. red. simpl in H. lia. apply IHl. simpl in H. lia. }
  assert (forall mfix, context_size size (fix_context mfix) <= mfixpoint_size size mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_size.
    rewrite list_size_rev /=. cbn.
    rewrite size_lift. unfold context_size in IHmfix.
    epose (list_size_mapi_rec_le (def_size size) (decl_size size) mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1).
    forward l. intros. destruct x; cbn; rewrite size_lift. lia.
    unfold def_size, mfixpoint_size. lia. }
  assert (auxl' : forall Γ mfix,
             mfixpoint_size size mfix < size pr0 ->
             All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context mfix)).
  { move=> Γ mfix H0. move: (fix_context mfix) {H0} (le_lt_trans _ _ _ (H mfix) H0).
    induction fix_context; cbn. constructor.
    case: a => [na [b|] ty] /=; rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
    eapply IHfix_context. unfold context_size. lia.
    simpl. split. apply aux. red. lia. apply aux; red; lia.
    apply IHfix_context; unfold context_size; lia.
    apply aux. red. lia. }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxl' at top.

  !destruct pr0; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  eapply X13; try (apply aux; red; simpl; lia).
  apply auxl'. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.

  eapply X14; try (apply aux; red; simpl; lia).
  apply auxl'. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.
Defined.

Lemma simpl_subst' :
  forall N M n p k, k = List.length N -> p <= n -> subst N p (lift0 (k + n) M) = lift0 n M.
Proof. intros. subst k. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

Lemma mkApps_size x l : size (mkApps x l) = size x + list_size size l.
Proof.
  induction l in x |- *; simpl; simp list_size. lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma mkApps_eq_head {x l} : mkApps x l = x -> l = [].
Proof.
  assert (WF := _ : WellFounded (MR lt size)).
  induction l. simpl. constructor.
  apply apply_noCycle_right. simpl. red. rewrite mkApps_size. simpl. lia.
Qed.

Lemma mkApps_eq_inv {x y l} : x = mkApps y l -> size y <= size x.
Proof.
  assert (WF := _ : WellFounded (MR lt size)).
  induction l in x, y |- *. simpl. intros -> ; constructor.
  simpl. intros. specialize (IHl _ _ H). simpl in IHl. lia.
Qed.

Lemma mkApps_eq_left x y l : mkApps x l = mkApps y l -> x = y.
Proof.
  induction l in x, y |- *; simpl. auto.
  intros. simpl in *. specialize (IHl _ _ H). now noconf IHl.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now noconf IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma atom_decompose_app t l : isApp t = false -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_inj {t t' l l'} : mkApps t l = mkApps t' l' ->
                                   isApp t = false -> isApp t' = false -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !atom_decompose_app in Happ; auto.
  now rewrite !app_nil_r in Happ.
Qed.

(** All2 lemmas *)

Derive NoConfusion for All2.

Lemma All2_skipn {A} {P : A -> A -> Type} {l l'} {n} : All2 P l l' -> All2 P (skipn n l) (skipn n l').
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All2_app {A} {P : A -> A -> Type} {l l' r r'} :
  All2 P l l' -> All2 P r r' ->
  All2 P (l ++ r) (l' ++ r').
Proof. induction 1; simpl; auto. Qed.

Definition on_Trel_eq {A B C} (R : A -> A -> Type) (f : B -> A) (g : B -> C) (x y : B) :=
  (on_Trel R f x y * (g x = g y))%type.

Definition All2_prop_eq Γ Γ' {A B} (f : A -> term) (g : A -> B) (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (on_Trel_eq (rel Γ Γ') f g).

Definition All2_prop Γ (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (rel Γ).

(* Scheme pred1_ind_all_first := Minimality for pred1 Sort Type. *)

Lemma All2_All2_prop {P Q : context -> context -> term -> term -> Type} {par par'} {l l' : list term} :
  All2 (P par par') l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2 (Q par par') l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *.
  apply aux; apply r. apply IHAll2.
Defined.

Lemma All2_All2_prop_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par'}
      {f : A -> term} {g : A -> B} {l l' : list A} :
  All2 (on_Trel_eq (P par par') f g) l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2_prop_eq par par' f g Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *.
  split. apply aux; apply r. apply r. apply IHAll2.
Defined.

Definition All2_prop2_eq Γ Γ' Γ2 Γ2' {A B} (f g : A -> term) (h : A -> B)
           (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ Γ') f x y * on_Trel_eq (rel Γ2 Γ2') g h x y)%type.

Definition All2_prop2 Γ Γ' {A} (f g : A -> term)
           (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ) f x y * on_Trel (rel Γ') g x y)%type.

Lemma All2_All2_prop2_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par' par2 par2'}
      {f g : A -> term} {h : A -> B} {l l' : list A} :
  All2_prop2_eq par par' par2 par2' f g h P l l' ->
  (forall par par' x y, P par par' x y -> Q par par' x y) ->
  All2_prop2_eq par par' par2 par2' f g h Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel_eq, on_Trel in *. split.
  apply aux. destruct r. apply p. split. apply aux. apply r. apply r. apply IHAll2.
Defined.

(* Lemma All2_All2_prop2 {A} {P Q : context -> term -> term -> Type} {par par'} *)
(*       {f g : A -> term} {l l' : list A} : *)
(*   All2_prop2 par par' f g P l l' -> *)
(*   (forall par x y, P par x y -> Q par x y) -> *)
(*   All2_prop2 par par' f g Q l l'. *)
(* Proof. *)
(*   intros H aux. *)
(*   induction H; constructor. unfold on_Trel_eq, on_Trel in *. split. *)
(*   apply aux. destruct r. apply p. apply aux. apply r. apply IHAll2. *)
(* Defined. *)

Section ParallelReduction.
  Context (Σ : global_context).

  Definition on_decl (P : context -> context -> term -> term -> Type)
             (Γ Γ' : context) (b : option (term * term)) (t t' : term) :=
    match b with
    | Some (b, b') => (P Γ Γ' b b' * P Γ Γ' t t')%type
    | None => P Γ Γ' t t'
    end.

  Definition on_decls (P : term -> term -> Type) (d d' : context_decl) :=
    match d.(decl_body), d'.(decl_body) with
    | Some b, Some b' => (P b b' * P d.(decl_type) d'.(decl_type))%type
    | None, None => P d.(decl_type) d'.(decl_type)
    | _, _ => False
    end.

  Section All_local_2.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Inductive All2_local_env : context -> context -> Type :=
    | localenv2_nil : All2_local_env [] []
    | localenv2_cons_abs Γ Γ' na t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' None t t' ->
        All2_local_env (Γ ,, vass na t) (Γ' ,, vass na t')
    | localenv2_cons_def Γ Γ' na b b' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' (Some (b, b')) t t' ->
        All2_local_env (Γ ,, vdef na b t) (Γ' ,, vdef na b' t').
  End All_local_2.

  Lemma All2_local_env_impl {P Q : context -> context -> term -> term -> Type} {par par'} :
    All2_local_env (on_decl P) par par' ->
    (forall par par' x y, P par par' x y -> Q par par' x y) ->
    All2_local_env (on_decl Q) par par'.
  Proof.
    intros H aux.
    induction H; constructor. auto. red in p. apply aux, p.
    apply IHAll2_local_env. red. split.
    apply aux. apply p. apply aux. apply p.
  Defined.


  Definition pred_atom t :=
    match t with
    | tVar _
    | tMeta _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Definition on_decl_over (P : context -> context -> term -> term -> Type) Γ Γ' :=
    fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ').

  Definition All2_local_env_over P Γ Γ' := All2_local_env (on_decl (on_decl_over P Γ Γ')).

  Inductive pred1 (Γ Γ' : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t0 t1 b0 b1 a0 a1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> pred1 Γ Γ' a0 a1 ->
      pred1 Γ Γ' (tApp (tLambda na t0 b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 Γ Γ' d0 d1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def_unfold i body :
      All2_local_env (on_decl pred1) Γ Γ' ->
      option_map decl_body (nth_error Γ' i) = Some (Some body) ->
      pred1 Γ Γ' (tRel i) (lift0 (S i) body)

  | pred_rel_refl i :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tRel i)  (tRel i)

  (** Case *)
  | pred_iota ind pars c u args0 args1 p brs0 brs1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | pred_fix mfix idx args0 args1 narg fn0 fn1 :
      unfold_fix mfix idx = Some (narg, fn0) ->
      is_constructor narg args1 = true ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' fn0 fn1 ->
      pred1 Γ Γ' (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ip p0 p1 mfix idx args0 args1 narg fn0 fn1 brs0 brs1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' fn0 fn1 ->
      pred1 Γ Γ' p0 p1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0)
            (tCase ip p1 (mkApps fn1 args1) brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix idx args0 args1 narg fn0 fn1 :
      unfold_cofix mfix idx = Some (narg, fn0) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' fn0 fn1 ->
      pred1 Γ Γ' (tProj p (mkApps (tCoFix mfix idx) args0))
            (tProj p (mkApps fn1 args1))

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      decl.(cst_body) = Some body ->
      pred1 Γ Γ' (tConst c u) (subst_instance_constr u body)

  | pred_const c u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tConst c u) (tConst c u)

  (** Proj *)
  | pred_proj i pars narg k u args0 args1 arg1 :
      All2 (pred1 Γ Γ') args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1 Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ Γ' M M' -> pred1 (Γ ,, vass na M) (Γ' ,, vass na M') N N' ->
                            pred1 Γ Γ' (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ Γ' M0 M1 ->
      pred1 Γ Γ' N0 N1 ->
      pred1 Γ Γ' (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)

  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' d0 d1 -> pred1 Γ Γ' t0 t1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1 Γ Γ' p0 p1 ->
      pred1 Γ Γ' c0 c1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | pred_proj_congr p c c' : pred1 Γ Γ' c c' -> pred1 Γ Γ' (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ Γ' M0 M1 -> pred1 (Γ ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
                               pred1 Γ Γ' (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') l l' -> pred1 Γ Γ' (tEvar ev l) (tEvar ev l')

  | pred_atom_refl t :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred_atom t -> pred1 Γ Γ' t t.

  Notation pred1_ctx Γ Γ' := (All2_local_env (on_decl pred1) Γ Γ').

  Ltac my_rename_hyp h th :=
    match th with
    | pred1_ctx _ _ ?G => fresh "pred" G
    | _ => PCUICWeakeningEnv.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.

  Definition extendP {P Q: context -> context -> term -> term -> Type}
             (aux : forall Γ Γ' t t', P Γ Γ' t t' -> Q Γ Γ' t t') :
    (forall Γ Γ' t t', P Γ Γ' t t' -> (P Γ Γ' t t' * Q Γ Γ' t t')).
  Proof.
    intros. split. apply X. apply aux. apply X.
  Defined.

  Lemma All2_All2_prop2_eq' {A B} {P Q : context -> context -> term -> term -> Type}
        {par par' par2 par2'}
        {f g : A -> term} {h : A -> B} {l l' : list A} :
    All2_prop2_eq par par' par2 par2' f g h (fun Γ Γ' x y => (P Γ Γ' x y) + (x = y))%type l l' ->
    (forall par par' x y, P par par' x y -> Q par par' x y) ->
    All2_prop2_eq par par' par2 par2'  f g h (fun Γ Γ' x y => (Q Γ Γ' x y) + (x = y))%type l l'.
  Proof.
    intros H aux.
    induction H; constructor. unfold on_Trel_eq, on_Trel in *. split.
    destruct r. destruct s. left.
    apply aux. apply p0. right. apply e. split.
    destruct r. destruct p. destruct s0. left.
    apply aux. apply p. right. apply e0. apply r. apply IHAll2.
  Defined.

  Lemma pred1_ind_all :
    forall P : forall (Γ Γ' : context) (t t0 : term), Type,
      let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in
      (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 ->
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 ->
          pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
          P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) ->
      (forall (Γ Γ' : context) (i : nat) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ Γ' (tRel i) (lift0 (S i) body)) ->
      (forall (Γ Γ' : context) (i : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          P Γ Γ' (tRel i) (tRel i)) ->
      (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ Γ' : context) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn0 fn1 : term),
          unfold_fix mfix idx = Some (narg, fn0) ->
          is_constructor narg args1 = true ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 -> P Γ Γ' (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)) ->
      (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn0 fn1 : term) (brs0 brs1 : list (nat * term)),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' fn0 fn1 ->
          P Γ Γ' fn0 fn1 ->
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0) (tCase ip p1 (mkApps fn1 args1) brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term)
              (narg : nat) (fn0 fn1 : term),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 ->
          P Γ Γ' (tProj p (mkApps (tCoFix mfix idx) args0)) (tProj p (mkApps fn1 args1))) ->
      (forall (Γ Γ' : context) (c : ident) (decl : constant_body) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          declared_constant Σ c decl ->
          forall u : universe_instance, cst_body decl = Some body ->
                                        P Γ Γ' (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ Γ' : context) (c : ident) (u : universe_instance),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          P Γ Γ' (tConst c u) (tConst c u)) ->
      (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance)
              (args0 args1 : list term) (arg1 : term),
          All2 (pred1 Γ Γ') args0 args1 ->
          All2 (P Γ Γ') args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ Γ' : context) (na : name) (M M' N N' : term),
          pred1 Γ Γ' M M' ->
          P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' ->
          P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ Γ' : context) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 -> P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' d0 d1 ->
          P Γ Γ' d0 d1 ->
          pred1 Γ Γ' t0 t1 ->
          P Γ Γ' t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 ->
          P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          pred1 Γ Γ' c0 c1 ->
          P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (c c' : term), pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 ->
          P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
          P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ Γ' : context) (ev : nat) (l l' : list term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ Γ' : context) (t : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          All2_local_env (on_decl P) Γ Γ' ->
          pred_atom t -> P Γ Γ' t t) ->
      forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0.
  Proof.
    intros. revert Γ Γ' t t0 X20.
    fix aux 5. intros Γ Γ' t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ _ (tRel _) _ => idtac
                | |- P _ _ (tConst _ _) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - simpl. apply X1; auto.
      apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - simpl. apply X2; auto.
      apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')).
    - eapply X4; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')).
    - eapply X5; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')).
      eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ Γ')).
    - eapply X6; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')).
    - eapply X7; eauto.
      apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - eapply X8; eauto.
      apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P) a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ Γ')).
    - eapply X15.
      eapply (All2_local_env_impl a). intros. apply X20.
      eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. exact X20.
      eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply X16.
      eapply (All2_local_env_impl a). intros. apply X20.
      eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. exact X20.
      eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')).
    - eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
  Defined.

  Lemma pred1_ind_all_ctx :
    forall (P : forall (Γ Γ' : context) (t t0 : term), Type)
           (Pctx : forall (Γ Γ' : context), Type),
      let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in
      (forall Γ Γ', All2_local_env (on_decl pred1) Γ Γ' -> All2_local_env (on_decl P) Γ Γ' -> Pctx Γ Γ') ->
      (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 ->
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 ->
          pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
          P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) ->
      (forall (Γ Γ' : context) (i : nat) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ Γ' (tRel i) (lift0 (S i) body)) ->
      (forall (Γ Γ' : context) (i : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tRel i) (tRel i)) ->
      (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ Γ' : context) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn0 fn1 : term),
          unfold_fix mfix idx = Some (narg, fn0) ->
          is_constructor narg args1 = true ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 -> P Γ Γ' (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)) ->
      (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn0 fn1 : term) (brs0 brs1 : list (nat * term)),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' fn0 fn1 ->
          P Γ Γ' fn0 fn1 ->
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0) (tCase ip p1 (mkApps fn1 args1) brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term)
              (narg : nat) (fn0 fn1 : term),
          unfold_cofix mfix idx = Some (narg, fn0) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 ->
          P Γ Γ' (tProj p (mkApps (tCoFix mfix idx) args0)) (tProj p (mkApps fn1 args1))) ->
      (forall (Γ Γ' : context) (c : ident) (decl : constant_body) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          declared_constant Σ c decl ->
          forall u : universe_instance, cst_body decl = Some body ->
                                        P Γ Γ' (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ Γ' : context) (c : ident) (u : universe_instance),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tConst c u) (tConst c u)) ->
      (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance)
              (args0 args1 : list term) (arg1 : term),
          All2 (pred1 Γ Γ') args0 args1 ->
          All2 (P Γ Γ') args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ Γ' : context) (na : name) (M M' N N' : term),
          pred1 Γ Γ' M M' ->
          P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' ->
          P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ Γ' : context) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 ->
          P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' d0 d1 ->
          P Γ Γ' d0 d1 ->
          pred1 Γ Γ' t0 t1 ->
          P Γ Γ' t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 ->
          P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          pred1 Γ Γ' c0 c1 ->
          P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (c c' : term), pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 ->
          P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
          P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ Γ' : context) (ev : nat) (l l' : list term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ Γ' : context) (t : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          pred_atom t -> P Γ Γ' t t) ->
      forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0.
  Proof.
    intros P Pctx P' Hctx. intros. revert Γ Γ' t t0 X20.
    fix aux 5. intros Γ Γ' t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ _ (tRel _) _ => idtac
                | |- P _ _ (tConst _ _) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - simpl. apply X1; auto. apply Hctx.
      apply (All2_local_env_impl a). intros. eapply X20.
      apply (All2_local_env_impl a). intros. eapply (aux _ _ _ _ X20).
    - simpl. apply X2; auto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')).
    - eapply X4; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')).
    - eapply X5; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')).
      eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ Γ')).
    - eapply X6; eauto.
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')).
    - eapply X7; eauto.
      apply Hctx, (All2_local_env_impl a). intros. exact a. intros. apply (aux _ _ _ _ X20).
    - eapply X8; eauto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P) a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ Γ')).
    - eapply X15.
      eapply (All2_local_env_impl a). intros. apply X20.
      eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. exact X20.
      eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply X16.
      eapply (All2_local_env_impl a). intros. apply X20.
      eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. exact X20.
      eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
  Defined.

  Lemma All2_local_env_app_inv :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) Γ Γl ->
      All2_local_env (on_decl (on_decl_over P Γ Γl)) Γ' Γr ->
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr).
  Proof.
    induction 2; auto.
    - simpl. constructor; auto.
    - simpl. constructor; auto.
  Qed.

  Lemma All2_local_env_length {P l l'} : @All2_local_env P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; auto. Qed.

  Hint Extern 20 (#|?X| = #|?Y|) =>
    match goal with
      [ H : All2_local_env _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
    | [ H : All2_local_env _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
    end : pcuic.

  Ltac pcuic := eauto with pcuic.

  Lemma All2_local_env_app':
    forall P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' ->
      ∃ Γl Γr, (Γ'' = Γl ,,, Γr) /\ #|Γ'| = #|Γr| /\ #|Γ| = #|Γl|.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. eapply (All2_local_env_length X).
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,,vass na t'). simpl. intuition eauto.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,, vdef na b' t'). simpl. intuition eauto.
  Qed.

  Lemma app_inj_length_r {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|r| = #|r'| -> l = l' /\ r = r'.
  Proof.
    induction r in l, l', r' |- *. destruct r'; intros; simpl in *; intuition auto; try discriminate.
    now rewrite !app_nil_r in H.
    intros. destruct r'; try discriminate.
    simpl in H.
    change (l ++ a :: r) with (l ++ [a] ++ r) in H.
    change (l' ++ a0 :: r') with (l' ++ [a0] ++ r') in H.
    rewrite !app_assoc in H. destruct (IHr _ _ _ H). now noconf H0.
    subst. now apply app_inj_tail in H1 as [-> ->].
  Qed.

  Lemma app_inj_length_l {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|l| = #|l'| -> l = l' /\ r = r'.
  Proof.
    induction l in r, r', l' |- *. destruct l'; intros; simpl in *; intuition auto; try discriminate.
    intros. destruct l'; try discriminate. simpl in *. noconf H.
    specialize (IHl _ _ _ H). forward IHl; intuition congruence.
  Qed.

  Lemma All2_local_env_app_ex:
    forall P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' ->
      ∃ Γl Γr, (Γ'' = Γl ,,, Γr) *
      All2_local_env
        (on_decl P)
        Γ Γl * All2_local_env (on_decl (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. constructor.
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor. auto. auto.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor. auto. auto.
  Qed.

  Lemma All2_local_env_app :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr) ->
      #|Γ| = #|Γl| ->
      All2_local_env (on_decl P) Γ Γl * All2_local_env (on_decl (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    intros. pose proof X as X'.
    apply All2_local_env_app' in X as [Γl' [Γr' ?]].
    destruct a as [? [? ?]].
    apply All2_local_env_app_ex in X' as [Γl2' [Γr2' [[? ?] ?]]].
    subst; rename_all_hyps.
    unfold app_context in heq_app_context.
    eapply app_inj_length_r in heq_app_context; try lia. destruct heq_app_context. subst.
    unfold app_context in heq_app_context0.
    eapply app_inj_length_r in heq_app_context0; try lia. intuition subst; auto.
    pose proof (All2_local_env_length a). lia.
  Qed.

  Lemma pred1_refl_gen Γ Γ' t : pred1_ctx Γ Γ' -> pred1 Γ Γ' t t.
  Proof.
    revert Γ'.
    unshelve einduction Γ, t using term_forall_ctx_list_ind;
    intros;
      try solve [(apply pred_atom; reflexivity) || constructor; auto];
      try solve [try red in X; constructor; unfold All2_prop2_eq, All2_prop2, on_Trel_eq, on_Trel in *; solve_all];
      intros.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_3.
      constructor; try red; eauto with pcuic.
    - assert (All2_local_env (on_decl (fun Δ Δ' : context => pred1 (Γ0 ,,, Δ) (Γ' ,,, Δ'))) (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        red in t0. red. split. eapply t0. eapply All2_local_env_app_inv; auto.
        eapply t0. eapply All2_local_env_app_inv; auto. }
      constructor; auto. red.
      unfold All2_prop_eq, on_Trel_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. eapply X3; auto.
      split. eapply X3. eapply All2_local_env_app_inv; auto. auto.
    - assert (All2_local_env (on_decl (fun Δ Δ' : context => pred1 (Γ0 ,,, Δ) (Γ' ,,, Δ'))) (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        red in t0. red. split. eapply t0. eapply All2_local_env_app_inv; auto.
        eapply t0. eapply All2_local_env_app_inv; auto. }
      constructor; auto. red.
      unfold All2_prop_eq, on_Trel_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. eapply X3; auto.
      split. eapply X3. eapply All2_local_env_app_inv; auto. auto.
  Qed.

  Lemma pred1_ctx_refl Γ : pred1_ctx Γ Γ.
  Proof.
    induction Γ. constructor.
    destruct a as [na [b|] ty]; constructor; try red; simpl; auto with pcuic.
    split; now apply pred1_refl_gen. apply pred1_refl_gen, IHΓ.
  Qed.
  Hint Resolve pred1_ctx_refl : pcuic.

  Lemma pred1_refl Γ t : pred1 Γ Γ t t.
  Proof. apply pred1_refl_gen, pred1_ctx_refl. Qed.

  Lemma pred1_pred1_ctx Γ Δ t u : pred1 Γ Δ t u -> pred1_ctx Γ Δ.
  Proof.
    intros H; revert Γ Δ t u H.
    refine (pred1_ind_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].
    induction X0. elimtype False. destruct pars, narg; discriminate. apply r.
  Qed.

  Hint Constructors pred1 : pcuic.
  Hint Resolve pred1_refl : pcuic.
  Hint Unfold All2_prop2_eq All2_prop2 on_decl on_decl_over on_rel on_Trel on_Trel_eq snd on_snd : pcuic.
  Hint Resolve All2_same: pcuic.
  Hint Constructors All2_local_env : pcuic.
  Hint Resolve pred1_refl_gen : pcuic.

  Hint Extern 4 => progress simpl : pcuic.
  Hint Extern 10 => progress split : pcuic.
  Hint Extern 5 => progress destruct_conjs : pcuic.

  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Γ Γ M N.
  Proof with eauto with pcuic.
    induction 1 using red1_ind_all; intros; eauto with pcuic;
      try constructor; intuition auto with pcuic.
    (* FIXNE cofix rule *) admit.
    admit.

    (* FIXME red1 allows conversion with differently annotated branches *)
    admit.
  (*   (* TODO update red1 to keep extra info equalities (on_Trel_eq) *) *)
    eapply OnOne2_All2...
    (* FIXME red1 converts in the wrong contexts, fixpoints and cofixpoints *)
    all:admit.
  Admitted.

End ParallelReduction.


Hint Constructors pred1 : pcuic.
Hint Resolve pred1_refl : pcuic.
Hint Unfold All2_prop2_eq All2_prop2 on_decl on_decl_over on_rel on_Trel on_Trel_eq snd on_snd : pcuic.
Hint Resolve All2_same: pcuic.
Hint Constructors All2_local_env : pcuic.
Hint Resolve pred1_refl_gen : pcuic.
Hint Resolve pred1_ctx_refl : pcuic.

Hint Extern 4 => progress simpl : pcuic.
Hint Extern 10 => progress split : pcuic.
Hint Extern 5 => progress destruct_conjs : pcuic.

Notation pred1_ctx Σ Γ Γ' := (All2_local_env (on_decl (pred1 Σ)) Γ Γ').

Hint Extern 20 (#|?X| = #|?Y|) =>
match goal with
  [ H : All2_local_env _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
| [ H : All2_local_env _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
end : pcuic.

Ltac pcuic := eauto with pcuic.

Ltac my_rename_hyp h th :=
  match th with
  | pred1_ctx _ _ ?G => fresh "pred" G
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Section ParallelReduction2.
  Context {Σ : global_context}.

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red Σ Γ M N.
  Proof.
    revert Γ Γ'. eapply (@pred1_ind_all Σ); intros; try constructor; pcuic.


    - (* Beta *)
      apply red_trans with (tApp (tLambda na t0 b1) a0).
      eapply (@red_app Σ); [apply red_abs|]; auto with pcuic.
      apply red_trans with (tApp (tLambda na t0 b1) a1).
      eapply (@red_app Σ); auto with pcuic.
      apply red1_red. constructor.

    - (* Zeta *)
      eapply red_trans with (tLetIn na d0 t0 b1).
      eapply red_letin; eauto with pcuic.
      eapply red_trans with (tLetIn na d1 t1 b1).
      eapply red_letin; eauto with pcuic.
      eapply red1_red; constructor.

    - (* To be continued :) *)

  Admitted.

End ParallelReduction2.

Section ParallelWeakening.

  Lemma nth_error_pred1_ctx {P} {Γ Δ} i body' :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Δ i) = Some (Some body') ->
    { body & (option_map decl_body (nth_error Γ i) = Some (Some body)) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body'.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b. intuition eauto. cbv. apply p.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma nth_error_pred1_ctx_l {P} {Γ Δ} i body :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    { body' & (option_map decl_body (nth_error Δ i) = Some (Some body')) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b'. intuition eauto. cbv. apply p.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
  Qed.
  Lemma skipn_nth_error {A} (l : list A) i :
     match nth_error l i with
     | Some a => skipn i l = a :: skipn (S i) l
     | None => skipn i l = []
     end.
  Proof.
    induction l in i |- *. destruct i. reflexivity. reflexivity.
    destruct i. simpl. reflexivity.
    simpl. specialize (IHl i). destruct nth_error.
    rewrite [skipn _ _]IHl. reflexivity.
    rewrite [skipn _ _]IHl. reflexivity.
  Qed.

  Lemma All2_local_env_over_app {Σ Γ0 Δ Γ'' Δ''} :
    pred1_ctx Σ Γ0 Δ ->
    All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
    pred1_ctx Σ (Γ0 ,,, Γ'') (Δ ,,, Δ'').
  Proof.
    intros. induction X0; pcuic; constructor; pcuic.
  Qed.

  (* Lemma All2_local_env_over_app_inv {Σ Γ0 Δ Γ'' Δ''} : *)
  (*   pred1_ctx Σ (Γ0 ,,, Γ'') (Δ ,,, Δ'') -> *)
  (*   pred1_ctx Σ Γ0 Δ -> *)
  (*   All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' -> *)

  (* Proof. *)
  (*   intros. induction X0; pcuic; constructor; pcuic. *)
  (* Qed. *)

  Lemma All2_local_env_weaken_pred_ctx {Σ Γ0 Γ'0 Δ Δ' Γ'' Δ''} :
      #|Γ0| = #|Δ| ->
  pred1_ctx Σ Γ0 Δ ->
  All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
  All2_local_env
    (on_decl
       (fun (Γ Γ' : context) (t t0 : term) =>
        forall Γ1 Γ'1 : context,
        Γ = Γ1 ,,, Γ'1 ->
        forall Δ0 Δ'0 : context,
        Γ' = Δ0 ,,, Δ'0 ->
        #|Γ1| = #|Δ0| ->
        forall Γ''0 Δ''0 : context,
        All2_local_env_over (pred1 Σ) Γ1 Δ0 Γ''0 Δ''0 ->
        pred1 Σ (Γ1 ,,, Γ''0 ,,, lift_context #|Γ''0| 0 Γ'1) (Δ0 ,,, Δ''0 ,,, lift_context #|Δ''0| 0 Δ'0)
          (lift #|Γ''0| #|Γ'1| t) (lift #|Δ''0| #|Δ'0| t0))) (Γ0 ,,, Γ'0) (Δ ,,, Δ') ->

  pred1_ctx Σ (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0) (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ').
  Proof.
    intros.
    pose proof (All2_local_env_length X0).
    eapply All2_local_env_app in X1 as [Xl Xr]; auto.
    induction Xr; simpl; auto. apply All2_local_env_over_app; pcuic.
    rewrite !lift_context_snoc. simpl. constructor. auto. red in p.
    specialize (p _ _ eq_refl _ _ eq_refl). forward p by auto.
    red. rewrite !Nat.add_0_r. simpl. specialize (p Γ'' Δ'').
    forward p. auto. pose proof (All2_local_env_length X0).
    rewrite H0 in p. congruence.

    destruct p.
    specialize (p _ _ eq_refl _ _ eq_refl H _ _ X0).
    specialize (p0 _ _ eq_refl _ _ eq_refl H _ _ X0).
    rewrite !lift_context_snoc. simpl. constructor; auto.
    red. split; auto.
    rewrite !Nat.add_0_r. rewrite H0 in p. simpl. congruence.
    rewrite !Nat.add_0_r. rewrite H0 in p0. simpl. congruence.
  Qed.

  Lemma All2_local_env_weaken_pred_ctx' {Σ Γ0 Γ'0 Δ Δ' Γ'' Δ''} ctx ctx' :
      #|Γ0| = #|Δ| -> #|Γ0 ,,, Γ'0| = #|Δ ,,, Δ'| ->
  pred1_ctx Σ Γ0 Δ ->
  All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
  All2_local_env
    (on_decl
       (on_decl_over
          (fun (Γ Γ' : context) (t t0 : term) =>
           forall Γ1 Γ'1 : context,
           Γ = Γ1 ,,, Γ'1 ->
           forall Δ0 Δ'0 : context,
           Γ' = Δ0 ,,, Δ'0 ->
           #|Γ1| = #|Δ0| ->
           forall Γ''0 Δ''0 : context,
           All2_local_env_over (pred1 Σ) Γ1 Δ0 Γ''0 Δ''0 ->
           pred1 Σ (Γ1 ,,, Γ''0 ,,, lift_context #|Γ''0| 0 Γ'1) (Δ0 ,,, Δ''0 ,,, lift_context #|Δ''0| 0 Δ'0)
             (lift #|Γ''0| #|Γ'1| t) (lift #|Δ''0| #|Δ'0| t0)) (Γ0 ,,, Γ'0) (Δ ,,, Δ')))
    ctx ctx' ->
  All2_local_env
    (on_decl
       (on_decl_over (pred1 Σ) (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0) (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')))
    (lift_context #|Γ''| #|Γ'0| ctx) (lift_context #|Δ''| #|Δ'| ctx').
  Proof.
    intros.
    pose proof (All2_local_env_length X0).
    induction X1; simpl; rewrite ?lift_context_snoc0; constructor; auto.
    - red in p. red in p. red. red. simpl.
      specialize (p Γ0 (Γ'0,,, Γ)).
      rewrite app_context_assoc in p. forward p by auto.
      specialize (p Δ (Δ',,, Γ')).
      rewrite app_context_assoc in p. forward p by auto.
      specialize (p H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in p.
      congruence.
    - destruct p.
      specialize (o Γ0 (Γ'0,,, Γ) ltac:(now rewrite app_context_assoc) Δ (Δ',,, Γ')
                                  ltac:(now rewrite app_context_assoc) H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in o.
      specialize (o0 Γ0 (Γ'0,,, Γ) ltac:(now rewrite app_context_assoc) Δ (Δ',,, Γ')
                                  ltac:(now rewrite app_context_assoc) H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in o0.
      red. split; auto.
  Qed.

  Hint Extern 100 => lia : pcuic.

  Lemma All2_local_env_app_left {Σ Γ Γ' Δ Δ'} :
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') -> #|Γ| = #|Γ'| ->
    pred1_ctx Σ Γ Γ'.
  Proof.
    intros. eapply All2_local_env_app in X; pcuic.
  Qed.

  Hint Extern 4 (pred1_ctx ?Σ ?Γ ?Γ') =>
    match goal with
      [ H : pred1_ctx Σ (Γ ,,, _) (Γ' ,,, _) |- _ ] => apply (All2_local_env_app_left H)
    end : pcuic.


  Lemma weakening_pred1 Σ Γ Γ' Γ'' Δ Δ' Δ'' M N : wf Σ ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') M N ->
    #|Γ| = #|Δ| ->
    All2_local_env_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
          (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')
          (lift #|Γ''| #|Γ'| M) (lift #|Δ''| #|Δ'| N).
  Proof.
    intros wfΣ H.

    remember (Γ ,,, Γ') as Γ0.
    remember (Δ ,,, Δ') as Δ0.
    intros HΓ.
    revert Γ Γ' HeqΓ0 Δ Δ' HeqΔ0 HΓ Γ'' Δ''.
    revert Γ0 Δ0 M N H.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros;
      rename_all_hyps; try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try pose proof (All2_local_env_length X0);
      try (eapply (All2_local_env_weaken_pred_ctx (Γ'0:=Γ'0) (Δ':=Δ') heq_length) in X0; pcuic);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *.

    - (* Beta *)
      specialize (forall_Γ _ (Γ'0,, vass na t0) eq_refl _ (Δ' ,, vass na t1) eq_refl heq_length _ _ X5).
      specialize (forall_Γ1 _ _ eq_refl _ _ eq_refl heq_length _ _ X5).
      econstructor; now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ (Γ'0,, vdef na d0 t0) eq_refl _ (Δ',, vdef na d1 t1)
                            eq_refl heq_length _ _ X5).
      simpl. econstructor; eauto.
      now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.

    - (* Rel unfold *)
      assert(#|Γ''| = #|Δ''|). red in X1. pcuic.
      elim (leb_spec_Set); intros Hn.
      + destruct nth_error eqn:Heq.
        pose proof (nth_error_Some_length Heq).
        rewrite !app_context_length in H H0.
        rewrite simpl_lift. lia. lia.
        rewrite Nat.add_succ_r.
        assert (pred1_ctx Σ Γ0 Δ) by (apply All2_local_env_app in predΓ'; pcuic).
        rewrite {2}H0.
        constructor; eauto. 
        rewrite <- heq_option_map. f_equal. rewrite <- Heq.
        now rewrite <- weaken_nth_error_ge.
        noconf heq_option_map.

      + (* Local variable *)
        pose proof (All2_local_env_length predΓ'). rewrite !app_context_length in H.
        rewrite <- lift_simpl; pcuic.
        econstructor; auto.
        rewrite (weaken_nth_error_lt). pcuic.
        now rewrite option_map_decl_body_map_decl heq_option_map.

    - (* Rel refl *)
      pose proof (All2_local_env_length X0).
      assert(#|Γ''| = #|Δ''|). red in X1. pcuic.
      rewrite !app_context_length in H.
      assert (#|Γ'0| = #|Δ'|) by lia. rewrite H2.
      elim (leb_spec_Set); intros Hn. rewrite H1. now econstructor.
      now constructor.

    - assert(#|Γ''| = #|Δ''|). red in X3; pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H1.
      assert (#|Γ'0| = #|Δ'|) by lia.
      rewrite lift_iota_red.
      autorewrite with lift.
      constructor; auto.
      apply All2_map. solve_all.
      apply All2_map. solve_all. specialize (b1 _ _ eq_refl _ _ eq_refl). forward b1 by pcuic.
      specialize (b1 _ _ X3). cbn in *. split; simpl. red. subst a. simpl. congruence. auto.

    - assert(Hlen:#|Γ''| = #|Δ''|). red in X1; pcuic.
      pose proof (lift_declared_constant _ _ _ #|Δ''| #|Δ'| wfΣ H).
      econstructor; eauto.
      rewrite H1.
      now rewrite - !map_cst_body heq_cst_body.

    - simpl. eapply pred_proj with (map (lift #|Δ''| #|Δ'|) args1).
      eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X5).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.
      econstructor; eauto.

    - econstructor; pcuic.
      rewrite !lift_fix_context. revert X2.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      red.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel_eq, on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.

    - econstructor; pcuic.
      rewrite !lift_fix_context. revert X2.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      red.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel_eq, on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.

    - specialize (forall_Γ0 Γ0 (Γ'0 ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Lemma weakening_pred1_pred1 Σ Γ Δ Γ' Δ' M N : wf Σ ->
    All2_local_env_over (pred1 Σ) Γ Δ Γ' Δ' ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') (lift0 #|Γ'| M) (lift0 #|Δ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Δ' M N); eauto.
    eapply pred1_pred1_ctx in X1. pcuic.
  Qed.

    Lemma All2_local_env_over_refl:
      forall (Σ : global_context) (Γ Δ Γ' : context),
        pred1_ctx Σ Γ Δ -> All2_local_env_over (pred1 Σ) Γ Δ Γ' Γ'.
    Proof.
      intros Σ Γ Δ Γ' X0.
      red. induction Γ'. constructor.
      pose proof IHΓ'. apply All2_local_env_over_app in IHΓ'; auto.
      destruct a as [na [b|] ty]; constructor; auto; intuition red; pcuic.
      intuition red; pcuic.
    Qed.


  Lemma weakening_pred1_0 Σ Γ Δ Γ' M N : wf Σ ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Γ' M N); eauto.
    eapply pred1_pred1_ctx in X0. pcuic.
    eapply pred1_pred1_ctx in X0.
    apply All2_local_env_over_refl; auto.
  Qed.

Hint Resolve pred1_pred1_ctx : pcuic.

        Lemma All2_local_env_over_pred1_ctx Σ Γ Γ' Δ Δ' :
          #|Δ| = #|Δ'| ->
          pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
          All2_local_env
            (on_decl (on_decl_over (pred1 Σ) Γ Γ')) Δ Δ'.
        Proof.
          intros. pose proof (All2_local_env_length X).
          apply All2_local_env_app in X.
          intuition. auto. rewrite !app_context_length in H0. pcuic.
        Qed.
        Hint Resolve All2_local_env_over_pred1_ctx : pcuic.

  Lemma nth_error_pred1_ctx_all_defs {P} {Γ Δ} :
    All2_local_env (on_decl P) Γ Δ ->
    forall i body body', option_map decl_body (nth_error Γ i) = Some (Some body) ->
              option_map decl_body (nth_error Δ i) = Some (Some body') ->
              P (skipn (S i) Γ) (skipn (S i) Δ) body body'.
  Proof.
    induction 1; destruct i; simpl; try discriminate.
    intros. apply IHX; auto.
    intros ? ? [= ->] [= ->]. apply p.
    intros ? ? ? ?. apply IHX; auto.
  Qed.

  Lemma All2_local_env_over_firstn_skipn:
    forall (Σ : global_context) (i : nat) (Δ' R : context),
      pred1_ctx Σ Δ' R ->
      All2_local_env_over (pred1 Σ) (skipn i Δ') (skipn i R) (firstn i Δ') (firstn i R).
  Proof.
    intros Σ i Δ' R redr.
    induction redr in i |- *; simpl.
    destruct i; constructor; pcuic.
    destruct i; simpl; constructor; pcuic. apply IHredr.
    repeat red. red in p. now rewrite /app_context !firstn_skipn.
    repeat red. red in p.
    destruct i; simpl; constructor; pcuic. apply IHredr.
    repeat red. destruct p.
    split; red; now rewrite /app_context !firstn_skipn.
  Qed.

  (* Checked that we can prove confluence in presence of let-reductions in the context *)
(*
  Theorem confluence Σ Γ Δ t l : wf Σ ->
    pred1 Σ Γ Δ t l -> forall Δ' r (Hr : pred1 Σ Γ Δ' t r),
    ∃ Δ'' v, (pred1 Σ Δ Δ'' l v) * (pred1 Σ Δ' Δ'' r v).
  Proof.
    intros wfΣ H; revert Γ Δ t l H.
    (* refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *. *)
    (* all:try intros **; rename_all_hyps; *)
    (*   try solve [specialize (forall_Γ _ X3); eauto]; eauto; *)
    (*     try solve [eexists; split; constructor; eauto]. *)
    (* intros. *)

    set(P' :=
          fun (Δ Δ' : context) =>
            forall Δ'', pred1_ctx Σ Δ Δ'' ->
                        ∃ R, pred1_ctx Σ Δ' R * pred1_ctx Σ Δ'' R).
                (* (forall i b b', option_map decl_body (nth_error (Γ ,,, Δ) i) = Some (Some b) -> *)
                (*                 option_map decl_body (nth_error (Γ ,,, Δ') i) = Some (Some b') -> *)
                (*                 (∃ v, (pred1 Σ (skipn (S i) (Γ ,,, Δ)) b v) * (pred1 Σ (skipn (S i) (Γ ,,, Δ')) b'v)))). *)
    refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); subst P'; intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].
    intros.

    - simpl. clear predΓ'.
      induction X0; simpl; pcuic.
      ++ intros. depelim X. simpl in o.
         specialize (IHX0 _ X) as [Δf [Δfl Δfr]].
         red in p. pose proof (p _ _ o) as [Δ'' [tf [tfl tfr]]].
         exists (Δ'' ,, vass na tf).
         split. constructor. auto. eapply pred1_pred1_ctx in tfl. auto. red. auto.
         constructor. eapply pred1_pred1_ctx in tfr. auto. red. auto.
      ++ intros. depelim X. simpl in o.
         specialize (IHX0 _ X) as [Δf [Δfl Δfr]]. destruct p, o; rename_all_hyps.
         pose proof (forall_Δ' _ _ p) as [Δ''' [bf [bfl bfr]]].
         pose proof (forall_Δ'0 _ _ p0) as [Δ'' [tf [tfl tfr]]].
         exists (Δ''' ,, vdef na bf tf).
         split. constructor. auto. eapply pred1_pred1_ctx in bfl. auto. red. split.
         auto. (* Admit type annotation and both reduced in different contexts: need
                  to use "All2_local_env" to force a common target context *)
         admit.
         constructor. auto. eapply pred1_pred1_ctx in bfr. auto. red. split. auto.
         admit.

    - depelim Hr.
      all:admit.
    - all:admit.
    - all:admit.
    - depelim Hr.
      + (* Refl / Zeta in context: the hard case. We allow reducing the whole contexts on both sides *)
        specialize (X0 _ a). destruct X0 as [R [redl redr]].
        exists R.
        eapply nth_error_pred1_ctx_l in e. 2:eapply redr.
        destruct e.
        destruct p. exists (lift0 (S i) x).
        split. pcuic.
        rewrite -{1}(firstn_skipn (S i) Δ').
        rewrite -{1}(firstn_skipn (S i) R).
        pose proof (All2_local_env_length redr).
        destruct nth_error eqn:Heq; noconf e; eapply nth_error_Some_length in Heq. simpl in H.
        assert (S i = #|firstn (S i) Δ'|).
        rewrite !firstn_length_le; try lia.
        rewrite {5 6}H1.
        assert (#|firstn (S i) Δ'| = #|firstn (S i) R|).
        rewrite !firstn_length_le; try lia.
        rewrite {2}H2.
        apply (weakening_pred1_pred1 Σ (skipn (S i) Δ') (skipn (S i) R) (firstn (S i) Δ') (firstn (S i) R)); auto.
        now eapply All2_local_env_over_firstn_skipn.
      + specialize (X0 _ a) as [R [rl rr]].
        exists R. exists (tRel i). split; pcuic.
      + admit.
      + specialize (X0 _ a) as [R [rl rr]].
        exists R. exists (tRel i). split; pcuic.
    - simpl in *. pose (pred1_pred1_ctx _ _ _ _ _ Hr).
      specialize (X0 _ a). destruct X0 as [R [Rl Rr]]. exists R.
      depelim Hr.
   *)

End ParallelWeakening.

  Hint Extern 4 (pred1_ctx ?Σ ?Γ ?Γ') =>
    match goal with
      [ H : pred1_ctx Σ (Γ ,,, _) (Γ' ,,, _) |- _ ] => apply (All2_local_env_app_left H)
    end : pcuic.

Hint Resolve pred1_pred1_ctx : pcuic.

Section ParallelSubstitution.

  Inductive psubst Σ (Γ : context) : list term -> list term -> context -> Type :=
  | emptyslet : psubst Σ Γ [] [] []
  | cons_let_ass Δ s s' na t t' T :
      psubst Σ Γ s s' Δ ->
      pred1 Σ Γ Δ t t' ->
      psubst Σ Γ (t :: s) (t' :: s') (Δ ,, vass na T)
  | cons_let_def Δ s s' na t t' T :
      psubst Σ Γ s s' Δ ->
      pred1 Σ Γ Δ (subst0 s t) (subst0 s' t') ->
      psubst Σ Γ (subst0 s t :: s) (subst0 s' t' :: s') (Δ ,, vdef na t T).

  Lemma psubst_length {Σ Γ s s' Γ'} : psubst Σ Γ s s' Γ' -> #|s| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_length' {Σ Γ s s' Γ'} : psubst Σ Γ s s' Γ' -> #|s'| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_nth_error  Σ Γ s s' Δ n t :
    psubst Σ Γ s s' Δ ->
    nth_error s n = Some t ->
    ∃ decl t',
      (nth_error Δ n = Some decl) *
      (nth_error s' n = Some t') *
    match decl_body decl return Type with
    | Some d =>
      { u &
        let s2 := (skipn (S n) s) in
        let s2' := (skipn (S n) s') in
      let b := subst0 s2 d in
      let b' := subst0 s2' u in
      psubst Σ Γ s2 s2' (skipn (S n) Δ) *
      (t = b) * (t' = b') * pred1 Σ Γ (skipn (S n) Δ) t t' }%type
    | None => pred1 Σ Γ (skipn (S n) Δ) t t'
    end.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists (vass na T), t'. intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (vdef na t0 T), (subst0 s' t'). intuition auto.
      simpl. exists t'. intuition simpl; auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error_None Σ Γ s s' Δ n :
    psubst Σ Γ s s' Δ ->
    nth_error s n = None ->
    (nth_error Δ n = None) * (nth_error s' n = None).
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; intros; intuition try congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
  Qed.

  Lemma subst_skipn' n s k t : k < n -> (n - k) <= #|s| ->
    lift0 k (subst0 (skipn (n - k) s) t) = subst s k (lift0 n t).
  Proof.
    intros Hk Hn.
    assert (#|firstn (n - k) s| = n - k) by (rewrite firstn_length_le; lia).
    assert (k + (n - k) = n) by lia.
    assert (n - k + k = n) by lia.
    rewrite <- (firstn_skipn (n - k) s) at 2.
    rewrite subst_app_simpl. rewrite H H0.
    rewrite <- (commut_lift_subst_rec t _ n 0 0); try lia.
    generalize (subst0 (skipn (n - k) s) t). intros.
    erewrite <- (simpl_subst_rec _ (firstn (n - k) s) _ k); try lia.
    now rewrite H H1.
  Qed.

  Lemma skipn_app_ge {A} (l l' : list A) n : #|l| <= n -> skipn n (l ++ l') = skipn (n - #|l|) l'.
  Proof.
    induction l in l', n |- *; destruct n; simpl; auto.
    intros. depelim H.
    intros H. now rewrite [skipn _ _]IHl.
  Qed.

  Lemma skipn_app_lt {A} (l l' : list A) n : n <= #|l| -> skipn n (l ++ l') = skipn n l ++ l'.
  Proof.
    induction l in l', n |- *; destruct n; simpl; auto.
    intros. depelim H. intros H.
    now rewrite [skipn _ _]IHl.
  Qed.

  Lemma split_app3 {A} (l l' l'' : list A) (l1 l1' l1'' : list A) :
    #|l| = #|l1| -> #|l'| = #|l1'| ->
        l ++ l' ++ l'' = l1 ++ l1' ++ l1'' ->
        l = l1 /\ l' = l1' /\ l'' = l1''.
  Proof.
    intros.
    eapply app_inj_length_l in H1 as [Hl Hr]; auto.
    eapply app_inj_length_l in Hr as [Hl' Hr]; auto.
  Qed.

  (** Parallel reduction is substitutive. *)
  Lemma substitution_let_pred1 Σ Γ Δ Γ' Γ1 Δ1 Γ'1 s s' M N : wf Σ ->
    psubst Σ Γ s s' Δ ->
    #|Γ| = #|Γ1| -> #|Γ'| = #|Γ'1| ->
    All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
    pred1 Σ (Γ ,,, Δ ,,, Γ') (Γ1 ,,, Δ1 ,,, Γ'1) M N ->
    pred1 Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1) (subst s #|Γ'| M) (subst s' #|Γ'1| N).
  Proof.
    intros wfΣ Hs.
    remember (Γ ,,, Δ ,,, Γ') as Γl.
    remember (Γ1 ,,, Δ1 ,,, Γ'1) as Γr.
    intros Hlen Hlen' HΔ HΓ.
    revert HeqΓl Γ1 Δ1 Γ'1 HeqΓr Hlen Hlen' HΔ.
    revert Γ Δ s s' Hs Γ'.
    revert Γl Γr M N HΓ.
    set(P' :=
          fun (Γl Γr : context) =>
            forall (Γ Δ : context) (s s' : list term),
              psubst Σ Γ s s' Δ ->
              forall Γ' : context,
                Γl = Γ ,,, Δ ,,, Γ' ->
                forall (Γ1 : list context_decl) (Δ1 Γ'1 : context),
                  Γr = Γ1 ,,, Δ1 ,,, Γ'1 ->
                  #|Γ| = #|Γ1| ->
                  All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
                  pred1_ctx Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)).

    refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros;
      try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try pose proof (All2_local_env_length X0);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *.

    - (* Contexts *)
      red. intros. subst.
      pose proof (All2_local_env_length X1).
      rewrite !app_context_length in H |- *.
      assert (#|Γ'0| = #|Γ'1|) by lia.
      eapply All2_local_env_over_app. eapply All2_local_env_app in predΓ'. intuition pcuic.
      now rewrite !app_context_length.
      eapply All2_local_env_app in X0 as [Xl Xr].
      2:{ rewrite !app_context_length. lia. }
      induction Xr; rewrite ?subst_context_snoc; constructor; pcuic. apply IHXr.
      + depelim predΓ'. auto.
      + depelim predΓ'. auto.
      + simpl in *. lia.
      + simpl in *.
        repeat red. rewrite !Nat.add_0_r. eapply p; eauto.
      + depelim predΓ'. auto.
        simpl in *.
        repeat red. apply IHXr. simpl in *. pcuic. lia. lia.
      + depelim predΓ'. auto.
        simpl in *. destruct p0.
        split; repeat red.
        rewrite !Nat.add_0_r. simpl. eapply p0; eauto.
        rewrite !Nat.add_0_r. simpl. eapply p1; eauto.

    - (* Beta *)
      specialize (forall_Γ _ _ _ _ Hs (_ ,, _) eq_refl _ _ (_ ,, _)
                           eq_refl heq_length (f_equal S heq_length0) HΔ).
      specialize (forall_Γ0 _ _ _ _ Hs _ eq_refl _ _ _
                           eq_refl heq_length heq_length0 HΔ).
      specialize (forall_Γ1 _ _ _ _ Hs _ eq_refl _ _ _
                           eq_refl heq_length heq_length0 HΔ).
      rewrite distr_subst. simpl.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ _ _ _ Hs (_ ,, _) eq_refl _ _ (_ ,, _)
                           eq_refl heq_length (f_equal S heq_length0) HΔ).
      specialize (forall_Γ _ _ _ _ Hs _ eq_refl _ _ _
                           eq_refl heq_length heq_length0 HΔ).
      specialize (forall_Γ0 _ _ _ _ Hs _ eq_refl _ _ _
                           eq_refl heq_length heq_length0 HΔ).
      simpl. rewrite distr_subst.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ1.

    - (* Rel *)
      pose proof (psubst_length Hs) as Hlens.
      pose proof (psubst_length' Hs) as Hlens'. rewrite <- Hlens in Hlens'.
      elim (leb_spec_Set); intros Hn.
      destruct (nth_error s) eqn:Heq.
      ++ (* Let-bound variable 1in the substitution *)
         pose proof (nth_error_Some_length Heq).
         pose proof predΓ' as X.
         eapply nth_error_pred1_ctx in X as [body' [Hnth Hred]]; eauto.
         rewrite <- commut_lift_subst_rec.
         rewrite distr_subst_lift.
         pose proof X as X'.
         eapply All2_local_env_app' in X' as [Δl [Δr [Heq' Heq'']]]; subst.
         pose proof X as X'. rewrite <- app_context_assoc in X'.
         eapply All2_local_env_app in X' as [Γl' [Δr'' [[Hctx Heq'] Heq''']]].
         rewrite Hctx in X.
         eapply All2_local_env_app' in Heq''' as [Δ' [Δr' [Hctx' Heq4]]].
         subst. clear Heq'. rewrite app_context_assoc in X.
         destruct Heq4. intuition. rewrite app_context_assoc in Hctx.
         unfold app_context in Hctx; apply app_inj_length_l in Hctx. 2:lia.
         destruct Hctx; subst. rewrite !app_length in H3. rewrite H1 in H3. assert(#|Γ0| = #|Γl'|) by lia.
         clear H3.
         eapply nth_error_pred1_ctx in X as [body' [Hnth [Hred IH]]]; eauto.
         rewrite -> nth_error_app_context_ge in Hnth by lia.
         rewrite -> nth_error_app_context_lt in Hnth by lia.
         eapply psubst_nth_error in Heq as [decl [t' [[Heq'' Heq'''] Heq]]]; eauto.
         rewrite Heq'' in Hnth. noconf Hnth. simpl in H3. rewrite H3 in Heq. simpl in Heq.
         destruct Heq as [u [[[Hsub ->] ->] Hred']]. clear Hred'.
         specialize (IH Γ0 (skipn (S (i - #|Γ'0|)) Δ) []).
         forward IH. simpl. rewrite skipn_app_ge; try lia.
         rewrite skipn_app_lt; try lia. now replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia.
         specialize (IH _ _ Hsub).
         simpl in IH. rewrite <- subst_skipn'; try lia.
         rewrite <- (subst_context_length s 0 Γ'0).
         eapply weakening_pred1_0; auto.
         rewrite (subst_context_length s 0 Γ'0).
         replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia.
         apply IH.

      ++ destruct (nth_error Γ' _) eqn:HΓ'; noconf heq_option_map. simpl in H.
         destruct c as [na [b|] ty]; noconf H.
         (* Rel is a let-bound variable in Γ0, only weakening needed *)
         pose proof (All2_local_env_subst_pred X).
         eapply All2_local_env_subst in X as [Γl' [Δr'' [H]]]. intuition; subst; rename_all_hyps.
         specialize (forall_s _ _ Hs).
         eapply nth_error_None in heq_nth_error0.
         assert(eq:S i = #|s| + (S (i - #|s|))) by lia. rewrite eq.
         rewrite simpl_subst'; try lia.
         econstructor; eauto.
         rewrite nth_error_app_context_ge /= in heq_nth_error; try lia.
         rewrite nth_error_app_context_ge /= in heq_nth_error; try lia.
         rewrite nth_error_app_context_ge !subst_context_length /=; try lia.
         eapply (f_equal (option_map decl_body)) in heq_nth_error.
         simpl in heq_nth_error. rewrite <- heq_nth_error.
         f_equal. f_equal. lia.

      ++ (* Local variable from Γ'0 *)
         pose proof (All2_local_env_subst_pred X).
         eapply All2_local_env_subst in X as [Γl' [Δr'' [H]]]. intuition; subst; rename_all_hyps.
         specialize (forall_s _ _ Hs).
         assert(eq: #|Γ'0| = #|Γ'0| - S i + S i) by lia. rewrite eq.
         rewrite <- (commut_lift_subst_rec body s' (S i) (#|Γ'0| - S i) 0); try lia.
         econstructor. eauto.
         rewrite nth_error_app_context_lt /= in heq_option_map. autorewrite with wf; lia.
         rewrite nth_error_app_context_lt; try (autorewrite with wf; lia).
         rewrite nth_error_subst_context. rewrite option_map_decl_body_map_decl heq_option_map.
         simpl. do 3 f_equal. lia.

    - elim (leb_spec_Set); intros Hn.
      + pose proof (All2_local_env_subst_pred X).
        eapply All2_local_env_subst in X as [Γl' [Δr'' [H]]]. intuition; subst; rename_all_hyps.
        specialize (forall_s _ _ Hs).
        pose proof (psubst_length Hs).
        destruct nth_error eqn:Heq.
        ++ eapply psubst_nth_error in Heq as [decl [t' [[Heq'' Heq'''] Heq]]]; eauto.
           eapply psubst_length' in Hs.
           destruct decl as [na [b|] ty]; simpl in *.
           destruct Heq as [u ?]; intuition; rename_all_hyps.
           rewrite heq_nth_error0. subst t t'.
           replace (S (i - #|Γ'0|)) with (S i - #|Γ'0|) by lia.
           eapply nth_error_Some_length in heq_nth_error.
           unshelve epose proof (weakening_pred1 Σ Γ0 [] (subst_context s 0 Γ'0) _ _ _ b0); eauto.
           simpl in X. rewrite !subst_context_length in X.
           now replace (S (i - #|Γ'0|)) with (S i - #|Γ'0|) in X by lia.
           rewrite Heq'''.
           unshelve epose proof (weakening_pred1 Σ Γ0 [] (subst_context s 0 Γ'0) _ _ _ Heq); eauto.
           simpl in X. now rewrite !subst_context_length in X.
        ++ eapply psubst_nth_error_None in Heq; eauto.
           intuition; rename_all_hyps. rewrite heq_nth_error0.
           eapply psubst_length' in Hs.
           assert(#|s| = #|s'|) as -> by lia.
           eauto with pcuic.
      + eapply pred1_refl.

    - rewrite subst_iota_red.
      autorewrite with subst.
      econstructor.
      apply All2_map. solve_all. unfold on_Trel_eq, on_Trel. solve_all.

    - pose proof (subst_declared_constant _ _ _ s' #|Γ'| u wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite H0.
      econstructor; eauto.

    - simpl. eapply pred_proj with (map (subst s' #|Γ'|) args1). eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ1.
      econstructor; eauto.

    - econstructor.
      { rewrite !subst_fix_context.
        now eapply All2_local_env_subst_ctx. }
      apply All2_map. red in X0. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X0).
      eapply All2_impl; eauto. simpl. intros.
      solve_all; rename_all_hyps.
      specialize (forall_Γ Γ0 Δ Γ' eq_refl _ _ Hs).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, fix_context mfix0)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl _ _ Hs).
      rewrite subst_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite subst_fix_context -heq_length.

    - econstructor.
      { rewrite !subst_fix_context.
        now eapply All2_local_env_subst_ctx. }
      apply All2_map. red in X0. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X0).
      eapply All2_impl; eauto. simpl. intros.
      solve_all; rename_all_hyps.
      specialize (forall_Γ Γ0 Δ Γ' eq_refl _ _ Hs).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, fix_context mfix0)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl _ _ Hs).
      rewrite subst_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite subst_fix_context -heq_length.

    - specialize (forall_Γ0 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Hint Constructors psubst : pcuic.
  Hint Transparent vass vdef : pcuic.

  Lemma substitution0_pred1 {Σ : global_context} Γ M M' na A N N' : wf Σ ->
    pred1 Σ Γ M M' ->
    pred1 Σ (Γ ,, vass na A) N N' ->
    pred1 Σ Γ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vass na A] [] [M] [M'] N N' wfΣ) as H.
    forward H. constructor; auto with pcuic.
    forward H by assumption.
    now simpl in H.
  Qed.

  Lemma substitution0_let_pred1 {Σ Γ na M M' A N N'} : wf Σ ->
    pred1 Σ Γ M M' ->
    pred1 Σ (Γ ,, vdef na M A) N N' ->
    pred1 Σ Γ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redN.
    pose proof (substitution_let_pred1 Σ Γ [vdef na M A] [] [M] [M'] N N' wfΣ) as H.
    forward H. pose proof (cons_let_def Σ Γ [] [] [] na M M' A).
    rewrite !subst_empty in X.
    forward X by constructor.
    apply X, redN.
    now simpl in H.
  Qed.
End ParallelSubstitution.
