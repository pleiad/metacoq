(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICReduction PCUICCumulativity PCUICConfluence PCUICParallelReductionConfluence PCUICEquality.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq.Template Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Ltac tc := try typeclasses eauto 10.
Hint Resolve eq_universe_leq_universe : pcuic.

Section RedEq.
  Context {cf : checker_flags}.

  Global Instance refl_eq_univ φ : Reflexive (eq_universe φ) := eq_universe_refl _.
  Global Instance eq_univ_trans φ : Transitive (eq_universe φ) := eq_universe_trans _.
  Global Instance refl_leq_univ φ : Reflexive (leq_universe φ) := leq_universe_refl _.
  Global Instance leq_univ_trans φ : Transitive (leq_universe φ) := leq_universe_trans _.
  Existing Class SubstUnivPreserving.
  (* FIXME SubstUnivPreserving will need to be up-to a sigma or set of constraints at least *)
  Global Instance eq_univ_substu φ : SubstUnivPreserving (eq_universe φ).
  Admitted.
  Global Instance leq_univ_substu φ : SubstUnivPreserving (leq_universe φ).
  Admitted.

  Context (Σ : global_env_ext).

  Context {Re Rle} {refl : Reflexive Re} {refl' :Reflexive Rle}
          {trre : Transitive Re} {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle}.
  Context (inclre : forall u u' : universe, Re u u' -> Rle u u').

  Lemma red_eq_term_upto_univ_r {Γ T V U} :
    eq_term_upto_univ Re Rle T U -> red Σ Γ U V ->
    ∑ T', red Σ Γ T T' * eq_term_upto_univ Re Rle T' V.
  Proof.
    intros eq r.
    apply red_alt in r.
    induction r in T, eq |- *.
    - eapply red1_eq_term_upto_univ_r in eq as [v' [r' eq']]; eauto.
    - exists T; split; eauto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  Lemma red_eq_term_upto_univ_l {Γ u v u'} :
    eq_term_upto_univ Re Rle u u' ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Γ u' v' *
    eq_term_upto_univ Re Rle v v'.
  Proof.
    intros eq r.
    eapply red_alt in r.
    induction r in u', eq |- *.
    - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto.
    - exists u'. split; auto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  (* Lemma red_eq_term_upto_univ_back {Γ x y z} : *)
  (*   red Σ Γ x y -> *)
  (*   eq_term_upto_univ Re Rle y z -> *)
  (*   ∑ x', *)
  (*   red Σ Γ x' z * *)
  (*   eq_term_upto_univ Re Rle x x. *)
  (* Proof. *)
  (*   intros eq r. *)
  (*   eapply red_alt in r. *)
  (*   induction r in u', eq |- *. *)
  (*   - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto. *)
  (*   - exists u'. split; auto. *)
  (*   - case: (IHr1 _ eq) => T' [r' eq']. *)
  (*     case: (IHr2 _ eq') => T'' [r'' eq'']. *)
  (*     exists T''. split=>//. *)
  (*     now transitivity T'. *)
  (* Qed. *)

End RedEq.

Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2,
    Σ ;;; Γ |- M1 = N1 ->
    Σ ;;; (Γ ,, vass na M1) |- M2 <= N2 ->
    Σ ;;; Γ |- (tProd na M1 M2) <= (tProd na' N1 N2).
Proof.
  intros.
Admitted.

Lemma cumul_trans {cf:checker_flags} (Σ : global_env_ext) Γ t u v : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply cumul_alt.
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, v'1.
  split. split; auto.
  transitivity v'; auto.
  transitivity w'; auto.
  eapply leq_term_trans with nf; eauto.
Qed.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u == v -> Σ ;;; Γ |- t == v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  econstructor 2; eauto.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v == u -> Σ ;;; Γ |- v == t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

Lemma conv_alt_sym `{cf : checker_flags} (Σ : global_env_ext) Γ t u :
  wf Σ ->
  Σ ;;; Γ |- t == u -> Σ ;;; Γ |- u == t.
Proof.
  intros wfΣ X.
  induction X.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv. eapply red1_red in r. eauto. eauto.
  - eapply red_conv_conv. eapply red1_red in r. eauto. eauto.
Qed.

(* Lemma conv_conv_alt `{cf : checker_flags} (Σ : global_env_ext) Γ t u : wf Σ -> *)
(*   Σ ;;; Γ |- t = u -> Σ ;;; Γ |- u == t. *)
(* Proof. *)
(*   intros wfΣ H. destruct H. *)
(*   destruct H as (v & v' & (redv & redv') & leqv). *)
(*   intros H'. apply cumul_alt in H'. *)
(*   destruct H' as (v0 & v'0 & (redv0 & redv'0) & leqv0). *)
(*   destruct (red_confluence wfΣ redv' redv0) as [nf [nfl nfr]]. *)
(*   destruct (red_confluence wfΣ redv redv'0) as [nf' [nfl' nfr']]. *)
(*   eapply red_eq_term_upto_univ_r in leqv; tc;eauto with pcuic. *)
(*   destruct leqv as [v''0 [red'0 eq2]]. *)
(*   eapply red_eq_term_upto_univ_l in leqv0; tc;eauto with pcuic. *)
(*   destruct leqv0 as [v'1 [red'1 eq1]]. *)
(*   eapply red_conv_conv; eauto. *)
(*   eapply red_conv_conv; eauto. *)
(*   eapply red_conv_conv_inv; eauto. *)
(*   eapply red_conv_conv_inv; eauto. *)
(*   eapply conv_sym; eauto. constructor. eapply eq_term_leq_term in eq1. *)

Lemma conv_alt_red {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (t u : term) :
  Σ;;; Γ |- t == u <~> (∑ v v' : term, (red Σ Γ t v × red Σ Γ u v') × eq_term (global_ext_constraints Σ) v v').
Proof.
  split. induction 1. exists t, u; intuition auto.
  destruct IHX as [? [? [? ?]]].
  exists x, x0; intuition auto. eapply red_step; eauto.
  destruct IHX as [? [? [? ?]]].
  exists x, x0; intuition auto. eapply red_step; eauto.
  intros.
  destruct X as [? [? [[? ?] ?]]].
  eapply red_conv_conv; eauto.
  eapply red_conv_conv_inv; eauto. now constructor.
Qed.

(* Needs context conversion too *)
(* Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2, *)
(*   conv Σ Γ M1 N1 -> *)
(*   cumul Σ (Γ ,, vass na M1) M2 N2 -> *)
(*   cumul Σ Γ (tProd na M1 M2) (tProd na' N1 N2). *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)

Lemma leq_term_antisym `{cf : checker_flags} (Σ : constraints) t u :
  leq_term Σ t u -> leq_term Σ u t -> eq_term Σ t u.
Admitted.

Coercion global_ext_constraints : global_env_ext >-> constraints.

Require Import PCUICParallelReduction PCUICParallelReductionConfluence.

Lemma cumul_trans_red `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
  ∑ l o r, red Σ Γ t l *
           red Σ Γ u o *
           red Σ Γ v r *
           leq_term Σ l o * leq_term Σ o r.
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, nf, v'1.
  repeat split.
  transitivity v'; auto.
  transitivity w; auto.
  transitivity w'; auto.
  eapply leq_term_trans with nf; eauto.
  eapply leq_term_trans with nf; eauto.
Qed.

Unset Universe Minimization ToSet.
Lemma clos_rt_eq_term `{cf : checker_flags} {Σ : global_env_ext} :
  inclusion (clos_refl_trans (eq_term Σ)) (eq_term Σ).
Proof.
  intros x y. induction 1. auto. apply eq_term_refl. now apply eq_term_trans with y.
Qed.

Lemma clos_rt_eq_leq_term `{cf : checker_flags} {Σ : global_env_ext} :
  inclusion (clos_refl_trans (eq_term Σ)) (leq_term Σ).
Proof.
  intros x y. induction 1. auto. apply eq_term_leq_term. now apply eq_term_trans with y. apply leq_term_refl.
  now apply leq_term_trans with y.
Qed.

Lemma clos_rt_leq_term `{cf : checker_flags} {Σ : global_env_ext} :
  inclusion (clos_refl_trans (leq_term Σ)) (leq_term Σ).
Proof.
  intros x y. induction 1. auto. apply leq_term_refl. now apply leq_term_trans with y.
Qed.

Lemma leq_term_upto_univ_confluent `{cf : checker_flags} {Σ : global_env_ext} :
  diamond (eq_term Σ).
Proof.
  intros x y. intros.
  exists x. split. now apply eq_term_sym. now apply eq_term_sym.
Qed.

Lemma All_All2_All2_mix {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' :
  All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' ->
  ∑ l''', All2 P l' l''' * All2 P l'' l'''.
Proof.
  intros H; induction H in l', l'' |- *;
  intros H' H''; depelim H'; depelim H''; try solve [econstructor; eauto; constructor].
  simpl. destruct (IHAll _ _ H' H''). destruct (p _ _ q r).
  exists (x1 :: x0). split; constructor; intuition auto.
Qed.

(* Lemma All_All2_All2_mix_hetero {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' : *)
(*   All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' -> *)
(*   ∑ l''', All2 P l' l''' * All2 P l'' l'''. *)
(* Proof. *)
(*   intros H; induction H in l', l'' |- *; *)
(*   intros H' H''; depelim H'; depelim H''; try solve [econstructor; eauto; constructor]. *)
(*   simpl. destruct (IHAll _ _ H' H''). destruct (p _ _ q r). *)
(*   exists (x1 :: x0). split; constructor; intuition auto. *)
(* Qed. *)

Lemma eq_term_upto_univ_incl `{cf:checker_flags} Re Rle : inclusion Re Rle -> inclusion (eq_term_upto_univ Re Re)
                                                                    (eq_term_upto_univ Re Rle).
Proof. intros. intros x y H. eapply eq_term_upto_univ_leq in H; eauto. Qed.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma All_inst {A : Type} {C : Type} {l : list C} {P : A -> C -> Type} :
  All (fun x : C => forall a : A, P a x) l -> forall x : A, All (P x) l.
Proof.
  intros. eapply All_impl; eauto.
Qed.

Hint Extern 10 => solve [reflexivity] : core.

Local Tactic Notation "join" uconstr(x) := exists x; intuition (constructor; eauto).

Lemma diamond_All2_diamond {A} (R : relation A) : diamond R -> diamond (All2 R).
Proof.
  intros HR l l' l'' Hl Hl'.
  induction Hl in l'', Hl' |- ; depelim Hl'.
  join [].
  destruct (IHHl _ Hl') as [tl' [? ?]].
  destruct (HR _ _ _ r r0) as [hd' [? ?]].
  join (hd' :: tl').
Qed.

Definition first_level (u : universe) :=
  match u with
  | NEL.sing a => fst a
  | NEL.cons a _ => fst a
  end.

Lemma make_first_level : forall l, first_level (Universe.make l) = l.
Proof. by case. Qed.

(* Lemma first_level_make : forall l, Universe.make (first_level u) = l. *)
(* Proof. by case. Qed. *)

Lemma diamond_map {A B} (R : relation A) (f : B -> A) (g : A -> B) :
  (forall x, x = f (g x)) ->
  diamond R -> diamond (on_Trel R f).
Proof.
  intros Hf HR l l' l'' Hl Hl'. red in Hl, Hl'.
  destruct (HR _ _ _ Hl Hl') as [hd' [? ?]].
  rewrite (Hf hd') in r, r0.
  join (g hd').
Qed.

Lemma All2_impl_hetero {A B C D : Type} (P : A -> B -> Type) (Q : C -> D -> Type) l l' (f : A -> C) (g : B -> D) :
  (forall x y, P x y -> Q (f x) (g y)) ->
  All2 P l l' ->
  All2 (fun x y => Q (f x) (g y)) l l'.
Proof.
  intros HP. induction 1; constructor; auto.
Qed.

(* Lemma All_impl_hetero {A B C D : Type} (P : A -> B -> Type) (Q : C -> D -> Type) l l' (f : A -> C) (g : B -> D) : *)
(*   (forall x y, P x y -> Q (f x) (g y)) -> *)
(*   All P l -> *)
(*   All2 (fun x y => Q (f x) (g y)) l l'. *)
(* Proof. *)
(*   intros HP. induction 1; constructor; auto. *)
(* Qed. *)

Definition diamond_on {A} (R : A -> A -> Type) (x : A) := forall y z, R x y -> R x z -> joinable R y z.

Lemma eq_term_upto_univ_diamomd :
  forall (Re Rle : universe -> universe -> Type),
    inclusion Re Rle ->
    diamond Re ->
    diamond Rle ->
    diamond (eq_term_upto_univ Re Rle).
Proof.
  intros Re Rle Rincl hRe hRle x.
  fold (diamond_on (eq_term_upto_univ Re Rle) x).
  induction x in Re, Rle, Rincl, hRe, hRle |- * using term_forall_list_ind;
    intros y z eq eq'.
  all: dependent destruction eq; dependent destruction eq'.
  all: try solve [ eexists; split; constructor ].
  Ltac t := intuition (constructor; eauto).

  - do 2 eapply All_inst with Re in X.
    do 3 eapply All_inst in X; eauto.
    eapply All_All2_All2_mix in X; [|eapply a|eapply a0].
    destruct X as [nf [H H']]. exists (tEvar n nf).
    split; constructor; auto.

  - destruct (hRle _ _ _ e e0).
    join (tSort x).

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [dom [? ?]].
    specialize (IHx2 Re _ ltac:(eauto) hRe hRle _ _ eq2 eq'2) as [codom [? ?]].
    join (tProd na' dom codom).

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [dom [? ?]].
    specialize (IHx2 Re _ ltac:(eauto) hRe hRle _ _ eq2 eq'2) as [codom [? ?]].
    join (tLambda na' dom codom).

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [def [? ?]].
    specialize (IHx2 Re Re ltac:(eauto) hRe hRe _ _ eq2 eq'2) as [ty [? ?]].
    specialize (IHx3 Re _ ltac:(eauto) hRe hRle _ _ eq3 eq'3) as [body [? ?]].
    join (tLetIn na' def ty body).

  - specialize (IHx1 Re _ ltac:(eauto) hRe hRle _ _ eq1 eq'1) as [fn [? ?]].
    specialize (IHx2 Re Re ltac:(eauto) hRe hRe _ _ eq2 eq'2) as [arg [? ?]].
    join (tApp fn arg).

  - eapply diamond_All2_diamond in hRle.
    destruct (hRle _ _ _ a a0) as [u'' ?].
    (* eexists (tConst s (map first_level u'')); t. *)
    (* This is wrong: we need specific Rie Rile relations for comparision
       of universes instances which are levels only *)
    todo "universe instances".

  - todo "universe instances".
  - todo "universe instances".

  - specialize (IHx1 Re Re ltac:(eauto) hRe hRe _ _ eq1 eq'1) as [fn [? ?]].
    specialize (IHx2 Re Re ltac:(eauto) hRe hRe _ _ eq2 eq'2) as [arg [? ?]].
    red in X.
    do 2 eapply All_inst with Re in X. do 3 eapply All_inst in X; eauto.

    eapply (All_impl (Q:=fun x => diamond_on (relation_conjunction (on_Trel eq fst)
                                                                   (on_Trel (eq_term_upto_univ Re Re) snd)) x)) in X.
    2:{ rewrite /diamond_on /= //.
        move=> [an t] H [ax ty] [az tz].
        rewrite /on_Trel => /= [] /= [] /= -> eq3 [] /= -> eq4.
        destruct (H ty tz eq3 eq4).
        join (az, x) => /=. }
    eapply All_All2_All2_mix in X as [brs [? ?]].
    2:{ eapply All2_impl. eapply a. t. }
    2:{ eapply All2_impl. eapply a0. t. }
    join (tCase (ind, par) fn arg brs) => //.

  - specialize (IHx Re Re ltac:(eauto) hRe hRe _ _ eq eq') as [arg [? ?]].
    join (tProj s arg).

  - red in X.
    eapply (All_impl (Q:=fun x =>
                           diamond_on (fun x y =>
                                         (eq_term_upto_univ Re Re (dtype x) (dtype y)) *
                                         (eq_term_upto_univ Re Re (dbody x) (dbody y)) *
                                         (rarg x = rarg y)) x))%type in X.
    2:{ rewrite /diamond_on /= //.
        move=> [na ty' body' arg'] /= [Hty Hbod] y z.
        move=> [[]] eqty eqbod -> [[]] eqty' eqbod' eq.
        destruct (Hty _ Re ltac:(eauto) hRe hRe _ _ eqty eqty') as [dtype [? ?]].
        destruct (Hbod _ Re ltac:(eauto) hRe hRe _ _ eqbod eqbod') as [dbody [? ?]].
        join {| dname := dname y; dtype := dtype; dbody := dbody; rarg := rarg z |} => /=. }
    eapply All_All2_All2_mix in X as [mfix [? ?]]; cycle 1.
    eapply All2_impl; [eapply a|]; intuition auto; intuition auto.
    eapply All2_impl; [eapply a0|]; intuition auto; intuition auto.
    join (tFix mfix n) => //.

  - red in X.
    eapply (All_impl (Q:=fun x =>
                           diamond_on (fun x y =>
                                         (eq_term_upto_univ Re Re (dtype x) (dtype y)) *
                                         (eq_term_upto_univ Re Re (dbody x) (dbody y)) *
                                         (rarg x = rarg y)) x))%type in X.
    2:{ rewrite /diamond_on /= //.
        move=> [na ty' body' arg'] /= [Hty Hbod] y z.
        move=> [[]] eqty eqbod -> [[]] eqty' eqbod' eq.
        destruct (Hty _ Re ltac:(eauto) hRe hRe _ _ eqty eqty') as [dtype [? ?]].
        destruct (Hbod _ Re ltac:(eauto) hRe hRe _ _ eqbod eqbod') as [dbody [? ?]].
        join {| dname := dname y; dtype := dtype; dbody := dbody; rarg := rarg z |} => /=. }
    eapply All_All2_All2_mix in X as [mfix [? ?]]; cycle 1.
    eapply All2_impl; [eapply a|]; intuition auto; intuition auto.
    eapply All2_impl; [eapply a0|]; intuition auto; intuition auto.
    join (tCoFix mfix n) => //.
Qed.

Lemma leq_universe_sup_l `{cf : checker_flags} u v φ : leq_universe φ u (Universe.sup u v).
  todo "Universes specification".
Admitted.

Lemma leq_universe_sup_r `{cf : checker_flags} u v φ : leq_universe φ v (Universe.sup u v).
  todo "Universes specification".
Admitted.

Lemma eq_term_upto_univ_diamond `{cf : checker_flags} {Σ : global_env_ext} :
  diamond (eq_term Σ).
Proof.
  eapply eq_term_upto_univ_diamomd. firstorder.
  red. intros x y z eq eq'. exists x. split; auto using eq_universe_sym.
  red. intros x y z eq eq'. exists x. split; auto using eq_universe_sym.
Qed.

Lemma leq_term_upto_univ_diamond `{cf : checker_flags} {Σ : global_env_ext} :
  diamond (leq_term Σ).
Proof.
  (* This corresponds to the fact that for universes `l, u, v`,
     if `l <= u` /\ `l <= v` then `u <= max(u, v)` `v <= max(u, v)` *)
  eapply eq_term_upto_univ_diamomd. apply: (eq_universe_leq_universe _).
  red. intros x y z eq eq'. exists x. split; auto using eq_universe_sym.
  red. intros x y z eq eq'. exists (Universe.sup y z).
  split; auto using leq_universe_sup_l, leq_universe_sup_r.
Qed.

Lemma commutes_eqterm_red1 {cf : checker_flags} {Σ : global_env_ext} Γ : commutes (eq_term Σ) (red1 Σ Γ).
Proof.
  intros x y z.
  intros.
  eapply red1_eq_term_upto_univ_l in H; tc; eauto.
Qed.

Lemma commutes_leqterm_red1 {cf : checker_flags} {Σ : global_env_ext} Γ : commutes (leq_term Σ) (red1 Σ Γ).
Proof.
  intros x y z.
  intros.
  eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe.
Qed.

Generalizable Variables A B R S T.

Definition rel_cart {A B} (R : relation A) (S : relation B) : relation (A * B) :=
  fun x y => (R x.1 y.1 * S x.2 y.2)%type.
Hint Unfold rel_cart : core.

Instance rel_cart_refl `{HR : Reflexive A R} `{HS : Reflexive B T} :
  Reflexive (rel_cart R T).
Proof. auto. Qed.

Instance rel_cart_trans `{HR : Transitive A R} `{HS : Transitive B T} :
  Transitive (rel_cart R T).
Proof. firstorder auto. Qed.

Instance rel_cart_sym `{HR : Symmetric A R} `{HS : Symmetric B T} :
  Symmetric (rel_cart R T).
Proof. firstorder auto. Qed.

Definition leq_term_rel {cf : checker_flags} Σ : relation (context * term) :=
  rel_cart eq (leq_term Σ).

Definition eq_term_rel {cf : checker_flags} Σ : relation (context * term) :=
  rel_cart eq (eq_term Σ).

Lemma commutes_leqterm_pred1 {cf : checker_flags} {Σ : global_env_ext} :
  commutes (@pred1_rel Σ) (leq_term_rel Σ).
Proof.
  intros x y z.
  intros.
  (* eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe. *)
Admitted.

Lemma commutes_eqterm_pred1 {cf : checker_flags} {Σ : global_env_ext} :
  commutes (@pred1_rel Σ) (eq_term_rel Σ).
Proof.
  intros x y z.
  intros.
  (* eapply red1_eq_term_upto_univ_l in H; tc; eauto. intros. now eapply eq_universe_leq_universe. *)
Admitted.

Definition red1_or_leq {cf : checker_flags} (Σ : global_env_ext) (Γ : context) :=
  relation_disjunction (leq_term Σ) (red1 Σ Γ).

Definition red1_leq {cf : checker_flags} (Σ : global_env_ext) : relation (context * term) :=
  relation_disjunction (@red1_rel_alpha Σ) (leq_term_rel Σ).

Definition red1_eq {cf : checker_flags} (Σ : global_env_ext) : relation (context * term) :=
  relation_disjunction (@red1_rel_alpha Σ) (eq_term_rel Σ).

Definition pred1_leq {cf : checker_flags} (Σ : global_env_ext) :=
  relation_disjunction (@pred1_rel Σ) (leq_term_rel Σ).

Definition pred1_eq {cf : checker_flags} (Σ : global_env_ext) :=
  relation_disjunction (@pred1_rel Σ) (eq_term_rel Σ).

Instance leq_term_refl {cf : checker_flags} Σ : Reflexive (leq_term Σ).
Proof. intros x; apply leq_term_refl. Defined.

Instance leq_term_trans {cf : checker_flags} Σ : Transitive (leq_term Σ).
Proof. intros x; apply leq_term_trans. Defined.

Instance eq_term_refl {cf : checker_flags} Σ : Reflexive (eq_term Σ).
Proof. intros x; apply eq_term_refl. Defined.

Instance eq_term_trans {cf : checker_flags} Σ : Transitive (eq_term Σ).
Proof. intros x; apply eq_term_trans. Defined.

Lemma pred1_leq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (pred1_leq Σ).
Proof.
  intros wfΣ.
  apply confluent_union. tc. intros x. red. apply pred1_refl.
  apply commutes_leqterm_pred1. apply (diamond_pred1_rel wfΣ).
  move=> [Γ x] [Δ y] [Ψ z] [] /= -> leqxy [] /= -> leqyz.
  destruct (leq_term_upto_univ_diamond leqxy leqyz) as [nf [redl redr]].
  exists (Ψ, nf); firstorder.
Qed.

Lemma pred1_eq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (pred1_eq Σ).
Proof.
  intros wfΣ.
  apply confluent_union. tc. intros x. red. apply pred1_refl.
  apply commutes_eqterm_pred1. apply (diamond_pred1_rel wfΣ).
  move=> [Γ x] [Δ y] [Ψ z] [] /= -> leqxy [] /= -> leqyz.
  destruct (eq_term_upto_univ_diamond leqxy leqyz) as [nf [redl redr]].
  exists (Ψ, nf); firstorder.
Qed.

Hint Unfold leq_term_rel : core.

Lemma red1_leq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (red1_leq Σ).
Proof.
  intros wfΣ.
  notypeclasses refine (fst (sandwich _ _ _ _) _).
  3:eapply pred1_leq_confluence; eauto.
  intros [ctx t] [ctx' t'].
  rewrite /red1_leq /pred1_leq /=.
  move=> [l|[/= <- r]].
  - left. now eapply red1_rel_alpha_pred1_rel.
  - right. auto.
  - intros [Γ x] [Δ y] [l|r].
    eapply clos_rt_disjunction_left.
    now apply pred1_rel_red1_rel_alpha.
    eapply clos_rt_disjunction_right.
    now constructor.
Qed.

Lemma red1_eq_confluence {cf : checker_flags} (Σ : global_env_ext) : wf Σ -> confluent (red1_eq Σ).
Proof.
  intros wfΣ.
  notypeclasses refine (fst (sandwich _ _ _ _) _).
  3:eapply pred1_eq_confluence; eauto.
  intros [ctx t] [ctx' t'].
  rewrite /red1_leq /pred1_leq /=.
  move=> [l|[/= <- r]].
  - left. now eapply red1_rel_alpha_pred1_rel.
  - right. red; auto.
  - intros [Γ x] [Δ y] [l|r].
    eapply clos_rt_disjunction_left.
    now apply pred1_rel_red1_rel_alpha.
    eapply clos_rt_disjunction_right.
    now constructor.
Qed.

Lemma red1_incl_red1_leq {cf : checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> forall x y, red Σ Γ x y -> clos_refl_trans (red1_leq Σ) (Γ, x) (Γ, y).
Proof.
  intros wfΣ.
  intros x y rxy.
  eapply red_alt in rxy.
  induction rxy. constructor. red. left. left. split; auto.
  constructor 2.
  now transitivity (Γ, y).
Qed.

Lemma leq_incl_red1_leq {cf : checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> forall x y, leq_term Σ x y -> clos_refl_trans (red1_leq Σ) (Γ, x) (Γ, y).
Proof.
  intros wfΣ.
  intros x y rxy. constructor. right. red; auto.
Qed.

Lemma cumul_trans_red_eqterm `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> eq_term Σ t v ->
  ∑ l o r, red Σ Γ t l *
           red Σ Γ u o *
           red Σ Γ v r *
           leq_term Σ l o * leq_term Σ o r.
Proof.
  intros wfΣ X X0.
  intros.
  eapply cumul_alt in X as [t0 [u0 [[redl redr] eq]]].
  eapply cumul_alt in X0 as [u1 [v0 [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [unf [nfl nfr]].
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [t1 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v1 [red'1 eq1]].
  exists t1, unf, v1.
  repeat split.
  transitivity t0; auto.
  transitivity u0; auto.
  transitivity v0; auto. eapply eq2. eapply eq1.
Qed.

Definition rel_comp {A} (R S : relation A) :=
  fun x z => ∑ y, R x y * S y z.

Lemma commutes_clos_rt_one {A} (R S : relation A) :
  commutes R S -> commutes (clos_refl_trans R) S.
Proof.
  intros Hcom x y z Hxy Hxz.
  eapply clos_rt_rt1n_iff in Hxy.
  induction Hxy in z, Hxz |- *.
  - exists z. split; auto.
  - destruct (Hcom _ _ _ r Hxz) as [j [jl jr]].
    specialize (IHHxy _ jl).
    destruct IHHxy as [w [szw Rjw]].
    exists w. split; auto. transitivity j => //. now constructor.
Qed.

Lemma commutes_sym {A} (R S : relation A) :
  commutes R S -> commutes S R.
Proof.
  intros Hcom x y z Hxy Hxz.
  destruct (Hcom _ _ _ Hxz Hxy) as [j [jl jr]].
  exists j. split; auto.
Qed.

Lemma commutes_clos_rt {A} (R S : relation A) :
  commutes R S -> commutes (clos_refl_trans R) (clos_refl_trans S).
Proof.
  intros. apply commutes_clos_rt_one.
  eapply commutes_sym. eapply commutes_clos_rt_one.
  now eapply commutes_sym.
Qed.

(* Lemma clos_rt_disjunction_mon {A} (R S : relation A) : *)
(*   relation_equivalence (clos_refl_trans (relation_disjunction R S)) *)
(*                        (relation_disjunction (clos_refl_trans R) (clos_refl_trans S)). *)
(* Proof. *)
(*   split. *)
(*   induction 1. *)
(*   destruct r. *)
(*   - left. now constructor. *)
(*   - right; now constructor. *)
(*   - left. now constructor 2. *)
(*   - destruct IHX1. *)

Definition commutes_horizontal {A} (R S : relation A) :=
  inclusion (rel_comp R S) (rel_comp S R).

Lemma commutes_horizontal_red_leq {cf : checker_flags} (Σ : global_env_ext) Γ :
  commutes_horizontal (leq_term Σ) (red Σ Γ).
Proof.
  intros x z. move=> [y [Hl Hr]].
  red.
  eapply red_eq_term_upto_univ_r in Hl. all:tc. 3:eapply Hr.
  2:eapply (eq_universe_leq_universe _).
  eapply Hl.
Qed.

Lemma commutes_horizontal_leq_red1_alpha_rels {cf : checker_flags} {Σ : global_env_ext} :
  commutes_horizontal (leq_term_rel Σ) (@red1_rel_alpha Σ).
Proof.
  intros [Γ x] [Δ z]. move=> [[Ψ y] [[/= -> Hl] Hr]].
  destruct Hr as [Hr|[Hr|Hr]].
  - destruct Hr as [Hr ->].
    eapply red1_eq_term_upto_univ_r in Hl as [mid [rmid leqmid]]. all:tc.
    3:eapply Hr.
    2:eapply eq_universe_leq_universe.
    exists (Δ, mid). split; firstorder.
  - destruct Hr as [Hr ->].
    exists (Δ, x). split; firstorder auto.
  - destruct Hr as [Hr ->].
    exists (Δ, x). split; firstorder auto.
Qed.

Hint Resolve rt_refl rt_step : core.

Lemma commutes_horizontal_clos_rt_right {A} (R S : relation A) :
  commutes_horizontal R S ->
  commutes_horizontal R (clos_refl_trans S).
Proof.
  intros HRS.
  intros x z [y [Hl Hr]].
  apply clos_rt_rt1n_iff in Hr.
  induction Hr in x, Hl |- *.
  - exists x. split; auto.
  - destruct (HRS x y) as [mid [Smid Rmid]]. exists x0; auto.
    destruct (IHHr _ Rmid) as [mid' [Smid' Rmid']].
    exists mid'; intuition auto.
    now eapply rt_trans with mid.
Qed.

Lemma commutes_horizontal_clos_rt {A} (R S : relation A) :
  commutes_horizontal R S ->
  commutes_horizontal (clos_refl_trans R) (clos_refl_trans S).
Proof.
  intros HRS.
  eapply commutes_horizontal_clos_rt_right.
  intros x z [y [Hl Hr]].
  eapply clos_rt_rtn1_iff in Hl.
  induction Hl in z, Hr.
  - now exists z.
  - destruct (HRS y z) as [mid [Smid Rmid]].
    now exists z0.
    destruct (IHHl _ Smid) as [mid' [Smid' Rmid']].
    exists mid'; intuition auto.
    now eapply rt_trans with mid.
Qed.

Lemma commutes_horizontal_clos_rt_disj {A} (R S : relation A) :
  commutes_horizontal S R ->
  inclusion (clos_refl_trans (relation_disjunction R S))
            (rel_comp (clos_refl_trans R) (clos_refl_trans S)).
Proof.
  intros Hcom x y Hxy.
  (* eapply commutes_clos_rt in Hcom. *)
  eapply clos_rt_rt1n_iff in Hxy.
  induction Hxy.
  - exists x. split. now constructor 2. now constructor 2.
  - destruct IHHxy as [y' [yy' y'z]].
    destruct r.
    * exists y'. split; auto.
      eapply clos_rt_rt1n_iff. eapply rt1n_trans. eauto. now eapply clos_rt_rt1n_iff.
    * eapply commutes_horizontal_clos_rt_right in Hcom.
      destruct (Hcom x y') as [mid [Rmid Smid]].
      now exists y.
      exists mid; intuition auto.
      now eapply rt_trans with y'.
Qed.

Lemma clos_rt_refl_trans {A} {R : relation A} `{Reflexive A R} `{Transitive A R} :
  relation_equivalence (clos_refl_trans R) R.
Proof.
  split.
  induction 1; auto. now transitivity y.
  intros. auto.
Qed.

Definition red_leq {cf : checker_flags} Σ Γ := fun x y => clos_refl_trans (red1_leq Σ) (Γ, x) (Γ, y).

Instance red_leq_trans {cf : checker_flags} (Σ : global_env_ext) Γ :
  Transitive (red_leq Σ Γ).
Proof. unfold red_leq. intros x y z Hxy Hyz. now transitivity (Γ, y). Qed.

Definition red_comp_leq `{cf : checker_flags} (Σ : global_env_ext) Γ t u :=
  ∑ t', red Σ Γ t t' * leq_term Σ t' u.

Lemma clos_rt_red1_leq_spec `{cf : checker_flags} {Σ : global_env_ext} {t u} :
  wf Σ -> clos_refl_trans (red1_leq Σ) t u -> red_comp_leq Σ t.1 t.2 u.2.
Proof.
  intros.
  eapply commutes_horizontal_clos_rt_disj in X0 as [[Δ mid] [r leq]].
  exists mid.
  split; auto. eapply clos_rt_red1_alpha_out in r as [Hctx Ht]=>//. simpl in *.
  - now eapply red_alt.
  - unshelve eapply (fst (clos_rt_refl_trans _ _)) in leq; tc.
    red in leq. red in leq. simpl in leq. intuition auto.
  - eapply commutes_horizontal_leq_red1_alpha_rels.
Qed.

Lemma red_leq_spec `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  wf Σ -> red_leq Σ Γ t u <~> red_comp_leq Σ Γ t u.
Proof.
  intros. split.
  - intros X0; eapply commutes_horizontal_clos_rt_disj in X0 as [[Δ mid] [r leq]].
    exists mid.
    split; auto. eapply clos_rt_red1_alpha_out in r as [Hctx Ht]=>//. simpl in *.
    * now eapply red_alt.
    * unshelve eapply (fst (clos_rt_refl_trans _ _)) in leq; tc.
      red in leq. red in leq. simpl in leq. intuition auto.
    * eapply commutes_horizontal_leq_red1_alpha_rels.

  - intros X0. destruct X0 as [v [redtv leqvu]].
    eapply rt_trans with (Γ, v).
    eapply clos_rt_disjunction_left.
    now eapply clos_rt_red1_red1_rel_alpha, red_alt.
    eapply clos_rt_disjunction_right.
    constructor. auto.
Qed.

(* Lemma cumul_alt_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : *)
(*    wf Σ -> *)
(*    Σ ;;; Γ |- t <= u -> *)
(*    ∑ o o', red Σ Γ t o * *)
(*            leq_term Σ o o' * *)
(*            red Σ Γ u o'. *)
(* Proof. *)
(*   intros. *)
(*   eapply cumul_alt in X0 as [v [v' [[redl redr] leq]]]. *)
(*   exists v'. split; red; auto. *)
(*   - transitivity (Γ, v). apply clos_rt_disjunction_left. *)
(*     eapply red_alt in redl. now apply clos_rt_red1_red1_rel_alpha. *)
(*     constructor. right. red; auto. *)
(*   - eapply clos_rt_disjunction_left. *)
(*     apply red_alt in redr. now eapply clos_rt_red1_red1_rel_alpha. *)
(* Qed. *)

Lemma confluence_clos_rt_red1_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  wf Σ ->
  clos_refl_trans (red1_leq Σ) (Γ, t) (Γ, u) ->
  clos_refl_trans (red1_leq Σ) (Γ, t) (Γ, v) ->
  ∑ nf, red_leq Σ Γ u nf * red_leq Σ Γ v nf.
Proof.
  intros wfΣ tu tv.
  destruct (red1_leq_confluence wfΣ tu tv) as [[Δ nf] [redl redr]].
  exists nf; auto.
  eapply clos_rt_red1_leq_spec in redl=>//.
  eapply clos_rt_red1_leq_spec in redr=>//.
  simpl in *.
  split; now eapply red_leq_spec.
Qed.

Lemma commutes_eqterm_red {cf : checker_flags} {Σ : global_env_ext} {Γ} : commutes (eq_term Σ) (clos_refl_trans (red1 Σ Γ)).
Proof.
  eapply commutes_sym, commutes_clos_rt_one, commutes_sym.
  eapply commutes_eqterm_red1.
Qed.

Lemma commutes_leqterm_red {cf : checker_flags} {Σ : global_env_ext} {Γ} : commutes (leq_term Σ) (clos_refl_trans (red1 Σ Γ)).
Proof.
  eapply commutes_sym, commutes_clos_rt_one, commutes_sym.
  eapply commutes_leqterm_red1.
Qed.

(* Lemma commutes_leqterm_red' {cf : checker_flags} {Σ : global_env_ext} {Γ} : commutes (leq_term Σ) (red Σ Γ). *)
(* Proof. *)
(*   eapply commutes_sym. *)
(*   apply commutes_proper. *)
(*  commutes_clos_rt_one, commutes_sym. *)
(*   eapply commutes_leqterm_red1. *)
(* Qed. *)

Lemma cumul_trans_red_leqterm `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
  ∑ o mid o', red Σ Γ t o *
       leq_term Σ o mid *
       red Σ Γ u mid *
       leq_term Σ mid o' *
       red Σ Γ v o'.
Proof.
  intros wfΣ X X0.
  intros.
  eapply cumul_alt in X as [t' [u' [[ol or] leq]]] => //.
  eapply cumul_alt in X0 as [u'' [v' [[o'l o'r] leq']]] => //.
  destruct (red_confluence wfΣ or o'l) as [unf [tl rr]].
  assert (∑ tnf, red Σ Γ t' tnf * leq_term Σ tnf unf).
  apply commutes_horizontal_red_leq. exists u'; auto.
  destruct X as [tnf [ttnf tnfunf]].
  destruct (commutes_leqterm_red leq' (equiv _ _ (red_alt Σ _ _ _) rr)) as [v'nf [? ?]].
  eapply red_alt in c.
  exists tnf, unf, v'nf.
  intuition auto. now transitivity t'.
  now transitivity u''.
  now transitivity v'.
Qed.

(* Lemma cumul_trans_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} : wf Σ -> *)
(*   Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v -> *)
(*   ∑ mid, red_leq Σ Γ t mid * *)
(*          red Σ Γ u mid * *)
(*          red_geq Σ Γ v mid. *)
(*          red_leq Σ Γ u o' * *)
(*        red Σ Γ u mid * *)
(*        leq_term Σ mid o' * *)
(*        red Σ Γ v o'. *)
(* Proof. *)
(*   intros wfΣ X X0. *)
(*   intros. *)
(*   eapply cumul_alt in X as [t' [u' [[ol or] leq]]] => //. *)
(*   eapply cumul_alt in X0 as [u'' [v' [[o'l o'r] leq']]] => //. *)
(*   destruct (red_confluence wfΣ or o'l) as [unf [tl rr]]. *)
(*   assert (∑ tnf, red Σ Γ t' tnf * leq_term Σ tnf unf). *)
(*   apply commutes_horizontal_red_leq. exists u'; auto. *)
(*   destruct X as [tnf [ttnf tnfunf]]. *)
(*   destruct (commutes_leqterm_red leq' (equiv _ _ (red_alt Σ _ _ _) rr)) as [v'nf [? ?]]. *)
(*   eapply red_alt in c. *)
(*   exists tnf, unf, v'nf. *)
(*   intuition auto. now transitivity t'. *)
(*   now transitivity u''. *)
(*   now transitivity v'. *)
(* Qed. *)

Lemma red_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ} t u :
  wf Σ ->
  red Σ Γ t u -> red_leq Σ Γ t u.
Proof.
  intros wfΣ tu. eapply red_alt in tu.
  red. induction tu; try solve [econstructor; eauto].
  constructor. red. left. left. auto.
Qed.

Lemma leq_red_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ} t u :
  wf Σ ->
  leq_term Σ t u -> red_leq Σ Γ t u.
Proof.
  intros wfΣ tu.
  red.
  constructor. red. right. red; auto.
Qed.

Lemma cumul_trans_red_conv_aux `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t ->
  (∃ v : term, red_leq Σ Γ t v × red Σ Γ u v).
Proof.
  intros wfΣ X X0.
  eapply cumul_alt in X as [v [v' [[tv uv'] leq]]].
  eapply cumul_alt in X0 as [w [w' [[tw uw'] leq']]].
  destruct (red_confluence wfΣ uv' tw) as [tj [? ?]].
  exists tj. intuition auto.
  - transitivity v; auto. now apply red_red_leq.
    transitivity v'. now eapply leq_red_leq.
    now eapply red_red_leq.
  - transitivity v'; auto.
Qed.


(*
   t0  <=  u0
   |       |
   |       |
   v       v
   t'      u
   |       |
   |       |
   t'' <= u''
*)

Lemma fill_le `{cf : checker_flags} {Σ : global_env_ext} {Γ t t' u u'} :
  wf Σ ->
  leq_term Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
  ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * leq_term Σ t'' u''.
Proof.
  intros wfΣ tu tt' uu'.
  pose proof tu as tu2.
  eapply red_eq_term_upto_univ_l in tu. 9:eapply tt'. all:tc. 2:eapply eq_universe_leq_universe.
  destruct tu as [u'' [uu'' t'u'']].
  destruct (red_confluence wfΣ uu' uu'') as [unf [ul ur]].
  eapply red_eq_term_upto_univ_r in t'u''. 9:eapply ur. all:tc. 2:eapply eq_universe_leq_universe.
  destruct t'u'' as [t'' [t't'' t''unf]].
  exists t'', unf. intuition auto.
Qed.

Instance eq_term_sym@{i j} {cf : checker_flags} φ :
  Symmetric@{i j} (eq_term_upto_univ (eq_universe φ) (eq_universe φ)) | (Symmetric (eq_term_upto_univ _ _)).
Proof.
  apply eq_term_upto_univ_sym.
  intros x y; eapply eq_universe_sym.
Qed.

Hint Unfold eq_term : typeclass_instances.

Instance leq_refl@{i j} (Re Rle : crelation@{i j} _) :
  Reflexive Re -> Reflexive Rle -> Reflexive@{i j} (eq_term_upto_univ Re Rle).
Proof. intros ** x. now apply eq_term_upto_univ_refl. Qed.

Instance leq_trans@{i j} (Re Rle : crelation@{i j} _) :
  Transitive Re -> Transitive Rle -> Transitive@{i j} (eq_term_upto_univ Re Rle).
Proof. intros ** x. now apply eq_term_upto_univ_trans. Qed.

Instance incl Re Rle :
  inclusion Re Rle -> inclusion (eq_term_upto_univ Re Re) (eq_term_upto_univ Re Rle).
Proof. intros H x y. eapply eq_term_upto_univ_leq. auto. Qed.

Lemma eq_context_upto_nth_error Re Γ Γ' n :
  Reflexive Re ->
  eq_context_upto Re Γ Γ' ->
  match nth_error Γ n with
  | Some d => ∑ d', (nth_error Γ' n = Some d') * eq_decl_upto Re d d'
  | None => nth_error Γ' n = None
  end.
Proof.
  intros Rerefl.
  induction Γ in Γ', n |- *.
  - move=> H. depelim H =>//. now rewrite nth_error_nil.
  - case: n => //=.
    * move=> H. depelim H.
      eexists; intuition eauto. constructor; simpl; auto. constructor.
      eexists; intuition eauto. constructor; simpl; auto.
      constructor; simpl; auto.
    * move=> n eqc. depelim eqc.
      eapply IHΓ; eauto.
      eapply IHΓ; eauto.
Qed.

Section RhoLeqTerm.
  Lemma rho_leq_term {Σ : global_env_ext}
        {Re Rle} {refl : Reflexive Re} {refl' :Reflexive Rle}
        {trre : Transitive Re} {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle}
        {inclre : inclusion Re Rle} Γ Γ' t u :
    eq_term_upto_univ Re Rle t u ->
    eq_context_upto Re (rho_ctx Σ Γ) (rho_ctx Σ Γ') ->
    eq_term_upto_univ Re Rle (rho Σ (rho_ctx Σ Γ) t) (rho Σ (rho_ctx Σ Γ') u).
  Proof.
    intros eqt eqctx.
    move t before Σ. move Γ before t. move Γ' before Γ. move eqctx before Γ'. move u before t.
    move eqt before u.
    induction t using term_forall_list_ind in u, Re, Rle, eqt, Γ, Γ', eqctx,
                                              refl, refl', trre, trle, inclre |- *; depelim eqt.
    all:cbn;try (constructor; auto).
    all:solve_all.
    - generalize (eq_context_upto_nth_error n _ eqctx).
      case: (nth_error (rho_ctx Σ Γ) n) => //=.
      move => [na [b|] ty] /= [d' [-> eqd]]; depelim eqd; simpl in *.
      depelim r. rewrite H. apply lift_eq_term_upto_univ. eapply incl; auto.
      depelim r. rewrite H. reflexivity.
      move=> -> /=. reflexivity.

    - specialize (IHt2 _ Re Rle eqt2 (Γ ,, vass n t1) (Γ' ,, vass na' a')).
      simpl in IHt2. rewrite !app_context_nil_l in IHt2.
      eapply IHt2; auto. constructor. eapply IHt1; auto.
      auto.

    - specialize (IHt2 _ Re Rle eqt2 (Γ ,, vass n t1) (Γ' ,, vass na' ty')).
      simpl in IHt2. rewrite !app_context_nil_l in IHt2.
      eapply IHt2; auto. constructor. eapply IHt1; auto.
      auto.

    - specialize (IHt3 _ Re Rle eqt3 (Γ ,, vdef n t1 t2) (Γ' ,, vdef na' t' ty')).
      simpl in IHt3. rewrite !app_context_nil_l in IHt3.
      transitivity (((rho Σ (vdef na' (rho Σ (rho_ctx Σ Γ') t') (rho Σ (rho_ctx Σ Γ') ty') :: rho_ctx Σ Γ') u') {0
     := rho Σ (rho_ctx Σ Γ) t1})). eapply PCUICSubstitution.subst_eq_term_upto_univ.
      eapply IHt3; auto. constructor. eapply IHt1; auto.
      auto.
  Admitted.

  Lemma red_confluence_upto {Γ t t' u v} :
    leq_term Σ t t' ->
    red Σ Γ t u -> red Σ Γ t' v ->
    ∑ v' v'', red Σ Γ u v' * red Σ Γ v v'' * leq_term Σ v' v''.
  Proof.
    move=> H H'. apply red_alt in H. apply red_alt in H'.
    destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]].
    apply red_alt in redl; apply red_alt in redr.
    exists nf; intuition auto.
  Qed.



(* Lemma red_leq_same `{cf : checker_flags} {Σ : global_env_ext} {Γ x y} : *)
(*   wf Σ -> *)
(*   red1 Σ Γ x y -> leq_term Σ y x -> False. *)
(* Proof. *)
(*   intros wfΣ xy yx. *)
(*   induction y in Γ, x, xy, yx |- * using term_forall_list_ind. *)
(*   all: depelim yx; try solve [depelim xy; solve_discr]. *)
(*   Ltac t' := firstorder eauto using eq_term_leq_term. *)
(*   - depelim xy. admit. *)
(*     solve_discr. *)
(*   - depelim xy; solve_discr. *)
(*     admit. *)
(*   - depelim xy; solve_discr; t'. *)
(*   - depelim xy; solve_discr; t'. *)
(*   - depelim xy; solve_discr. t'. *)

(* eapply eq_universe_refl. *)
(*   Set Typeclasses Debug Verbosity 2. *)
(*   Fail typeclasses eauto. *)



(* (*   induction xy; intros; auto. *) *)


(* (*   eapply red_alt in *) *)
(* (* xy. *) *)
(* (*   eapply clos_rt_rt1n_iff in xy. *) *)
(* (*   induction xy. intros. reflexivity. *) *)
(* (*   intros zx. *) *)

(* Lemma confluence_upto_leq `{cf : checker_flags} {Σ : global_env_ext} {Γ x y z} : *)
(*   wf Σ -> *)
(*   red Σ Γ x z -> red Σ Γ y z -> leq_term Σ x y -> eq_term Σ x y. *)
(* Proof. *)
(*   intros wfΣ xz. *)
(*   eapply red_alt in xz. *)
(*   eapply clos_rt_rt1n_iff in xz. *)
(*   induction xz in y |- *. *)
(*   intros yx xy. *)
(*   eapply leq_term_antisym. auto. *)
(*   induction xy; constructor; auto. eapply All2_sym; eauto. tc. *)
(*   Set Typeclasses Debug Verbosity 2. *)
(*   Fail typeclasses eauto. *)

(*

   t   <=   u    <=   t           t0 <= t1 /\ t0 -> t' /\ t1 -> t' -> t0 = t1
   |        |         |
   |        |         |
   v        v         v
   t0  <=   u'  <=   t1
    \               /
     \            /
      \          /
       \        /
        v      v
           t'


   t   <=   u    <=   t
   |        |         |
   |        |         |
   v        v         v
   t0  <=   u0  <=   t1
    \      |         /
     \     |       /
      \  <=U->    /
       \   |    /
        v  v   v
           t'


*)

Lemma cumul_trans_red_conv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
Proof.
  move=> wfΣ tu ut.
  eapply cumul_trans_red_leqterm in ut; eauto. clear tu.
  destruct ut as [t0 [u0 [t1 [[[[tt0 t0u0] uu0] u0t1] tt1]]]].
  destruct (red_confluence wfΣ tt0 tt1) as [t' [t0t' t1t']].

  eapply red_alt in t0t'.
  destruct (commutes_leqterm_red t0u0 t0t') as [u0' [? ?]].
  eapply red_alt in c.
  eapply red_alt in t0t'.

(*

   t  <=  u
   |      |
   |      |
   v      v
   t' =>  u'

*)



Corollary confluence {cf : checker_flags} {Σ : global_env_ext} Γ Δ Δ' t u t' u' :
  wf Σ ->
  leq_term Σ t t' ->
  pred1 Σ Γ Δ t t' ->
  pred1 Σ Γ Δ' u u' ->
  pred1 Σ Δ (rho_ctx Σ Γ) t' (rho Σ (rho_ctx Σ Γ) t) *
  pred1 Σ Δ' (rho_ctx Σ Γ) u' (rho Σ (rho_ctx Σ Γ) u) *
  leq_term Σ (rho Σ (rho_ctx Σ Γ) t) (rho Σ (rho_ctx Σ Γ) u).
Proof.
  intros wfΣ **.
  split. eapply triangle in X0. eapply triangle in X. all:eauto.
  induction H.

Qed.

Lemma fill_le' `{cf : checker_flags} {Σ : global_env_ext} {Γ t t' u u'} :
  wf Σ ->
  leq_term Σ t u -> red Σ Γ t t' -> red Σ Γ u u' -> (leq_term Σ t' u' + (leq_term Σ u' t' -> False)).
Proof.
  intros wfΣ tu tt' uu'.


  pose proof tu as tu2.
  eapply red_eq_term_upto_univ_r in uu'. 9:eapply tu2. all:tc. 2:eapply eq_universe_leq_universe.
  destruct uu' as [t'' [t't'' t''unf]].
  assert (leq_term
  intros.

  exists t'', unf. intuition auto.
Qed.


  destruct (fill_le wfΣ u0t1 c t1t') as [u0'' [t'' [[u0'u0'' t't''] lequ0t'']]].


  destruct (commutes_horizontal_red_leq (Σ:=Σ) (Γ := Γ) (x:=u0) (y:=t')) as [u0'' [? ?]].
  exists t1. auto.

  Lemma leq_term_gen_antisym {cf : checker_flags} φ x y y' :
    leq_term φ x y -> leq_term φ y' x -> (eq_term φ x y * eq_term φ y' x).
  Proof.
  Admitted.

  assert(red_leq Σ Γ u0 t').
  { transitivity t0. eapply leq_red_leq.



  destruct (red_confluence wfΣ uu0 uu1) as [u' [? ?]].
  destruct (fill_le wfΣ leqt0u0 r r1) as [t'' [u0'' [[? ?] leqt''u0'']]].
  destruct (fill_le wfΣ lequ1t1 r2 r0) as [u1' [t1'' [[? ?] lequ1't1'']]].

(*

   t   <=   u    <=   t
   |        |         |
   |        |         |
   v        v         v
   t0  <= u0 u1 <=   t1
    \ \   \ /       /
     \ \   u       /
      \ v         /
       \ x       /
        v Λ     v
            t'
*)

Lemma cumul_trans_red_conv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} : wf Σ ->
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
Proof.
  move=> wfΣ tu ut.
  eapply cumul_alt in tu.
  eapply cumul_alt in ut.
  destruct tu as [t0 [u0 [[tt0 uu0] leqt0u0]]].
  destruct ut as [u1 [t1 [[uu1 tt1] lequ1t1]]].
  destruct (red_confluence wfΣ tt0 tt1) as [t' [? ?]].
  destruct (red_confluence wfΣ uu0 uu1) as [u' [? ?]].
  destruct (fill_le wfΣ leqt0u0 r r1) as [t'' [u0'' [[? ?] leqt''u0'']]].
  destruct (fill_le wfΣ lequ1t1 r2 r0) as [u1' [t1'' [[? ?] lequ1't1'']]].

(*
   t'      u'     if red_leq t' u0'' /\ red u' u0'' /\ red t' t'1 /\ red_leq u' t'1 ->
   | \     |
   |  \    |      red_leq x y /\ red z y -> red x x' /\ leq x' y /\ red x 
   v    \  v
   t'' <=  u0''

   and

   t'      u'
   |     / |
   |   /   |
   v /     v
   t'1 >= u1'

*)


  eapply red_eq_term_upto_univ_l in r. 9:eapply leqt0u0. all:tc. 2:eapply eq_universe_leq_universe.
  destruct r. intuition.
  eapply red_eq_term_upto_univ_l in leqtt1. all:tc. 3:eapply r0. 2:eapply eq_universe_leq_universe.
  destruct leqtt1. intuition.

  destruct (red_confluence wfΣ tt0 tu1) as [unf' [? ?]].




  eapply red_eq_term_upto_univ_r in leqt0u0. all:tc. 3:eapply r. 2:eapply eq_universe_leq_universe.



  destruct (cumul_trans_red_conv_aux wfΣ tu ut) as [nf0 [lnf0 rnf0]].
  destruct (cumul_trans_red_conv_aux wfΣ ut tu) as [nf1 [lnf1 rnf1]].
  eapply red_leq_spec in lnf0. red in lnf0.


  destruct (confluence_clos_rt_red1_leq wfΣ rnf0 lnf1) as [tnf' [tl rr]].
  destruct (confluence_clos_rt_red1_leq wfΣ lnf0 rnf1) as [tnf'' [tl' rr']].
  eapply conv_alt_red.
  assert(red_leq Σ Γ t tnf').
  transitivity nf0; auto.
  assert(red_leq Σ Γ u tnf').
  transitivity nf1; auto.
  assert(red_leq Σ Γ t tnf'').
  transitivity nf0; auto.
  assert(red_leq Σ Γ u tnf'').
  transitivity nf1; auto.
  eapply red_leq_spec in X => //.
  destruct X as [tred [redtnf leqtnf]].
  eapply red_leq_spec in X0 => //.
  destruct X0 as [tred' [redtnf' leqtnf']].
  eapply red_leq_spec in X1 => //.
  destruct X1 as [tred2 [redtnf2 leqtnf2]].
  eapply red_leq_spec in X2 => //.
  destruct X2 as [tred3 [redtnf3 leqtnf3]].
  destruct (red_confluence wfΣ redtnf redtnf2).
  destruct (red_confluence wfΣ redtnf' redtnf3).
  destruct p, p0.
  exists x, x0.
  split; auto.
  split. now transitivity tred. now transitivity tred'.
  apply leq_term_antisym.



  






  exists tnf', tnf'; intuition auto.
  trq



  destruct (cumul_trans_red_leqterm wfΣ X X0) as [tnf [mid [unf ?]]].
  intuition auto.
  eapply cumul_alt in X as [v [v' [[tv uv'] leq]]].
  pose proof (commutes_leqterm_red

  destruct (red_confluence wfΣ b b5) as [tj [? ?]].
  destruct (red_confluence wfΣ b1 a1) as [uj [? ?]].
  destruct (red_confluence wfΣ a0 b5) as [t'j [? ?]].



  clear r1.


  destruct (confluence_clos_rt_red1_leq wfΣ r r3) as [tnf' [tl rr]].
  destruct (confluence_clos_rt_red1_leq wfΣ r0 r2) as [unf' [ul ur]].
  pose proof (transitivity r tl).
  pose proof (transitivity r0 tl).
  pose proof (transitivity r2 ur).
  pose proof (transitivity r3 ur).
  destruct (confluence_clos_rt_red1_leq wfΣ X1 X4) as [nf [nfl nfr]].
  destruct (confluence_clos_rt_red1_leq wfΣ X2 X3) as [nf' [nfl' nfr']].
  pose proof (transitivity

  eapply red_leq_spec in X1 => //.
  eapply red_leq_spec in X2 => //.
  eapply red_leq_spec in X3 => //.
  eapply red_leq_spec in X4 => //.
  destruct X1 as [tred [redtnf leqtnf]].
  destruct X2 as [ured [redunf lequnf]].
  destruct X3 as [tred' [redtnf' leqtnf']].
  destruct X4 as [ured' [redunf' lequnf']].
  eapply conv_alt_red.
  exists tred, ured. split; auto.
  split.


  eapply red_leq_spec in r.
  eapply red_leq_spec in r0.
  eapply red_leq_spec in r2.
  eapply red_leq_spec in r3. all:auto.





  eapply cumul_alt_red_leq in X as [o [ol or]] => //.
  eapply cumul_alt_red_leq in X0 as [o' [o'l o'r]] => //.



  pose proof (transitivity or tl).
  pose proof (transitivity or tl).

  eapply red_leq_spec in tl => //.
  eapply red_leq_spec in rr => //.
  eapply red_leq_spec in rr => //.


  destruct (confluence_clos_rt_red1_leq wfΣ ul tl) as [nfl [tnfl tnfr]].
  destruct (confluence_clos_rt_red1_leq wfΣ ur rr) as [nfr [onfl o'nfr]].




  destruct (red_confluence wfΣ r r1) as [onf [? ?]].
  destruct (red_confluence wfΣ r0 r2) as [o'nf [? ?]].


  destruct (red1_leq_confluence wfΣ or o'l) as [[Γ' u'] [uo uo']].
  destruct (red1_leq_confluence wfΣ ol o'r) as [[Γ'' u''] [uo2 uo'2]].
  apply conv_alt_red.
  destruct (red1_leq_confluence wfΣ uo uo2) as [[Δ u'u''] [? ?]].
  destruct (red1_leq_confluence wfΣ uo' uo'2) as [[Δ' o'u''] [? ?]].

  assert (clos_refl_trans (red1_leq Σ) (Γ, t) (Δ, u'u'')).
  { transitivity (Γ, o). auto. transitivity (Γ', u'); auto. }
  assert (clos_refl_trans (red1_leq Σ) (Γ, t) (Δ', o'u'')).
  { transitivity (Γ, o'). auto. transitivity (Γ', u'); auto. }
  assert (clos_refl_trans (red1_leq Σ) (Γ, u) (Δ', o'u'')).
  { transitivity (Γ, o'). auto. transitivity (Γ', u'); auto. }
  assert (clos_refl_trans (red1_leq Σ) (Γ, u) (Δ, u'u'')).
  { transitivity (Γ, o). auto. transitivity (Γ', u'); auto. }

  eapply clos_rt_red1_leq_spec in X as [ou' [oou' leq1]].
  eapply clos_rt_red1_leq_spec in X0 as [o'u' [o'ou' leq2]].
  eapply clos_rt_red1_leq_spec in X1 as [ou'' [oou'' leq3]].
  eapply clos_rt_red1_leq_spec in X2 as [o'u''2 [o'ou'' leq4]].
  all:auto.
  simpl in *.
  destruct (red_confluence wfΣ oou' oou'') as [onf [onfl onfr]].
  destruct (red_confluence wfΣ oou' oou'') as [onf [onfl onfr]].


Abort.
(* Lemma clos_red1_leq_samectx {cf : checker_flags} (Σ : global_env_ext) Γ Δ t u : *)
(*   clos_refl_trans (red1_leq Σ) (Γ, t) (Δ, u) -> *)
(*   clos_refl_trans  *)
(*   Γ = Δ. *)
(* Proof. *)
(*   intros H. generalize_eqs H. induction H; simplify_dep_elim. *)
(*   red in r. destruct r. red in r. intuition auto. *)


(*   eapply (red_leq_spec wfΣ) in uo as [tnf [ttnf let_]] => //. *)
(*   eapply red_leq_spec in X0 as [unf [uunf leu]] => //. *)
(*   assert (red_leq Σ Γ t u''). *)
(*   red. econstructor 3; eauto. admit. *)
(*   assert (red_leq Σ Γ u u''). *)
(*   red. econstructor 3; eauto. admit. *)
(*   eapply red_leq_spec in X as [tnf' [ttnf' let']] => //. *)
(*   eapply red_leq_spec in X0 as [unf' [uunf' leu']] => //. *)
(*   destruct (red_confluence wfΣ ttnf ttnf') as [t' [? ?]]. *)
(*   destruct (red_confluence wfΣ uunf uunf') as [u2 [? ?]]. *)
(*   exists t', u2. *)
(*   intuition auto. *)
(*   transitivity tnf; auto. *)
(*   transitivity unf; auto. *)


Existing Class wf.

Lemma cumul_conv_alt `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u} :
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
Proof.
  intros l r.
Admitted.

Lemma conv_conv_alt `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ t u :
  Σ ;;; Γ |- t = u <~> Σ ;;; Γ |- t == u.
Proof.
  split; induction 1. apply cumul_conv_alt in b; auto.
  constructor; constructor. now eapply eq_term_leq_term.
  eapply eq_term_leq_term; now apply eq_term_sym.
  constructor. econstructor 2; eauto. apply IHX.
  econstructor 3. 2:eauto. apply IHX.
  constructor. econstructor 3. 2:eauto. apply IHX.
  econstructor 2; eauto. apply IHX.
Qed.

Section Inversions.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext) (wfΣ : wf Σ).

  Lemma conv_trans_reg : forall Γ u v w,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = w ->
                            Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma cumul_App_r {Γ f u v} :
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tApp f u <= tApp f v.
  Proof.
    intros h.
    apply conv_conv_alt in h => //. induction h.
    - eapply cumul_refl. constructor.
      + apply leq_term_refl.
      + assumption.
    -  eapply cumul_red_l ; try eassumption.
       econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_r {Γ f x y} :
    Σ ;;; Γ |- x = y ->
    Σ ;;; Γ |- tApp f x = tApp f y.
  Proof.
    intros h.
    eapply conv_conv_alt => //.
    apply conv_conv_alt in h => //. induction h.
    - constructor. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_l:
    forall {Γ na na' A1 A2 B},
      Σ ;;; Γ |- A1 = A2 ->
                 Σ ;;; Γ |- tProd na A1 B = tProd na' A2 B.
  Proof.
    intros Γ na na' A1 A2 B h.
    eapply conv_conv_alt. tc.
    apply conv_conv_alt in h. induction h.
    - constructor. constructor.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_r  :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 = B2 ->
                              Σ ;;; Γ |- tProd na A B1 = tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    eapply conv_conv_alt.
    apply conv_conv_alt in h. induction h.
    - constructor. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma cumul_Prod_r :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
                              Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - eapply cumul_refl. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_cumul_l :
    forall Γ u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- u <= v.
  Proof.
    intros Γ u v [? ?].
    assumption.
  Qed.

  Lemma conv_refl' :
    forall leq Γ t,
      conv leq Σ Γ t t.
  Proof.
    intros leq Γ t.
    destruct leq.
    - cbn. constructor. apply conv_refl'.
    - cbn. constructor. apply cumul_refl'.
  Qed.

  Lemma conv_sym :
    forall Γ u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = u.
  Proof.
    intros Γ u v [h1 h2].
    econstructor ; assumption.
  Qed.

  Lemma conv_conv :
    forall {Γ leq u v},
      ∥ Σ ;;; Γ |- u = v ∥ ->
                   conv leq Σ Γ u v.
  Proof.
    intros Γ leq u v h.
    destruct leq.
    - assumption.
    - destruct h as [[h1 h2]]. cbn.
      constructor. assumption.
  Qed.

  Lemma eq_term_conv :
    forall {Γ u v},
      eq_term (global_ext_constraints Σ) u v ->
      Σ ;;; Γ |- u = v.
  Proof.
    intros Γ u v e.
    constructor.
    - eapply cumul_refl.
      eapply eq_term_leq_term. assumption.
    - eapply cumul_refl.
      eapply eq_term_leq_term.
      eapply eq_term_sym.
      assumption.
  Qed.

  Lemma conv_trans :
    forall Γ u v w,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = w ->
                            Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma conv_trans' :
    forall leq Γ u v w,
      conv leq Σ Γ u v ->
      conv leq Σ Γ v w ->
      conv leq Σ Γ u w.
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1, h2. constructor.
      eapply conv_trans ; eassumption.
    - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma red_conv_l :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ u v.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
      + simpl. constructor.
        eapply cumul_red_l.
        * eassumption.
        * eapply cumul_refl'.
  Qed.

  Lemma red_conv_r :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ v u.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
      + simpl. constructor.
        eapply cumul_red_r.
        * eapply cumul_refl'.
        * assumption.
  Qed.

  Lemma conv_Prod :
    forall leq Γ na A1 A2 B1 B2,
      Σ ;;; Γ |- A1 = A2 ->
                 conv leq Σ (Γ,, vass na A1) B1 B2 ->
                 conv leq Σ Γ (tProd na A1 B1) (tProd na A2 B2).
  Proof.
    intros [] Γ na A1 A2 B1 B2 h1 h2.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply conv_trans.
      + eapply conv_Prod_r. eassumption.
      + eapply conv_Prod_l. eassumption.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply cumul_trans. auto.
      + eapply cumul_Prod_r. eassumption.
      + eapply conv_cumul_l. eapply conv_Prod_l. assumption.
  Qed.

  Lemma cumul_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tCase indn p u brs <= tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    eapply conv_conv_alt in h.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto.
    - eapply cumul_red_l ; eauto.
      constructor. assumption.
    - eapply cumul_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma cumul_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tProj p u <= tProj p v.
  Proof.
    intros Γ p u v h.
    eapply conv_conv_alt in h.
    induction h.
    - eapply cumul_refl. constructor. assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_l :
    forall {Γ f g x},
      Σ ;;; Γ |- f = g ->
                 Σ ;;; Γ |- tApp f x = tApp g x.
  Proof.
    intros Γ f g x h.
    eapply conv_conv_alt.
    apply conv_conv_alt in h. induction h.
    - constructor. constructor.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tCase indn p u brs = tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto.
    - eapply conv_alt_red_l ; eauto.
      constructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma conv_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- tProj p u = tProj p v.
  Proof.
    intros Γ p u v h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - eapply conv_alt_refl. constructor. assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_l :
    forall Γ na A b na' A',
      Σ ;;; Γ |- A = A' ->
                 Σ ;;; Γ |- tLambda na A b = tLambda na' A' b.
  Proof.
    intros Γ na A b na' A' h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - eapply conv_alt_refl. constructor.
      + assumption.
      + eapply eq_term_refl.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b = b' ->
                             Σ ;;; Γ |- tLambda na A b = tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    eapply conv_conv_alt in h.
    apply conv_conv_alt.
    induction h.
    - eapply conv_alt_refl. constructor.
      + eapply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u <= u' ->
                                 Σ ;;; Γ |- tLetIn na ty t u <= tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - eapply cumul_refl. constructor.
      all: try eapply eq_term_refl.
      assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b <= b' ->
                             Σ ;;; Γ |- tLambda na A b <= tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    induction h.
    - eapply cumul_refl. constructor.
      + eapply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u <= v ->
                         Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Lambda_r. assumption.
  Qed.

  Lemma cumul_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B <= B' ->
                         Σ ;;; Δ |- it_mkProd_or_LetIn Γ B <= it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Prod_r. assumption.
  Qed.

End Inversions.
