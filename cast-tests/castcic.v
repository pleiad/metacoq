From MetaCoq.Template Require Import TemplateMonad config utils Loader.
From MetaCoq.PCUIC Require Import PCUICAst PCUICToTemplate PCUICPretty PCUICSN PCUICTyping PCUICNormal.
From MetaCoq.SafeChecker Require Import PCUICErrors SafeTemplateChecker PCUICWfEnvImpl PCUICWfEnv PCUICSafeChecker PCUICSafeReduce.
From Coq Require Import Nat.
Import MCMonadNotation.

Global Existing Instance PCUICSN.default_normalizing.

Axiom castcic_unk : forall (A : Type), A.
Axiom castcic_err : forall (A : Type), A.
Axiom castcic_cast : forall (A B : Type), A -> B.

Notation unk := castcic_unk.
Notation err := castcic_err.
Notation cast := castcic_cast.

Program Definition eval_compute_cheat (cf := default_checker_flags)
  {nor : normalizing_flags}
  (p : Ast.Env.program) φ : Ast.term
  := let p' := trans_program p in
    let tm := reduce_term RedFlags.default
    canonical_abstract_env_ext_impl
    {| referenced_impl_env_ext  := (p'.1 , φ);
       referenced_impl_ext_wf  := (todo "wf") |}
    [] p'.2 (todo "welltyped") in
    PCUICToTemplate.trans tm.

Definition even (n : nat) :=
  match n with
  | 0 => True
  | S m => False
  end.

Definition idM := forall A, A -> A.
MetaCoq Quote Recursively Definition foo := (unk idM).
Definition bar := Eval lazy in eval_compute_cheat foo Monomorphic_ctx.
Print bar.
MetaCoq Unquote Definition baz := bar.
Print baz.

MetaCoq Quote Definition foo := Eval lazy in (even (unk nat)).
MetaCoq Quote Recursively Definition foo' := (add0 (err nat)).
Definition foo'' := Eval lazy in trans_program (foo'.1, foo).
Print foo''.
Definition pd :=
  match foo''.2 with
  | tCase _ p _ _ => p
  | _ => mk_predicate [] [] [] (tRel 1000)
  end.
Definition mk_pred_lambda p :=
  it_mkLambda_or_LetIn (inst_case_predicate_context p) (preturn p).
Eval lazy in (mk_pred_lambda pd).
Definition baz := Eval lazy in eval_compute_cheat foo' Monomorphic_ctx.
Print baz.
MetaCoq Unquote Definition baz' := baz.
Print baz'.