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

Program Definition add0 (n : nat) :=
  match n return n + 0 = n with
  | 0 => _
  | S m => _
  end.
Next Obligation.
todo "".
Defined.
MetaCoq Quote Definition bar := Eval lazy in add0.
Print bar.

Definition even (n : nat) :=
  match n with
  | 0 => true
  | S m => false
  end.

MetaCoq Quote Definition foo := Eval lazy in (even (unk nat)).
Print foo.
Definition pd :=
  match foo with
  | tCase _ p _ _ => p
  | _ => mk_predicate [] [] [] foo
  end.
Definition foo' := Eval lazy in eval_compute_cheat foo Monomorphic_ctx.
Print foo'.
Definition a := inst_case_predicate_context
MetaCoq Unquote Definition foo'' := foo'.
Print foo''.