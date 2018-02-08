/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
prelude
import init.meta.tactic init.meta.simp_tactic init.meta.interactive
import init.meta.congr_lemma init.meta.match_tactic
import init.meta.ttactic
open tactic

meta def conv (α : Type) :=
tactic α

meta def conv.goal := tactic.goal

meta instance : goal_type conv.goal :=
⟨id, id⟩
section
local attribute [reducible] conv
meta instance : monad conv := by apply_instance
meta instance : monad_fail conv := by apply_instance
meta instance : alternative conv := by apply_instance
meta instance : monad_except _ conv := by apply_instance
meta def conv.goal_cfg {m : Type → Type} [has_monad_lift_t tactic m] : goal_cfg m :=
{ goal_ty := conv.goal,
  goal_ty_is_goal_type := by apply_instance,
  ..tactic.goal_cfg }
meta instance : monad_tactic conv :=
{ goal_cfg := conv.goal_cfg }
end

namespace conv
meta def convert (c : conv unit) (lhs : expr) (rel : name := `eq) : tactic (expr × expr) :=
do lhs_type   ← infer_type lhs,
   rhs        ← mk_meta_var lhs_type,
   new_target ← mk_app rel [lhs, rhs],
   new_g      ← mk_meta_var new_target,
   gs         ← get_goals,
   set_goals [new_g],
   c,
   try $ any_goals reflexivity,
   n          ← num_goals,
   when (n ≠ 0) (fail "convert tactic failed, there are unsolved goals"),
   set_goals gs,
   rhs        ← instantiate_mvars rhs,
   new_g      ← instantiate_mvars new_g,
   return (rhs, new_g)

meta def lhs : conv expr :=
do (_, lhs, rhs) ← target_lhs_rhs,
   return lhs

meta def rhs : conv expr :=
do (_, lhs, rhs) ← target_lhs_rhs,
   return rhs

meta def update_lhs (new_lhs : expr) (h : expr) : conv unit :=
do transitivity,
   rhs >>= unify new_lhs,
   exact h,
   t ← target >>= instantiate_mvars,
   change t

meta def change (new_lhs : expr) : conv unit :=
do (r, lhs, rhs) ← target_lhs_rhs,
   new_target ← mk_app r [new_lhs, rhs],
   tactic.change new_target

meta def skip : conv unit :=
reflexivity

meta def whnf : conv unit :=
lhs >>= tactic.whnf >>= change

meta def dsimp (s : option simp_lemmas := none) (u : list name := []) (cfg : dsimp_config := {}) : conv unit :=
do s ← match s with
       | some s := return s
       | none   := simp_lemmas.mk_default
       end,
   l ← lhs,
   s.dsimplify u l cfg >>= change

private meta def congr_aux : list congr_arg_kind → list expr → tactic (list expr × list expr)
| []      []      := return ([], [])
| (k::ks) (a::as) := do
  (gs, largs) ← congr_aux ks as,
  match k with
  | congr_arg_kind.fixed            := return $ (gs, a::largs)
  | congr_arg_kind.fixed_no_param   := return $ (gs, largs)
  | congr_arg_kind.eq               := do
      a_type  ← infer_type a,
      rhs     ← mk_meta_var a_type,
      g_type  ← mk_app `eq [a, rhs],
      g       ← mk_meta_var g_type,
      return (g::gs, a::rhs::g::largs)
  | congr_arg_kind.cast             := return $ (gs, a::largs)
  | _                               := fail "congr tactic failed, unsupported congruence lemma"
  end
| ks      as := fail "congr tactic failed, unsupported congruence lemma"

meta def congr : conv unit :=
do (r, lhs, rhs) ← target_lhs_rhs,
   guard (r = `eq),
   let fn   := lhs.get_app_fn,
   let args := lhs.get_app_args,
   cgr_lemma ← mk_congr_lemma_simp fn (some args.length),
   g::gs ← get_goals,
   (new_gs, lemma_args) ← congr_aux cgr_lemma.arg_kinds args,
   let g_val := cgr_lemma.proof.mk_app lemma_args,
   unify g g_val,
   set_goals $ new_gs ++ gs,
   return ()

meta def funext : conv unit :=
iterate $ do
  (r, lhs, rhs) ← target_lhs_rhs,
  guard (r = `eq),
  (expr.lam n _ _ _) ← return lhs,
  tactic.applyc `funext,
  intro n,
  return ()

end conv
