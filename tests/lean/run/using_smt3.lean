open tactic

lemma ex1 : let x := 1 in ∀ y, x = y → y = 1 :=
by using_smt $ smt_tactic.intros >> get_local `x >>= (fun a, trace a)

meta def fail_if_success {α : Type} (t : smt_tactic α) : smt_tactic unit :=
do (some _) ← optional t | skip,
   failed

def my_smt_config : smt_config :=
{ pre_cfg := { zeta := tt } }

lemma ex2 : let x := 1 in ∀ y, x = y → y = 1 :=
by using_smt_with my_smt_config $ smt_tactic.intros >> fail_if_success (get_local `x) >> return ()
