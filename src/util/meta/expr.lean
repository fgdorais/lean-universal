-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .name
import .level

namespace expr

meta def mk_list (l : level) (t : expr) : list expr → expr
| [] := expr.app (expr.const `list.nil [l]) t
| (x::xs) := let e := mk_list xs in expr.mk_app (expr.const `list.cons [l]) [t,x,e]

meta def prop_sort : expr := sort level.zero

meta def type_sort : expr := sort level.one

meta def mk_local (pfx : name) : name → binder_info → expr → expr :=
λ n b t, expr.local_const (pfx ++ n) n b t

meta def mk_locals (pfx : name) (b : binder_info) : list (name × expr) → list expr
| [] := []
| ((n,t)::nts) := mk_local pfx n b t :: mk_locals nts

meta def mk_num_locals (pfx root : name) (base : nat) : list expr → binder_info → list expr :=
λ ls bi, let ls : list (name × expr) := list.zip (mk_num_names root base ls.length) ls in mk_locals pfx bi ls

meta def mk_sub_locals (pfx root : name) (base : nat) : list expr → binder_info → list expr :=
λ ls bi, let ls : list (name × expr) := list.zip (mk_sub_names root base ls.length) ls in mk_locals pfx bi ls

meta def mk_vars : list nat → list expr := list.map mk_var

meta def mk_num_vars (len : nat) (fst : nat := 0) : list expr := mk_vars $ list.range' len fst

meta def mk_sort : level → expr := expr.sort

meta def mk_sorts : list level → list expr := list.map expr.sort

meta def bind_lambdas : expr → list expr → expr
| e [] := e
| e (p::ps) := bind_lambda (bind_lambdas e ps) p

meta def bind_pis : expr → list expr → expr
| e [] := e
| e (p::ps) := bind_pi (bind_pis e ps) p

meta def num_pis {elab : opt_param bool tt} (root : name) (base : nat) (bi : binder_info) : list (expr elab) → expr elab → expr elab
| [] e := e
| (t::ts) e := expr.pi (mk_num_name root (base + ts.length)) bi t $ num_pis ts e

meta def num_lambdas {elab : opt_param bool tt} (root : name) (base : nat) (bi : binder_info) : list (expr elab) → expr elab → expr elab
| [] e := e
| (t::ts) e := expr.lam (mk_num_name root (base + ts.length)) bi t $ num_lambdas ts e

meta def sub_pis {elab : opt_param bool tt} (root : name) (base : nat) (bi : binder_info) : list (expr elab) → expr elab → expr elab
| [] e := e
| (t::ts) e := expr.pi (mk_sub_name root (base + ts.length)) bi t $ sub_pis ts e

meta def sub_lambdas {elab : opt_param bool tt} (root : name) (base : nat) (bi : binder_info) : list (expr elab) → expr elab → expr elab
| [] e := e
| (t::ts) e := expr.lam (mk_sub_name root (base + ts.length)) bi t $ sub_lambdas ts e

meta def sorts {elab : opt_param bool tt} : list level → list (expr elab) := list.map sort

meta def num_sorts {elab : opt_param bool tt} (root : name) (base : nat) : nat → list (expr elab) :=
λ n, expr.sorts $ level.num_params root base n

meta def sub_sorts {elab : opt_param bool tt} (root : name) (base : nat) : nat → list (expr elab) :=
λ n, expr.sorts $ level.sub_params root base n

meta def app_beta : expr → expr → expr
| (expr.lam _ _ _ e) := instantiate_var e
| e := expr.app e

meta def mk_app_beta : expr → list expr → expr
| (expr.lam _ _ _ e) (x::xs) := mk_app_beta (instantiate_var e x) xs
| e xs := mk_app e xs

end expr

namespace tactic

meta def mk_locals (root : name) (base : nat) (bi : binder_info) : list expr → tactic (list expr)
| [] := return []
| (x::xs) := mk_locals xs >>= λ ls, mk_local' (mk_num_name root (base + xs.length)) bi x >>= λ l, return (l::ls)

meta def get_locals (root : name) (base : nat) : nat → tactic (list expr)
| 0 := return []
| (n+1) := get_locals n >>= λ xs, get_local (mk_num_name root (base + xs.length)) >>= λ x, return (x::xs)

meta def mk_local_lambdas : expr → tactic (list expr × expr)
| (expr.lam n bi d b) := do
  p ← mk_local' n bi d,
  e ← whnf (expr.instantiate_var b p),
  (ps, r) ← mk_local_lambdas e,
  return ((p :: ps), r)
| e := return ([], e)

end tactic
