-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .expr
import .format

meta abbreviation expr_ctx : Type := list (name × expr × binder_info)

namespace expr_ctx
open exceptional

meta def nil : expr_ctx := list.nil

meta def add (ctx : expr_ctx) (n : name) (e : expr) (b : binder_info := binder_info.default) : expr_ctx :=
(n, e, b) :: ctx

meta def pop : expr_ctx → exceptional (expr_ctx × name × expr × binder_info)
| ((n,e,b)::ctx) := success (ctx,n,e,b)
| [] := fail "empty expr_ctx"

meta def get : expr_ctx → exceptional (name × expr × binder_info) :=
λ ctx, ctx.pop >>= λ r, success r.snd

meta def nth : expr_ctx → nat → exceptional (name × expr × binder_info)
| (_ :: ctx) (n+1) := nth ctx n
| (c :: _) 0 := success c
| [] _ := fail "empty expr_ctx"

meta def del : expr_ctx → exceptional expr_ctx :=
λ ctx, ctx.pop >>= λ r, success r.fst

meta def drop : expr_ctx → nat → exceptional expr_ctx
| ctx 0 := success ctx
| ctx (k+1) := del ctx >>= λ ctx, drop ctx k

meta def take : expr_ctx → nat → exceptional expr_ctx
| _ 0 := success nil
| ctx (k+1) := 
  ctx.pop >>=
  λ ⟨ctx, c⟩, ctx.take k >>=
  λ ctx, success $ c :: ctx

meta def app (ctx : expr_ctx) : expr → expr :=
λ e, e.mk_app (expr.mk_num_vars ctx.length).reverse

meta def app_beta (ctx : expr_ctx) : expr → expr :=
λ e, e.mk_app_beta (expr.mk_num_vars ctx.length).reverse

meta def insert_aux : expr_ctx → nat → name × expr × binder_info → exceptional expr_ctx
| ctx (k+1) :=
  λ c, ctx.pop >>=
  λ ⟨ctx, n, t, b⟩, insert_aux ctx k c >>=
  λ ctx, success $ ctx.add n (t.lift_vars k 1) b
| ctx 0 :=
  λ ⟨n, t, b⟩, success $ ctx.add n t b

meta def insert (ctx : expr_ctx) (i : nat) (n : name) (t : expr) (b : binder_info := binder_info.default) :
exceptional expr_ctx := insert_aux ctx i (n, t.lower_vars 0 i, b)

meta def delete : expr_ctx → nat → exceptional expr_ctx
| ctx (k+1) :=
  ctx.pop >>=
  λ ⟨ctx, n, t, b⟩, delete ctx k >>=
  λ ctx, success $ ctx.add n (t.lower_vars k 1) b
| ctx 0 := ctx.del

meta def collect_univ_params (ctx : expr_ctx) : list name :=
ctx.foldl (λ us ⟨_,e,_⟩, e.collect_univ_params.foldr list.insert us) []

meta def implicitize : expr_ctx → expr_ctx
| [] := []
| ((n,t,binder_info.default)::ctx) := (n,t,binder_info.implicit) :: implicitize ctx
| (c::ctx) := c :: implicitize ctx

meta def lam : expr_ctx → expr → expr
| [] e := e
| ((n,t,_)::ctx) e := lam ctx (expr.lam n binder_info.default t e)

meta def mk_lam : expr_ctx → nat → expr → exceptional expr :=
λ ctx k e, ctx.take k >>= λ ctx, success $ ctx.lam e

meta def pi : expr_ctx → expr → expr
| [] e := e
| ((n,t,b)::ctx) e := pi ctx (expr.pi n b t e)

meta def mk_pi : expr_ctx → nat → expr → exceptional expr :=
λ ctx k e, ctx.take k >>= λ ctx, success $ ctx.pi e

meta def get_ctx_lam_aux : expr → expr_ctx → expr × expr_ctx
| (expr.lam n b t e) ctx := get_ctx_lam_aux e ((n, t, b) :: ctx)
| e ctx := (e, ctx)

meta def get_ctx_lam : expr → expr × expr_ctx :=
λ e, get_ctx_lam_aux e nil

meta def get_ctx_pi_aux : expr → expr_ctx → expr × expr_ctx
| (expr.pi n b t e) ctx := get_ctx_pi_aux e ((n, t, b) :: ctx)
| e ctx := (e, ctx)

meta def get_ctx_pi : expr → expr × expr_ctx := λ e, get_ctx_pi_aux e nil

meta def lift_vars : expr_ctx → nat → nat → expr_ctx
| [] _ _ := []
| ((n,e,b)::ctx) s i := (n, e.lift_vars s i, b) :: lift_vars ctx (s+1) i

meta def lower_vars : expr_ctx → nat → nat → expr_ctx
| [] _ _ := []
| ((n,e,b)::ctx) s d := (n, e.lower_vars s d, b) :: lower_vars ctx (s+1) d

meta def mk_local (upfx : name) : expr_ctx → list expr
| [] := []
| ((n,t,b)::ctx) :=
  let loc := mk_local ctx in
  let t := t.instantiate_vars loc in
  expr.local_const (mk_num_name upfx ctx.length) n b t :: loc

meta def ref_aux : expr_ctx → name → nat → exceptional nat
| [] n _ := fail $ "name " ++ n.to_string ++ " not found in expr_ctx"
| (c::ctx) n k := if c.fst = n then success k else ref_aux ctx n (k+1)

meta def ref : expr_ctx → name → exceptional nat :=
λ ctx n, ctx.ref_aux n 0

meta def ref_var : expr_ctx → name → exceptional expr :=
λ ctx n, ctx.ref n >>= λ k, success $ expr.var k

meta def refs (ctx : expr_ctx) : list name → exceptional (list nat)
| [] := success []
| (n::ns) := ctx.ref n >>= λ k, refs ns >>= λ ks, success $ k :: ks

meta def ref_vars : expr_ctx → list name → exceptional (list expr) :=
λ ctx ns, ctx.refs ns >>= λ ks, success $ ks.map expr.var

meta def expr_to_fmt (ctx : expr_ctx) : expr → format
| (expr.var i) := 
  match ctx.nth i with 
  | success ⟨n,_⟩ := to_fmt n
  | exception _ _ := "#" ++ to_fmt (i - ctx.length)
  end
| (expr.sort l) := "Sort " ++ format.paren (to_fmt l)
| (expr.app a b) := expr_to_fmt a ++ " " ++ format.paren (expr_to_fmt b)
| (expr.pi n b t e) := "Π " ++ b.to_fmt (to_fmt n ++ " : " ++ expr_to_fmt t) ++ ", " ++ expr_to_fmt e
| (expr.lam n b t e) := "λ " ++ b.to_fmt (to_fmt n ++ " : " ++ expr_to_fmt t) ++ ", " ++ expr_to_fmt e
| (expr.local_const _ n b t) := b.to_fmt (to_fmt n ++ " : " ++ expr_to_fmt t)
| (expr.elet n t v e) := "let " ++ to_fmt n ++ " : " ++ expr_to_fmt t ++ " := " ++ expr_to_fmt v ++ " in " ++ expr_to_fmt e
| (expr.mvar n _ t) := format.paren (to_fmt n ++ " : " ++ expr_to_fmt t)
| (expr.const n l) := "@" ++ to_fmt n ++ "." ++ format.cbrace (format.join (list.intersperse format.space (l.map to_fmt)))
| (expr.macro m e) := to_fmt (expr.macro_def_name m) ++ format.sbracket (format.join $ list.intersperse ", " $ e.map expr_to_fmt)

meta def expr_to_string (ctx : expr_ctx) (e : expr) : string := to_string $ ctx.expr_to_fmt e

meta def to_format : expr_ctx → format
| (⟨n, t, b⟩ :: ctx) := to_format ctx ++ format.space ++ b.to_fmt (to_fmt n ++ " : " ++ expr_to_fmt ctx t)
| [] := ""

meta def to_format_num : expr_ctx → nat → format
| (⟨n, t, b⟩ :: ctx) (p+1) := to_format_num ctx p ++ format.space ++ b.to_fmt (to_fmt n ++ " : " ++ expr_to_fmt ctx t)
| _ 0 := ""
| [] _ := ""

end expr_ctx

meta def tactic.mk_local_ctx : expr_ctx → tactic (list expr) :=
λ ctx, tactic.mk_fresh_name >>= λ upfx, return $ expr_ctx.mk_local upfx ctx
