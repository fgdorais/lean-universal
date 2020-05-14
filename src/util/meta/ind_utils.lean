-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .expr_ctx

meta structure inductive_declaration :=
(to_name : name)
(univ_params : list name)
(type : expr)
(num_params : nat)
(num_indices : nat)
(recursor : option name)
(constructors : list (name × expr))
(is_trusted : bool)

meta def environment.get_ind : environment → name → exceptional inductive_declaration :=
λ env n, env.get n >>=
λ d, list.mmap env.get (env.constructors_of n) >>=
λ cs, exceptional.success $
{ to_name := n
, univ_params := d.univ_params
, type := d.type
, num_params := env.inductive_num_params n
, num_indices := env.inductive_num_indices n
, recursor := env.recursor_of n
, constructors := cs.map (λ d, (d.to_name, d.type))
, is_trusted := d.is_trusted
}

meta def inductive_declaration.rec_to_rec_on : inductive_declaration → declaration → exceptional declaration :=
λ id rd, let (e, ctx) := expr_ctx.get_ctx_pi rd.type in ctx.pop >>=
λ ⟨ctx, n, e, b⟩, 
let mi := ctx.length - id.num_params in
ctx.insert (mi - 1) n e b >>=
λ ctx, 
let ni := mi - id.num_indices - 1 in
let rot : expr := ctx.pi (expr.app (expr.var mi) (expr.var ni)) in
let rov : expr := expr.const rd.to_name (rd.univ_params.map level.param) in
let rov : expr := expr.mk_app rov (expr.mk_num_vars (ctx.length - 1)).reverse in
let rov : expr := expr.app (rov.lift_vars (mi-1) 1) (expr.var ni) in
let rov : expr := ctx.lam rov in
exceptional.success $ declaration.defn (id.to_name ++ `rec_on) rd.univ_params rot rov reducibility_hints.abbrev id.is_trusted

meta def environment.add_ind (env : environment) (d : inductive_declaration) (rec_on : opt_param bool ff) : exceptional environment :=
env.add_inductive d.to_name d.univ_params d.num_params d.type d.constructors (bnot d.is_trusted) >>=
λ env, if rec_on = tt
then env.get (d.to_name ++ `rec) >>= d.rec_to_rec_on >>= env.add
else exceptional.success env

meta def tactic.get_ind : name → tactic inductive_declaration :=
λ n, tactic.get_env >>= λ env, tactic.returnex $ env.get_ind n

meta def tactic.add_ind (d : inductive_declaration) (rec_on : opt_param bool ff) : tactic unit :=
tactic.updateex_env $ λ env, env.add_ind d rec_on

namespace inductive_declaration
variable (d : inductive_declaration)
include d
open exceptional

meta def parse_ctx_aux : nat → expr → expr_ctx → exceptional expr_ctx
| (k+1) (expr.pi n b t e) ctx :=
  parse_ctx_aux k e (ctx.add n t b)
| 0 (expr.sort _) ctx := success ctx
| (k+1) _ _ := exception (λ _, format.to_string "parameter error")
| 0 _ _ := exception (λ _, format.to_string "type error")

/-- parameters, indices -/
meta def parse_ctx : exceptional expr_ctx :=
d.parse_ctx_aux (d.num_params + d.num_indices) d.type expr_ctx.nil

/-- parameters, motive -/
meta def mk_rec_ctx_motive : level → exceptional expr_ctx :=
λ l, let ls : list level := d.univ_params.map level.param in
d.parse_ctx >>=
λ ctx, let h : expr := ctx.app $ expr.const d.to_name ls in
let ctx := ctx.add `object h in
ctx.mk_pi d.num_indices.succ (expr.sort l) >>=
λ e, ctx.drop d.num_indices.succ >>=
λ ctx, success $ ctx.add `motive e

meta def mk_rec_ctx_on_object : level → exceptional expr_ctx :=
λ l, let ls : list level := d.univ_params.map level.param in
d.parse_ctx >>=
λ ctx, let h : expr := ctx.app $ expr.const d.to_name ls in
let ctx := ctx.add `object h in
ctx.mk_pi d.num_indices.succ (expr.sort l) >>=
λ e, ctx.insert d.num_indices.succ `motive (e.lift_vars 0 d.num_indices.succ)

meta def mk_cases_ctx_cons_aux : name → expr → exceptional expr :=
let ls : list level := d.univ_params.map level.param in
λ n e, 
let (ctyp, ctx) := expr_ctx.get_ctx_pi e in
let num_args := ctx.length - d.num_params in
let cval : expr := ctx.app (expr.const n ls) in
ctx.insert num_args `motive (default expr) >>=
λ ctx, 
let ctyp := ctyp.lift_vars num_args 1 in
let cval := cval.lift_vars num_args 1 in
let cmot : expr := expr.var num_args in
let cmot : expr := expr.mk_app cmot (ctyp.get_app_args.drop d.num_params) in
let cmot : expr := expr.app cmot cval in
ctx.mk_pi num_args cmot 

meta def mk_rec_ctx_cons_aux : name → expr → exceptional expr :=
let ls : list level := d.univ_params.map level.param in
λ n e,
let (ctyp, ctx) := expr_ctx.get_ctx_pi e in
let cval : expr := ctx.app (expr.const n ls) in
let num_args : nat := ctx.length - d.num_params in
let args : list expr := list.map (λ p : name × expr × binder_info, p.snd.fst) (list.take num_args ctx) in
ctx.insert num_args `motive (default expr) >>=
λ ctx, 
let ctyp := ctyp.lift_vars num_args 1 in
let cval := cval.lift_vars num_args 1 in
let cmot : expr := expr.var num_args in
let cmot : expr := expr.mk_app cmot (ctyp.get_app_args.drop d.num_params) in
let cmot : expr := expr.app cmot cval in
let add_ih : expr → expr_ctx → exceptional expr_ctx :=
λ e ctx, 
let (e, ectx) := expr_ctx.get_ctx_pi e in
match e.get_app_fn with
| expr.const en els :=
  if en = d.to_name then
  let emot : expr := expr.var (ctx.length - (d.num_params + 1)) in
  let emot : expr := expr.mk_app emot (e.get_app_args.drop d.num_params) in
  let emot : expr := expr.app emot (expr.var num_args) in
  success $ ctx.add (mk_sub_name `ih (ctx.length - num_args)) emot
  else success ctx
| _ := success ctx
end in 
list.mfoldr add_ih ctx args >>=
λ ctx, ctx.mk_pi (ctx.length - (d.num_params + 1)) cmot

meta def mk_cases_ctx_cons : level → exceptional expr_ctx :=
let ctx_add : expr_ctx → nat × name × expr → exceptional expr_ctx :=
λ ctx ⟨i, n, e⟩, d.mk_cases_ctx_cons_aux n e >>=
λ e, success $ ctx.add (n.update_prefix name.anonymous) (e.lift_vars 0 i) in 
λ l, d.mk_rec_ctx_motive l >>=
λ ctx, list.mfoldl ctx_add ctx d.constructors.enum

meta def mk_cases_on_ctx_cons : level → exceptional expr_ctx :=
let ctx_add : expr_ctx → nat × name × expr → exceptional expr_ctx :=
λ ctx ⟨i, n, e⟩, d.mk_cases_ctx_cons_aux n e >>=
λ e, success $ ctx.add (n.update_prefix name.anonymous) (e.lift_vars 0 (d.num_indices + i + 1)) in 
λ l, d.mk_rec_ctx_on_object l >>=
λ ctx, list.mfoldl ctx_add ctx d.constructors.enum

meta def mk_cases_on_type : level → exceptional expr :=
λ l, d.mk_cases_on_ctx_cons l >>=
λ ctx,
let motive_idx := ctx.length - (d.num_params + 1) in
let object_idx := ctx.length - (d.num_params + 1 + d.num_indices + 1) in
let goal : expr := expr.var motive_idx in
let goal : expr := expr.mk_app goal (expr.mk_num_vars d.num_indices object_idx.succ) in
let goal : expr := expr.app goal (expr.var object_idx) in
success $ ctx.pi goal
/-
let ce : expr := ctx.app (expr.const n ls) in
ctx.take (ctx.length - d.num_params) >>=
λ ctx, 
let ce : expr := ce.lift_vars ctx.length d.num_indices.succ in
let mc : expr := expr.mk_app (expr.var (ctx.length + d.num_indices)) (e.get_app_args.drop d.num_params ++ [ce]) in
let mc : expr := ctx.pi mc in
success $ ctx.add `_ mc

let adj := ctx.length - d.num_params in
ctx.take (ctx.length - d.num_params) >>=
λ ctx, --let e := e.lift_vars adj 1 in
success $ ctx.add `_ (expr.mk_app (expr.var adj) e.get_app_args)
-/

end inductive_declaration

meta structure structure_declaration :=
(to_name : name)
(mk_name : name)
(univ_params : list name)
(type : expr)
(fields : list (name × expr))
(is_trusted : bool)

meta def structure_declaration.num_fields : structure_declaration → nat := λ sd, sd.fields.length

meta def environment.structure_constructor : environment → name → option name :=
λ env nm,
match env.constructors_of nm with
| [cn] := some cn
| _ := none
end

meta def environment.get_str : environment → name → exceptional structure_declaration :=
λ env n, env.get n >>= λ decl,
match env.structure_fields n with
| some fns := fns.mmap (λ fn, env.get (n ++ fn))
| none := exceptional.fail "invalid structure"
end >>= λ fdecls,
match env.structure_constructor n with
| some mkname := exceptional.success mkname
| none := exceptional.fail "invalid structure"
end >>= λ mkname,
exceptional.success
{ to_name := decl.to_name
, mk_name := mkname
, univ_params := decl.univ_params
, type := decl.type
, fields := fdecls.map (λ d, (d.to_name, d.type))
, is_trusted := decl.is_trusted
}

meta def tactic.get_str : name → tactic structure_declaration :=
λ n, tactic.get_env >>= λ env, tactic.returnex (env.get_str n)

namespace structure_declaration
variable (d : structure_declaration)
include d

meta def to_inductive : inductive_declaration :=
let ls : list level := d.univ_params.map level.param in
let (type, params) := expr_ctx.get_ctx_pi d.type in 
let mk : expr := params.app (expr.const d.to_name ls) in
let f : expr_ctx → nat × name × expr → expr_ctx :=
λ ctx ⟨k, n, e⟩,
let (e,_) := expr_ctx.get_ctx_pi e in
ctx.add n (e.lift_vars 0 k) in
let ctx : expr_ctx := list.foldl f params d.fields.enum in
let mk : expr := ctx.pi (mk.lift_vars 0 d.fields.length) in
{ to_name := d.to_name
, univ_params := d.univ_params
, type := d.type
, num_params := params.length
, num_indices := 0
, constructors  := [(d.mk_name, mk)]
, recursor := none
, is_trusted := d.is_trusted
}

/-
meta def mk_fields_aux : nat × name × expr × level → declaration :=
λ ⟨fk, fn, ft, fl⟩,
let ls : list level := d.univ_params.map level.param in
let it : expr := d.params.app (expr.const d.to_name ls) in
let typ : expr := expr.pi `n binder_info.default it (ft.lift_vars 0 1) in
let typ : expr := d.params.pi typ in
let f : expr → nat × name × expr × level → expr :=
λ e ⟨fk, fn, ft, _⟩, expr.lam fn binder_info.default (ft.lift_vars 0 fk) e in
let mel : expr := expr.lam `n binder_info.default (it.lift_vars 0 d.fields.length) (expr.var (fk+1)) in
let mel : expr := expr.var (d.fields.length - fk - 1) in
let mel : expr := list.foldl f mel d.fields.indexed.reverse in
let mot : expr := expr.lam `n binder_info.default it (ft.lift_vars 0 1) in
let val : expr := expr.const (d.to_name ++ `rec) (fl::ls) in
let val : expr := d.params.app val in
let val : expr := expr.mk_app val [mot, mel] in
let val : expr := d.params.lam val in
declaration.defn (d.to_name ++ fn) d.univ_params typ val reducibility_hints.abbrev d.is_trusted
-/

-- meta def mk_fields : list declaration := sorry --- d.fields.indexed.map d.mk_fields_aux

end structure_declaration
