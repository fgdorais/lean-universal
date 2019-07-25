-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .default
import .meta.default

meta structure identity_info :=
(to_name : name)
(cl_name : option name)
(el_name : option name)
(univ_params : list name)
(params : expr_ctx)
(vars : list (level × name × expr))
(eqns : list (level × expr × expr × expr))
(is_trusted : bool)

namespace identity_info
variable (info : identity_info)
include info

meta def num_vars : nat := info.vars.length

meta def num_hyps : nat := info.eqns.length - 1

meta def type : expr := info.params.pi (expr.sort level.zero)

meta def eqn : expr :=
let bi : binder_info := if info.num_hyps = 0 then binder_info.default else binder_info.strict_implicit in
let vars : expr_ctx := info.vars.enum.map $ λ ⟨k, _, n, t⟩, 
  (n, t.lift_vars 0 (info.vars.length - k - 1), bi) in
let eqns : list expr := info.eqns.map $ λ ⟨lvl, typ, lhs, rhs⟩,
  let typ := typ.lift_vars 0 vars.length in
  let lhs := vars.app_beta (lhs.lift_vars 0 vars.length) in
  let rhs := vars.app_beta (rhs.lift_vars 0 vars.length) in
  expr.mk_app (expr.const `eq [lvl]) [typ, lhs, rhs] in
let eqn : expr := eqns.tail.foldl (λ q e,  
  expr.pi `h binder_info.default e (q.lift_vars 0 1)
) eqns.head in
vars.pi eqn

end identity_info

namespace identity
open exceptional

meta def get_info_aux_1 : expr_ctx → list (expr × expr × expr) × expr_ctx
| vars@((n,t,b)::ctx) :=
  match t with
  | `(@eq %%typ %%lhs %%rhs) :=
    let (eqns, vars) := get_info_aux_1 ctx in
    let typ := typ.lower_vars 0 (eqns.length + vars.length) in
    let lhs := vars.lam (lhs.lower_vars 0 eqns.length) in
    let rhs := vars.lam (rhs.lower_vars 0 eqns.length) in
    ((typ, lhs, rhs) :: eqns, vars)
  | _ := ([], vars)
  end
| [] := ([],[])

meta def get_info_aux : expr → list (name × expr) × list (expr × expr × expr) :=
λ e, 
let (e, ctx) := expr_ctx.get_ctx_pi e in
let (eqns, ctx) := get_info_aux_1 (ctx.add `_ e) in
let vars : list (name × expr) := ctx.enum.map (λ ⟨k,n,t,_⟩, (n, t.lower_vars 0 (ctx.length - k - 1))) in
(vars, eqns)

meta def get_info (decl : declaration) (clname : opt_param (option name) none) (elname : opt_param (option name) none) : exceptional identity_info :=
let (e, params) := expr_ctx.get_ctx_lam decl.value in
let (vars, eqns) := get_info_aux e in
vars.mmap (λ ⟨nm, typ⟩,
match typ with
| expr.var i := 
  match list.nth params i with
  | some (_, expr.sort lvl, _) := success (lvl, nm, typ)
  | _ := fail "dom sort error"
  end
| _ := fail $ "dom sort error"
end) >>= λ vars,
eqns.mmap (λ ⟨typ,lhs,rhs⟩, match typ with
| expr.var i :=
  match list.nth params i with
  | some (_, expr.sort lvl, _) := success (lvl, typ, lhs, rhs)
  | _ := fail "cod sort error"
  end
| _ := fail "cod sort error"
end) >>= λ eqns,
success
{ to_name := decl.to_name
, cl_name := clname
, el_name := elname
, univ_params := decl.univ_params
, params := params
, vars := vars
, eqns := eqns
, is_trusted := decl.is_trusted
}

meta def mk_decl (info : identity_info) : declaration :=
let itype : expr := info.params.pi (expr.sort level.zero) in
let vars : expr_ctx := info.vars.enum.map (λ ⟨k, _, n, t⟩, (n, t.lift_vars 0 (info.vars.length - k - 1), binder_info.default)) in
let eqns : list expr := info.eqns.map (λ ⟨lvl, typ, lhs, rhs⟩,
  let typ := typ.lift_vars 0 vars.length in
  let lhs := vars.app (lhs.lift_vars 0 vars.length) in
  let rhs := vars.app (rhs.lift_vars 0 vars.length) in
  expr.mk_app (expr.const `eq [lvl]) [typ, lhs, rhs]
) in
let ivalue : expr := info.params.lam info.eqn in
declaration.defn info.to_name info.univ_params itype ivalue reducibility_hints.abbrev tt

meta def mk_class : identity_info → inductive_declaration × declaration :=
λ info,
let clname : name := info.cl_name.get_or_else (info.to_name ++ `class) in
let elname : name := info.el_name.get_or_else (info.to_name ++ `elim) in
let ls : list level := info.univ_params.map level.param in
let params : expr_ctx := info.params.map (λ ⟨n, e, _⟩, (n, e, binder_info.implicit)) in
let cltype : expr := info.type in
let ctx : expr_ctx := info.params.add `h info.eqn in 
let clcons : expr := expr.const clname ls in 
let clcons : expr := info.params.app clcons in
let clcons : expr := ctx.pi (clcons.lift_vars 0 1) in
let clind : inductive_declaration :=
{ to_name := clname
, univ_params := info.univ_params
, type := cltype
, num_params := info.params.length
, num_indices := 0
, recursor := none
, constructors := [(clname ++ `intro, clcons)]
, is_trusted := info.is_trusted
} in
let clinst : expr := expr.const clname ls in
let clinst : expr := info.params.app clinst in
let ctx : expr_ctx := info.params.add `_inst clinst binder_info.inst_implicit in
let eltype : expr := ctx.pi (info.eqn.lift_vars 0 1) in
let elvalue : expr := expr.const (clname ++ `rec) (level.zero::ls) in
let elvalue : expr := info.params.app elvalue in
let elvalue : expr := expr.app elvalue info.eqn in
let eid : expr := expr.app (expr.const `id [level.zero]) info.eqn in
let elvalue : expr := expr.app elvalue eid in
let elvalue : expr := info.params.lam elvalue in
let eldecl := declaration.defn elname info.univ_params eltype elvalue reducibility_hints.abbrev info.is_trusted in 
(clind, eldecl)

meta def mk_pattern_name (vars : nat) (hyps : nat := 0) : name :=
if hyps = 0
then mk_sub_name `algebra.identity vars
else mk_sub_name (mk_sub_name `algebra.identity vars) hyps

meta def mk_pattern_decl (vars : nat) (hyps : nat := 0) : inductive_declaration × declaration :=
let pname : name := mk_pattern_name vars hyps in
let dls : list level := level.sub_params `u vars 1 in
let dlm : level := level.list_max dls in
let dom : expr_ctx := (mk_sub_names `α vars 1).zip (dls.map (λ l, (expr.sort l, binder_info.implicit))) in
let cls : list level := level.sub_params `v (hyps+1) 1 in
let cod : expr_ctx := (mk_sub_names `β (hyps+1) 1).zip (cls.map (λ l, (expr.sort l, binder_info.implicit))) in
let var : expr_ctx := (mk_sub_names `x vars 1).reverse.map (λ n, (n, expr.var (vars + hyps), binder_info.default)) in
let ctx : expr_ctx := cod.reverse ++ dom.reverse in
let fts : list expr := (list.range (hyps+1)).reverse.map (λ i, expr.lift_vars (var.pi (expr.var (vars+hyps-i))) 0 i) in
let lhs : expr_ctx := (mk_sub_names `lhs (hyps+1) 1).reverse.zip (fts.map (λ e, (e, binder_info.default))) in
let rhs : expr_ctx := (mk_sub_names `rhs (hyps+1) 1).reverse.zip (fts.map (λ e, (e.lift_vars 0 (hyps+1), binder_info.default))) in
let ctx : expr_ctx := rhs ++ lhs ++ cod.reverse ++ dom.reverse in
let ptype := ctx.pi (expr.sort level.zero) in
let var : expr_ctx := var.lift_vars 0 (2 * hyps + 2) in
let ctx : expr_ctx := rhs ++ lhs ++ cod.reverse ++ dom.reverse in
let eql : list expr := (list.range (hyps+1)).map (λ i, var.app (expr.var (vars + 2 * hyps + 1 - i))) in
let eqr : list expr := (list.range (hyps+1)).map (λ i, var.app (expr.var (vars + hyps - i))) in
let eqs : list expr := (cls.zip $ list.zip eql eqr).enum.map (λ e : nat × level × expr × expr, 
  expr.mk_app (expr.const `eq [e.snd.fst]) [expr.var (vars+3*hyps+2-e.fst), e.snd.snd.fst, e.snd.snd.snd]) in
let eqn : expr := var.pi (eqs.reverse.tail.foldl (λ e h, expr.pi `h binder_info.default h (e.lift_vars 0 1)) eqs.reverse.head) in
let cctx := ctx.add `_ eqn in
let pcons := cctx.pi ((ctx.app (expr.const pname (dls++cls))).lift_vars 0 1) in
let pdecl : inductive_declaration :=
{ to_name := pname
, univ_params := mk_sub_names `u vars 1 ++ mk_sub_names `v (hyps+1) 1
, type := ptype
, num_params := vars + 3 * hyps + 3
, num_indices := 0
, recursor := some (pname ++ `rec)
, constructors := [(pname ++ `intro, pcons)]
, is_trusted := tt  
} in
let ectx := ctx.add `_inst (ctx.app (expr.const pname (dls++cls))) binder_info.inst_implicit in
let etype := ectx.pi (eqn.lift_vars 0 1) in
let evalue : expr := ctx.app (expr.const (pname ++ `rec) (level.zero :: dls ++ cls)) in
let evalue : expr := expr.app evalue eqn in
let evalue : expr := expr.app evalue (expr.app (expr.const `id [level.zero]) eqn) in
let evalue : expr := ctx.lam evalue in
let edecl := declaration.defn (pname ++ `elim) pdecl.univ_params etype evalue reducibility_hints.abbrev tt in
(pdecl, edecl)

meta def mk_pattern_inst (info : identity_info) : declaration × declaration :=
let pcname : name := mk_pattern_name info.num_vars info.num_hyps in
let pename : name := pcname ++ `elim in
let piname : name := pcname ++ `intro in
let plvls : list level :=
  info.vars.reverse.map prod.fst ++ 
  info.eqns.reverse.map prod.fst in
let pargs : list expr := 
  info.vars.reverse.map (λ ⟨_,_,t⟩, t) ++
  info.eqns.reverse.map (λ ⟨_,t,_,_⟩, t) ++
  info.eqns.reverse.map (λ ⟨_,_,l,_⟩, l) ++
  info.eqns.reverse.map (λ ⟨_,_,_,r⟩, r) in
let pclass : expr := expr.mk_app (expr.const pcname plvls) pargs in
let pintro : expr := expr.mk_app (expr.const piname plvls) pargs in
let pelim : expr := expr.mk_app (expr.const pename plvls) pargs in
let icname : name := info.cl_name.get_or_else (info.to_name ++ `class) in
let iiname : name := icname ++ `intro in
let iename : name := info.el_name.get_or_else (info.to_name ++ `elim) in
let ilvls : list level := info.univ_params.map level.param in
let iclass : expr := info.params.app (expr.const icname ilvls) in
let iintro : expr := info.params.app (expr.const iiname ilvls) in
let ielim : expr := info.params.app (expr.const iename ilvls) in
let toctx : expr_ctx := info.params.add `_inst iclass binder_info.inst_implicit in
let totype : expr := toctx.pi (pclass.lift_vars 0 1) in
let toarg : expr := expr.app (ielim.lift_vars 0 1) (expr.var 0) in
let tovalue : expr := expr.app (pintro.lift_vars 0 1) toarg in
let tovalue : expr := toctx.lam tovalue in
let todecl := declaration.defn (icname ++ `to_pattern) info.univ_params totype tovalue reducibility_hints.abbrev info.is_trusted in
let ofctx : expr_ctx := info.params.add `_inst pclass binder_info.inst_implicit in
let oftype : expr := ofctx.pi (iclass.lift_vars 0 1) in
let ofarg : expr := expr.app (pelim.lift_vars 0 1) (expr.var 0) in
let ofvalue : expr := expr.app (iintro.lift_vars 0 1) ofarg in
let ofvalue : expr := ofctx.lam ofvalue in
let ofdecl := declaration.defn (icname ++ `of_pattern) info.univ_params oftype ofvalue reducibility_hints.abbrev info.is_trusted in
(todecl, ofdecl)

meta def mk_identity_instance (th : declaration) : exceptional declaration :=
let (e, ctx) := expr_ctx.get_ctx_pi th.type in
match e.get_app_fn with
| (expr.const nm lvls) :=
  if nm.get_prefix = `algebra.identity 
  then success (nm.get_suffix, lvls, e.get_app_args)
  else fail "invalid identity theorem"
| _ := fail "invalid identity theorem"
end >>=
λ ⟨iname, ilvls, iargs⟩,
let targ : expr := expr.const th.to_name (th.univ_params.map level.param) in
let targ : expr := ctx.app targ in
let itype : expr := expr.const (`algebra.class ++ iname) ilvls in
let itype : expr := ctx.pi (expr.mk_app itype iargs) in
let ivalue : expr := expr.const (`algebra.class ++ iname ++ `intro) ilvls in
let ivalue : expr := expr.mk_app ivalue iargs in
let ivalue : expr := ctx.lam (expr.app ivalue targ) in
success $ declaration.defn (th.to_name ++ `_identity) th.univ_params itype ivalue reducibility_hints.abbrev tt

end identity

meta def theory.mk_infer : structure_declaration → exceptional declaration :=
λ sd, let (_, ctx) := expr_ctx.get_ctx_pi sd.type in
sd.fields.reverse.enum.mmap (λ ⟨k, fn, ft⟩,
  let (ft, _) := expr_ctx.get_ctx_pi ft in
  let ft := ft.lower_vars 0 1 in
  match ft.get_app_fn with
  | expr.const nm ls :=
    if nm.get_prefix = `algebra.identity then
    let cl : expr := expr.const (nm.update_prefix `algebra.class) ls in
    let cl : expr := expr.mk_app cl ft.get_app_args in
    let cl : expr := expr.lift_vars cl 0 (sd.num_fields - k - 1) in
    let el : expr := expr.const (nm.update_prefix `algebra) ls in
    let el : expr := expr.mk_app el ft.get_app_args in
    let el : expr := expr.app (el.lift_vars 0 sd.num_fields) (expr.var k) in
    exceptional.success (fn.get_suffix, cl, el) 
    else exceptional.fail "invalid axiom"
  | e := exceptional.fail "invalid axiom"
  end) >>= λ axs,
let axarg : list expr := axs.map (λ ⟨_,_,el⟩, el) in
let axctx : expr_ctx := axs.map (λ ⟨n,cl,_⟩, (n, cl, binder_info.inst_implicit)) in
let iftype : expr := expr.const sd.to_name (sd.univ_params.map level.param) in
let iftype : expr := ctx.pi (axctx.pi ((ctx.app iftype).lift_vars 0 axctx.length)) in
let ifvalue : expr := expr.const sd.mk_name (sd.univ_params.map level.param) in
let ifvalue : expr := ctx.app ifvalue in
let ifvalue : expr := expr.mk_app (ifvalue.lift_vars 0 axctx.length) axarg.reverse in
let ifvalue : expr := ctx.lam (axctx.lam ifvalue) in
exceptional.success $
declaration.defn (sd.to_name ++ `infer) sd.univ_params iftype ifvalue reducibility_hints.abbrev sd.is_trusted

meta def tactic.add_pattern_decl (vars : nat) (hyps : nat := 0) : tactic unit :=
let (idecl, edecl) := identity.mk_pattern_decl vars hyps in
tactic.add_ind idecl >> tactic.add_decl edecl >> tactic.set_basic_attribute `class idecl.to_name tt

section attributes
open tactic

@[user_attribute]
meta def algebra.identity_decl_attr : user_attribute :=
{ name := `identity
, descr := "declare an algebraic quasi-identity"
, after_set := some $ λ nm _ _, do {
    guard (nm.get_prefix = `algebra.identity),
    decl ← get_decl nm,
    info ← identity.get_info decl 
      (some $ nm.update_prefix `algebra.class)
      (some $ nm.update_prefix `algebra),
    (cldecl, eldecl) ← pure $ identity.mk_class info,
    add_ind cldecl >> set_basic_attribute `class cldecl.to_name tt,
    add_decl eldecl >> set_basic_attribute `reducible eldecl.to_name tt,
    (resolve_constant (identity.mk_pattern_name info.num_vars info.num_hyps) >> tactic.skip)
      <|> tactic.add_pattern_decl info.num_vars info.num_hyps,
    (todecl, ofdecl) ← pure $ identity.mk_pattern_inst info,
    add_decl todecl >> tactic.set_basic_attribute `instance todecl.to_name tt,
    add_decl ofdecl,
    skip
  }
}

@[user_attribute]
meta def algebra.identity_inst_attr : user_attribute unit (option name) :=
{ name := `identity_instance
, descr := "declare an algebraic quasi-identity instance"
, parser := optional lean.parser.ident
, after_set := some $ λ nm prio perm, do {
    decl ← get_decl nm,
    arg ← algebra.identity_inst_attr.get_param nm, 
    match arg with
    | some _ := fail "not implemented"
    | none := do {
        d ← identity.mk_identity_instance decl,
        add_decl d,
        set_basic_attribute `instance d.to_name perm (some prio)
      }
    end
  }
} 

@[user_attribute]
meta def algebra.theory_attr : user_attribute :=
{ name := `theory
, descr := "declare an algebraic theory"
, after_set := some $ λ nm prio perm, do {
    decl ← get_str nm,
    infer ← theory.mk_infer decl,
    add_decl infer,
    decl.fields.mfoldr (λ ⟨fn,_⟩ t, algebra.identity_inst_attr.set fn none perm (some prio)) ()
  }
} 

end attributes
