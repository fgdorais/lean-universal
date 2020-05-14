import .default
import .meta.default

definition list.pure {α : Type*} (x : α) : list α := [x]

namespace tactic

meta def mk_list_expr (ty : expr) : list expr → tactic expr
| [] := mk_app `list.nil [ty]
| (e :: es) := mk_list_expr es >>= λ es, mk_app `list.cons [ty, e, es]

meta def get_structure_fields (nm : name) : tactic (list name) :=
do {
  nm ← resolve_constant nm,
  env ← get_env,
  env.structure_fields nm
}

meta def add_structure_field_hints (d : declaration) : tactic unit :=
do {
  (ctx, typ) ← mk_local_pis d.type,
  val ← pure $ d.value.mk_app_beta ctx,
  let tnm := typ.get_app_fn.const_name,
  fns ← get_structure_fields tnm,
  dobj ← mk_app d.to_name ctx,
  gobj ← mk_local' `t binder_info.default typ,
  let ctx := ctx ++ [gobj],
  hcns ← mk_mapp `unification_constraint.mk [none, some gobj, some dobj],
  hcns ← infer_type hcns >>= λ t, mk_list_expr t [hcns],
  (fns.reverse.zip val.get_app_args.reverse).mfoldl (λ k ⟨fn, fv⟩, 
  do {
    fe ← mk_mapp (tnm ++ fn) $ (typ.get_app_args ++ [gobj]).map option.some,
    hpat ← mk_mapp `unification_constraint.mk [none, some fe, some fv],
    hintv ← mk_mapp `unification_hint.mk [some hpat, some hcns],
    hintt ← infer_type hintv,
    let hintn : name := d.to_name ++ mk_sub_name `_hint (k+1),
    let hintt : expr := hintt.pis ctx,
    let hintv : expr := hintv.lambdas ctx,
    let hdecl := declaration.defn hintn hintt.collect_univ_params hintt hintv reducibility_hints.abbrev tt,
    add_decl hdecl,
    set_basic_attribute `unify hintn tt,
    pure (k+1)
  } <|> (pure k)) (0),
  skip
}

end tactic

section signature_inst_attr
open tactic

@[user_attribute]
meta def algebra.signature_inst_attr : user_attribute :=
{ name := `signature_instance
, descr := "declare an algebraic signature instance"
, after_set := some $ λ nm _ _, do {
    decl ← resolve_constant nm >>= get_decl,
    add_structure_field_hints decl
  }
}

end signature_inst_attr
