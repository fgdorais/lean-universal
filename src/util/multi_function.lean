-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .meta.ind_utils

/-

structure {u_0 u_1 ... u_{n-1} v_0 v_1 ... v_{n-1}} multi_function_n 
(α_0 : Sort u_0) (α_1 : Sort u_1) ... (α_{n-1} : Sort u_{n-1})
(β_0 : Sort v_0) (β_1 : Sort v_1) ... (β_{n-1} : Sort v_{n-1}) :=
mk :: (fn_0 : α_0 → β_0) (fn_1 : α_1 → β_1) ... (fn_{n-1} : α_{n-1} → β_{n-1})

theorem multi_function_n.mk.eta {α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}} (f : multi_function_n α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}),
multi_function_n.mk (multi_function_n.fn_0 f) (multi_function_n.fn_1 f) ... (multi_function_n.fn_{n-1} f) = f

definition multi_function_n.id {α_0 α_1 ... α_{n-1}} :
multi_function_n α_0 α_1 ... α_{n-1} α_0 α_1 ... α_{n-1}

definition multi_function_n.comp {α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1} γ_0 γ_1 ... γ_{n-1}} :
multi_function_n β_0 β_1 ... β_{n-1} γ_0 γ_1 ... γ_{n-1} → 
multi_function_n α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1} → 
multi_function_n α_0 α_1 ... α_{n-1} γ_0 γ_1 ... γ_{n-1}

theorem multi_function_n.comp.assoc {α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1} γ_0 γ_1 ... γ_{n-1} δ_0 δ_1 ... δ_{n-1}} 
(f : multi_function_n γ_0 γ_1 ... γ_{n-1} δ_0 δ_1 ... δ_{n-1})
(g : multi_function_n β_0 β_1 ... β_{n-1} γ_0 γ_1 ... γ_{n-1})
(h : multi_function_n α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}) :  
multi_function_n.comp (multi_function_n.comp f g) h = multi_function_n.comp f (multi_function_n.comp g h)

theorem multi_function_n.comp.left_id {α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}}
(f : multi_function_n α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}) : 
multi_function_n.comp multi_function_n.id f = f

theorem multi_function_n.comp.right_id {α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}}
(f : multi_function_n α_0 α_1 ... α_{n-1} β_0 β_1 ... β_{n-1}) : 
multi_function_n.comp f multi_function_n.id = f

-/

namespace multi_function

def to_name (n : nat) : name := mk_sub_name `multi_function n

def mk_name (n : nat) : name := to_name n ++ `mk

def fn_name (n i : nat) : name := to_name n ++ mk_sub_name `fn i

meta def mk_decl (n : nat) : inductive_declaration :=
let nm := to_name n in
let dus := mk_sub_names `u n in
let dls := dus.map level.param in
let dns := mk_sub_names `α n in
let cus := mk_sub_names `v n in
let cls := cus.map level.param in
let cns := mk_sub_names `β n in
let ctx : expr_ctx :=
  (dns ++ cns).reverse.zip $
  (dls ++ cls).reverse.map $
  λ l, (expr.sort l, binder_info.default) in
let lt := level.list_max (level.one :: dls ++ cls) in
let type : expr := ctx.pi (expr.sort lt) in
let inst : expr := ctx.app (expr.const nm (dls ++ cls)) in
let ctx : expr_ctx := ctx.map (λ ⟨n, t, _⟩, (n, t, binder_info.implicit)) in
let ctx : expr_ctx := (mk_sub_names `fn n).reverse.enum.foldr (λ ⟨k, fn⟩ ctx,
  ctx.add fn (expr.pi `_ binder_info.default (expr.var (2 * n - 1)) (expr.var n))
) ctx in
let cons : expr := ctx.pi (inst.lift_vars 0 n) in
{ to_name := nm
, univ_params := dus ++ cus
, type := type
, recursor := some (nm ++ `rec)
, constructors := [(mk_name n, cons)]
, num_params := 2 * n
, num_indices := 0
, is_trusted := tt 
}

meta def mk_proj (n : nat) : list declaration :=
let nm := to_name n in
let dus := mk_sub_names `u n in
let dls := dus.map level.param in
let dns := mk_sub_names `α n in
let cus := mk_sub_names `v n in
let cls := cus.map level.param in
let cns := mk_sub_names `β n in
let ctx : expr_ctx :=
  (dns ++ cns).reverse.zip $
  (dls ++ cls).reverse.map $
  λ l, (expr.sort l, binder_info.implicit) in
let inst : expr := ctx.app (expr.const nm (dls ++ cls)) in
let tctx : expr_ctx := ctx.add `f inst in
let types : list expr := (list.range' n).map (λ k,
  tctx.pi (expr.pi `_ binder_info.default (expr.var (2 * n - k)) (expr.var (n + 1 - k)))
) in
let fctx : expr_ctx := (mk_sub_names `fn n).reverse.map (λ fn,
  (fn, (expr.pi `_ binder_info.default (expr.var (2 * n - 1)) (expr.var n)), binder_info.default)
) in
let values : list expr := (list.range' n).map (λ k,
  let l := level.imax (level.param $ mk_sub_name `u k) (level.param $ mk_sub_name `v k) in
  let mot : expr := expr.pi `_ binder_info.default (expr.var (2 * n - k)) (expr.var (n + 1 - k)) in
  let mot : expr := expr.lam `H binder_info.default inst mot in
  let val : expr := fctx.lam (expr.var (n - k - 1)) in
  let rec : expr := ctx.app (expr.const (nm ++ `rec) (l :: dls ++ cls)) in
  let rec : expr := rec.app mot in
  let rec : expr := rec.app val in
  ctx.lam rec
) in
(list.zip types values).enum.map (λ ⟨k, t, v⟩,
  declaration.defn (fn_name n k) (dus ++ cus) t v reducibility_hints.abbrev tt
)

meta def mk_eta (n : nat) : declaration :=
let nm := to_name n in
let dus := mk_sub_names `u n in
let dls := dus.map level.param in
let dns := mk_sub_names `α n in
let cus := mk_sub_names `v n in
let cls := cus.map level.param in
let cns := mk_sub_names `β n in
let lvl := level.list_max (level.one :: dls ++ cls) in
let ctx : expr_ctx :=
  (dns ++ cns).reverse.zip $
  (dls ++ cls).reverse.map $
  λ l, (expr.sort l, binder_info.implicit) in
let inst : expr := ctx.app (expr.const nm (dls ++ cls)) in
let cons : expr := ctx.app (expr.const (mk_name n) (dls ++ cls)) in
let tctx : expr_ctx := ctx.add `f inst in
let fns : list expr := (list.range n).map (λ k,
  let e : expr := expr.const (fn_name n k) (dls ++ cls) in
  tctx.app e
) in
let lhs : expr := expr.mk_app (cons.lift_vars 0 1) fns in
let eqn : expr := expr.mk_app (expr.const `eq [lvl]) [inst.lift_vars 0 1, lhs, expr.var 0] in
let type : expr := tctx.pi $ eqn in
let rec : expr := ctx.app $ expr.const (nm ++ `rec_on) (level.zero :: dls ++ cls) in
let rec : expr := rec.app (expr.lam `f binder_info.default inst eqn) in
let rec : expr := expr.app (rec.lift_vars 0 1) (expr.var 0) in
let fctx : expr_ctx := (list.range n).map (λ k,
  (mk_sub_name `fn (n-k-1), expr.pi `_ binder_info.default (expr.var (2 * n)) (expr.var (n+1)), binder_info.default)
) in
let fobj : expr := fctx.app (cons.lift_vars 0 (n+1)) in
let prf : expr := expr.const `eq.refl [lvl] in
let prf : expr := prf.mk_app [inst.lift_vars 0 (n+1), fobj] in
let value : expr := tctx.lam (rec.app $ fctx.lam prf) in
declaration.thm (mk_name n ++ `eta) (dus ++ cus) type (pure value)

/-
meta def mk_eq (n : nat) : declaration :=
let nm := to_name n in
let dus := mk_sub_names `u n in
let dls := dus.map level.param in
let dns := mk_sub_names `α n in
let cus := mk_sub_names `v n in
let cls := cus.map level.param in
let cns := mk_sub_names `β n in
let lvl := level.list_max (level.one :: dls ++ cls) in
let ctx : expr_ctx :=
  (dns ++ cns).reverse.zip $
  (dls ++ cls).reverse.map $
  λ l, (expr.sort l, binder_info.implicit) in
let inst : expr := ctx.app (expr.const nm (dls ++ cls)) in
let tctx : expr_ctx :=
[ (mk_sub_name `f 2, inst.lift_vars 0 1, binder_info.default)
, (mk_sub_name `f 1, inst, binder_info.default)
] ++ ctx in
let tctx : expr_ctx := (list.zip dls cls).indexed.foldl (λ tctx ⟨k, dl, cl⟩,
  let typ : expr := expr.pi `_ binder_info.default (expr.var (2 * n + 1)) (expr.var (n + 2)) in
  let lhs : expr := expr.const (nm ++ mk_sub_name `fn k) (dls ++ cls) in
  let lhs : expr := lhs.app (expr.var (k+1)) in
  let rhs : expr := expr.const (nm ++ mk_sub_name `fn k) (dls ++ cls) in
  let rhs : expr := rhs.app (expr.var k) in
  let eqn : expr := expr.const `eq [level.imax dl cl] in
  let eqn : expr := eqn.mk_app [typ, lhs, rhs] in
  tctx.add (mk_sub_name `h k) eqn
) tctx in
let type : expr := tctx.pi $ expr.mk_app (expr.const `eq [lvl]) [inst.lift_vars 0 (n+2), expr.var (n+1), expr.var n]
in 
let value : expr := inhabited.default expr in
declaration.thm (nm ++ `eq) (dus ++ cus) type (pure value)
-/

meta def mk_id (n : nat) : declaration :=
let nm := to_name n in
let us := mk_sub_names `u n in
let ls := us.map level.param in
let ts := mk_sub_names `α n in
let ctx : expr_ctx := ts.reverse.zip $ ls.reverse.map (λ l, (expr.sort l, binder_info.implicit)) in
let type : expr := expr.const nm (ls ++ ls) in
let type : expr := type.mk_app (expr.mk_num_vars n ++ expr.mk_num_vars n).reverse in
let type : expr := ctx.pi type in
let value : expr := expr.const (nm ++ `mk) (ls ++ ls) in
let value : expr := value.mk_app (expr.mk_num_vars n ++ expr.mk_num_vars n).reverse in
let value : expr := value.mk_app $ (list.range' n).map (λ k,
  let e : expr := expr.const `id [level.param $ mk_sub_name `u k] in
  e.app (expr.var (n - k - 1))
) in
let value : expr := ctx.lam value in
declaration.defn (nm ++ `id) us type value reducibility_hints.abbrev tt

meta def mk_comp (n : nat) : declaration :=
let nm := to_name n in
let nus := mk_sub_names `u n in
let nvs := mk_sub_names `v n in
let nws := mk_sub_names `w n in
let lus := nus.map level.param in
let lvs := nvs.map level.param in
let lws := nws.map level.param in
let tus := mk_sub_names `α n in
let tvs := mk_sub_names `β n in
let tws := mk_sub_names `γ n in
let ctx : expr_ctx := 
  (tus ++ tvs ++ tws).reverse.zip $
  (lus ++ lvs ++ lws).reverse.map $
    λ l, (expr.sort l, binder_info.implicit) in
let typeuv : expr := expr.const nm (lus ++ lvs) in
let typevw : expr := expr.const nm (lvs ++ lws) in
let typeuw : expr := expr.const nm (lus ++ lws) in
let typeuv : expr := typeuv.mk_app (expr.mk_num_vars n (2 * n)).reverse in
let typeuv : expr := typeuv.mk_app (expr.mk_num_vars n (1 * n)).reverse in
let typeuw : expr := typeuw.mk_app (expr.mk_num_vars n (2 * n)).reverse in
let typeuw : expr := typeuw.mk_app (expr.mk_num_vars n (0 * n)).reverse in
let typevw : expr := typevw.mk_app (expr.mk_num_vars n (1 * n)).reverse in
let typevw : expr := typevw.mk_app (expr.mk_num_vars n (0 * n)).reverse in
let ctx : expr_ctx := ctx.add `f typevw in
let ctx : expr_ctx := ctx.add `g (typeuv.lift_vars 0 1) in
let type : expr := ctx.pi (typeuw.lift_vars 0 2) in
let pruv : list expr := (list.range n).map (λ k, 
  let e : expr := expr.const (nm ++ mk_sub_name `fn k) (lus ++ lvs) in
  let e : expr := e.mk_app (expr.mk_num_vars n (2 * n + 2)).reverse in
  let e : expr := e.mk_app (expr.mk_num_vars n (1 * n + 2)).reverse in
  e.app (expr.var 0)
) in
let prvw : list expr := (list.range n).map (λ k, 
  let e : expr := expr.const (nm ++ mk_sub_name `fn k) (lvs ++ lws) in
  let e : expr := e.mk_app (expr.mk_num_vars n (1 * n + 2)).reverse in
  let e : expr := e.mk_app (expr.mk_num_vars n (0 * n + 2)).reverse in
  e.app (expr.var 1)
) in
let args : list expr := (list.zip pruv prvw).reverse.enum.map (λ ⟨k, fuv, fvw⟩,
  let u := [mk_sub_name `u (n-k-1), mk_sub_name `v (n-k-1), mk_sub_name `w (n-k-1)] in
  let e : expr := expr.const `function.comp (u.map level.param) in
  e.mk_app [expr.var (2*n+2+k), expr.var (1*n+2+k), expr.var (0*n+2+k), fvw, fuv]
) in
let value : expr := expr.const (nm ++ `mk) (lus ++ lws) in
let value : expr := value.mk_app (expr.mk_num_vars n (2 * n + 2)).reverse in
let value : expr := value.mk_app (expr.mk_num_vars n (0 * n + 2)).reverse in
let value : expr := value.mk_app args.reverse in
let value : expr := ctx.lam value in
declaration.defn (nm ++ `comp) (nus ++ nvs ++ nws) type value reducibility_hints.abbrev tt

meta def mk_comp_assoc (n : nat) : declaration :=
let nm := to_name n in
let nts := mk_sub_names `t n in
let nus := mk_sub_names `u n in
let nvs := mk_sub_names `v n in
let nws := mk_sub_names `w n in
let lts := nts.map level.param in
let lus := nus.map level.param in
let lvs := nvs.map level.param in
let lws := nws.map level.param in
let tts := mk_sub_names `α n in
let tus := mk_sub_names `β n in
let tvs := mk_sub_names `γ n in
let tws := mk_sub_names `δ n in
let ctx : expr_ctx := 
  (tts ++ tus ++ tvs ++ tws).reverse.zip $
  (lts ++ lus ++ lvs ++ lws).reverse.map $
    λ l, (expr.sort l, binder_info.implicit) in
let typetu : expr := expr.const nm (lts ++ lus) in
let typetu : expr := typetu.mk_app (expr.mk_num_vars n (3 * n)).reverse in
let typetu : expr := typetu.mk_app (expr.mk_num_vars n (2 * n)).reverse in
let typeuv : expr := expr.const nm (lus ++ lvs) in
let typeuv : expr := typeuv.mk_app (expr.mk_num_vars n (2 * n)).reverse in
let typeuv : expr := typeuv.mk_app (expr.mk_num_vars n (1 * n)).reverse in
let typevw : expr := expr.const nm (lvs ++ lws) in
let typevw : expr := typevw.mk_app (expr.mk_num_vars n (1 * n)).reverse in
let typevw : expr := typevw.mk_app (expr.mk_num_vars n (0 * n)).reverse in
let typetw : expr := expr.const nm (lts ++ lws) in
let typetw : expr := typetw.mk_app (expr.mk_num_vars n (3 * n)).reverse in
let typetw : expr := typetw.mk_app (expr.mk_num_vars n (0 * n)).reverse in
let ctx : expr_ctx := ctx.add `f typevw in
let ctx : expr_ctx := ctx.add `g (typeuv.lift_vars 0 1) in
let ctx : expr_ctx := ctx.add `h (typetu.lift_vars 0 2) in
let lhsl : expr := expr.const (nm ++ `comp) (lus ++ lvs ++ lws) in
let lhsl : expr := lhsl.mk_app (expr.mk_num_vars n (2 * n + 3)).reverse in
let lhsl : expr := lhsl.mk_app (expr.mk_num_vars n (1 * n + 3)).reverse in
let lhsl : expr := lhsl.mk_app (expr.mk_num_vars n (0 * n + 3)).reverse in
let lhsl : expr := lhsl.mk_app [expr.var 2, expr.var 1] in
let lhs : expr := expr.const (nm ++ `comp) (lts ++ lus ++ lws) in
let lhs : expr := lhs.mk_app (expr.mk_num_vars n (3 * n + 3)).reverse in
let lhs : expr := lhs.mk_app (expr.mk_num_vars n (2 * n + 3)).reverse in
let lhs : expr := lhs.mk_app (expr.mk_num_vars n (0 * n + 3)).reverse in
let lhs : expr := lhs.mk_app [lhsl, expr.var 0] in
let rhsr : expr := expr.const (nm ++ `comp) (lts ++ lus ++ lvs) in
let rhsr : expr := rhsr.mk_app (expr.mk_num_vars n (3 * n + 3)).reverse in
let rhsr : expr := rhsr.mk_app (expr.mk_num_vars n (2 * n + 3)).reverse in
let rhsr : expr := rhsr.mk_app (expr.mk_num_vars n (1 * n + 3)).reverse in
let rhsr : expr := rhsr.mk_app [expr.var 1, expr.var 0] in
let rhs : expr := expr.const (nm ++ `comp) (lts ++ lvs ++ lws) in
let rhs : expr := rhs.mk_app (expr.mk_num_vars n (3 * n + 3)).reverse in
let rhs : expr := rhs.mk_app (expr.mk_num_vars n (1 * n + 3)).reverse in
let rhs : expr := rhs.mk_app (expr.mk_num_vars n (0 * n + 3)).reverse in
let rhs : expr := rhs.mk_app [expr.var 2, rhsr] in
let lvl : level := level.list_max (level.one :: lts ++ lws) in
let eqn : expr := expr.const `eq [lvl] in
let eqn : expr := eqn.mk_app [typetw.lift_vars 0 3, lhs, rhs] in
let type : expr := ctx.pi eqn in
let proof : expr := expr.const `eq.refl [lvl] in
let proof : expr := proof.mk_app [typetw.lift_vars 0 3, lhs] in
let proof : expr := ctx.lam proof in
declaration.thm (nm ++ `comp ++ `assoc) (nts ++ nus ++ nvs ++ nws) type (pure proof)

meta def mk_comp_left_id (n : nat) : declaration :=
let nm := to_name n in
let nus := mk_sub_names `u n in
let nvs := mk_sub_names `v n in
let lus := nus.map level.param in
let lvs := nvs.map level.param in
let tus := mk_sub_names `α n in
let tvs := mk_sub_names `β n in
let ctx : expr_ctx := (list.zip (tus ++ tvs) (lus ++ lvs)).reverse.map (λ ⟨n, l⟩,
  (n, expr.sort l, binder_info.implicit)
) in
let typeuv : expr := ctx.app (expr.const nm (lus ++ lvs)) in
let ctx : expr_ctx := ctx.add `f typeuv in
let compuvv : expr := expr.const (nm ++ `comp) (lus ++ lvs ++ lvs) in
let compuvv : expr := compuvv.mk_app (expr.mk_num_vars n n).reverse in
let compuvv : expr := compuvv.mk_app (expr.mk_num_vars n 0).reverse in
let compuvv : expr := compuvv.mk_app (expr.mk_num_vars n 0).reverse in
let idv : expr := expr.const (nm ++ `id) lvs in
let idv : expr := idv.mk_app (expr.mk_num_vars n 0).reverse in
let lvl : level := level.list_max (level.one :: lus ++ lvs) in
let lhs : expr := expr.mk_app (compuvv.lift_vars 0 1) [idv.lift_vars 0 1, expr.var 0] in
let type : expr := expr.const `eq [lvl] in
let type : expr := type.mk_app [typeuv.lift_vars 0 1, lhs, expr.var 0] in
let type : expr := ctx.pi type in
let proof : expr := ctx.app $ expr.const (mk_name n ++ `eta) (lus ++ lvs) in
let proof : expr := ctx.lam proof in
declaration.thm (nm ++ `comp ++ `left_id) (nus ++ nvs) type (pure proof)

meta def mk_comp_right_id (n : nat) : declaration :=
let nm := to_name n in
let nus := mk_sub_names `u n in
let nvs := mk_sub_names `v n in
let lus := nus.map level.param in
let lvs := nvs.map level.param in
let tus := mk_sub_names `α n in
let tvs := mk_sub_names `β n in
let ctx : expr_ctx := (list.zip (tus ++ tvs) (lus ++ lvs)).reverse.map (λ ⟨n, l⟩,
  (n, expr.sort l, binder_info.implicit)
) in
let typeuv : expr := ctx.app (expr.const nm (lus ++ lvs)) in
let ctx : expr_ctx := ctx.add `f typeuv in
let compuuv : expr := expr.const (nm ++ `comp) (lus ++ lus ++ lvs) in
let compuuv : expr := compuuv.mk_app (expr.mk_num_vars n n).reverse in
let compuuv : expr := compuuv.mk_app (expr.mk_num_vars n n).reverse in
let compuuv : expr := compuuv.mk_app (expr.mk_num_vars n 0).reverse in
let idu : expr := expr.const (nm ++ `id) lus in
let idu : expr := idu.mk_app (expr.mk_num_vars n n).reverse in
let lvl : level := level.list_max (level.one :: lus ++ lvs) in
let lhs : expr := expr.mk_app (compuuv.lift_vars 0 1) [expr.var 0, idu.lift_vars 0 1] in
let type : expr := expr.const `eq [lvl] in
let type : expr := type.mk_app [typeuv.lift_vars 0 1, lhs, expr.var 0] in
let type : expr := ctx.pi type in
let proof : expr := ctx.app $ expr.const (mk_name n ++ `eta) (lus ++ lvs) in
let proof : expr := ctx.lam proof in
declaration.thm (nm ++ `comp ++ `right_id) (nus ++ nvs) type (pure proof)

end multi_function

meta def environment.add_multi_function (env : environment) (n : nat) : exceptional environment :=
env.add_ind (multi_function.mk_decl n) tt >>= λ env, list.mfoldl environment.add env $
multi_function.mk_proj n ++
[ multi_function.mk_eta n
, multi_function.mk_id n
, multi_function.mk_comp n
, multi_function.mk_comp_assoc n
, multi_function.mk_comp_left_id n
, multi_function.mk_comp_right_id n
]

namespace tactic

meta def add_multi_function (n : nat) : tactic unit :=
do {
  let mfn := multi_function.to_name n,
  updateex_env $ λ env, env.add_multi_function n,
  -- vm needs code for cases_on ...
  ron ← get_decl (mfn ++ `rec_on),
  add_decl (ron.update_name $ mfn ++ `cases_on),
  -- set attributes
  (list.range n).mmap (λ k,
    set_basic_attribute `reducible (mfn ++ mk_sub_name `fn k) tt >>
    set_basic_attribute `inline (mfn ++ mk_sub_name `fn k) tt
  ),
  set_basic_attribute `reducible (mfn ++ `id) tt,
  set_basic_attribute `reducible (mfn ++ `comp) tt,
  guard (n = 0) <|> set_basic_attribute `simp (mfn ++ `mk.eta) tt,
  guard (n = 0) <|> set_basic_attribute `simp (mfn ++ `comp.left_id) tt,
  guard (n = 0) <|> set_basic_attribute `simp (mfn ++ `comp.right_id) tt,
  skip
}

meta def ensure_multi_function (n : nat) : tactic unit :=
get_decl (multi_function.to_name n) >> skip <|> add_multi_function n

end tactic

run_cmd tactic.add_multi_function 1
run_cmd tactic.add_multi_function 2

instance {α} {β} : has_coe_to_fun (multi_function_1 α β) := ⟨_, multi_function_1.fn_0⟩

theorem multi_function_1.eq {α} {β} {f g : multi_function_1 α β} : f.fn_0 = g.fn_0 → f = g :=
λ h,
eq.subst (multi_function_1.mk.eta f) $
eq.subst (multi_function_1.mk.eta g) $
congr rfl h

theorem multi_function_2.eq {α_0} {α_1} {β_0} {β_1} {f g : multi_function_2 α_0 α_1 β_0 β_1} : f.fn_0 = g.fn_0 → f.fn_1 = g.fn_1 → f = g :=
λ h_0 h_1, 
eq.subst (multi_function_2.mk.eta f) $
eq.subst (multi_function_2.mk.eta g) $
congr (congr rfl h_0) h_1
