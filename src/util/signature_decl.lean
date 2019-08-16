-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .default
import .meta.default

/-- signature information -/
meta structure signature_info :=
(to_name : name)
(mk_name : name)
(univ_params : list name)
(params : list (name × level × binder_info))
(ops : list (name × nat × list nat))

namespace signature_info
open exceptional

meta def num_params (info : signature_info) : nat := info.params.length

meta def param_names (info : signature_info) : list name := info.params.map prod.fst

meta def param_snd (info : signature_info) : list (level × binder_info) := info.params.map prod.snd

meta def param_levels (info : signature_info) : list level := info.param_snd.map prod.fst

meta def param_meta_levels (info : signature_info) : list level := 
info.param_levels.map $ λ l, l.metaify info.univ_params

meta def param_binders (info : signature_info) : list binder_info := info.param_snd.map prod.snd

meta def op_names (info : signature_info) : list name := info.ops.map prod.fst

meta def op_sorts (info : signature_info) : list (nat × list nat) := info.ops.map prod.snd

meta def sig_name (info : signature_info) : name := info.to_name.add_sub_str "sig"

meta def hom_name (info : signature_info) : name := info.to_name.add_sub_str "hom"

meta def expr_name (info : signature_info) : name := info.to_name.add_sub_str "expr"

meta def trans_name (info : signature_info) : name := info.to_name.add_sub_str "trans"

section parse
open exceptional
open interactive
open lean lean.parser

meta def parse_level : list name → list name → level → level × list name × list name
| us ms (level.zero) := (level.zero, us, ms)
| us ms (level.succ l) := 
  let (l, us, ms) := parse_level us ms l in
  (level.succ l, us, ms)
| us ms (level.max l₁ l₂) :=
  let (l₁, us, ms) := parse_level us ms l₁ in
  let (l₂, us, ms) := parse_level us ms l₂ in
  (level.max l₁ l₂, us, ms)
| us ms (level.imax l₁ l₂) :=
  let (l₁, us, ms) := parse_level us ms l₁ in
  let (l₂, us, ms) := parse_level us ms l₂ in
  (level.imax l₁ l₂, us, ms)
| us ms (level.param n) := 
  let i := us.index_of n in
  if i = us.length
  then (level.param $ mk_sub_name `u us.length, n :: us, ms)
  else (level.param $ mk_sub_name `u (us.length - i - 1), us, ms) 
| us ms (level.mvar n) := 
  let i := ms.index_of n in
  if i = ms.length
  then (level.mvar $ mk_sub_name `m ms.length, us, n :: ms)
  else (level.mvar $ mk_sub_name `m (ms.length - i - 1), us, ms) 
  
meta def parse_params : list pexpr → list name × list name → list (name × level × binder_info) → exceptional (list (name × level × binder_info) × list name × list name)
| [] us ps := success $ (ps, us) 
| (e :: es) us ps :=
  parse_params es us ps >>= λ ⟨ps, us⟩,
  match e with
  | (expr.local_const _ n b (expr.sort l)) :=
    let (l, us) := parse_level us.1 us.2 l in
    success ((n, l, b) :: ps, us)
  | _ := fail "invalid signature parameter"
  end

meta def parse_op (ns : list name) : parser (name × nat × list nat) :=
do {
  nm ← ident,
  tk ":",
  ps ← sep_by (tk "→" <|> tk "->") ident,
  guard (ps.length > 0),
  let vs := ps.reverse.map (λ p, list.index_of p ns),
  guard (∀ v ∈ vs, v < ns.length),
  tk ")",
  pure (nm, vs.head, vs.tail)
}

meta def parse : parser signature_info :=
do {
  nm ← ident,
  ps ← parse_binders,
  (ps, us, ms) ← parse_params ps ([],[]) [],
  tk ":=",
  tk "(",
  fs ← sep_by (tk "(") (parse_op $ ps.map prod.fst),
  pure
  { to_name := nm
  , mk_name := `mk
  , univ_params := mk_sub_names `u us.length ++ mk_sub_names `m ms.length
  , params := ps
  , ops := fs
  }
}

meta def get_param (info : signature_info) (n : nat) : exceptional (name × level × binder_info) :=
match info.params.nth n with
| some p := success p
| none := fail "parameter index too large"
end

meta def format_sig (info : signature_info) : exceptional format :=
let s0 : list format := 
[ "structure"
, format.cbrace (format.join $ list.intersperse format.space $ info.univ_params.map to_fmt)
, to_fmt info.sig_name
] in
let s1 : list format := info.params.map (λ ⟨n, l, b⟩,
  b.to_fmt (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s2 : list format :=
let lvl : level := level.normalize $ level.list_max (level.one :: (info.params.map (λ ⟨_,l,_⟩, l))) in
[ ":"
, "Sort (" ++ to_fmt lvl ++ ")"
, ":="
, to_fmt info.mk_name
, "::"
] in
info.ops.mmap (λ ⟨n,c,d⟩,
  prod.fst <$> info.get_param c >>= 
  λ c, d.mfoldl (λ f n, 
    prod.fst <$> info.get_param n >>= λ n, success $ to_fmt n ++ " → " ++ f
  ) (to_fmt c) >>= λ fn,
  success $ format.paren $ format.join $
  list.intersperse format.space [to_fmt n, ":", fn]
) >>= λ s3,
success $ format.interspace (s0 ++ s1 ++ s2 ++ s3)

meta def format_hom (info : signature_info) : exceptional format :=
let us : list name := mk_sub_names `u info.univ_params.length in
let vs : list name := mk_sub_names `v info.univ_params.length in
let ul : list (name × level) := info.univ_params.zip (us.map level.param) in
let vl : list (name × level) := info.univ_params.zip (vs.map level.param) in
let up : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `α k, level.subst.app ul l)
) in
let vp : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `β k, level.subst.app vl l)
) in
let s0 : list format :=
[ "structure"
, format.cbrace (format.interspace $ (us ++ vs).map to_fmt)
, to_fmt info.hom_name
] in
let s1 : list format := up.map (λ ⟨n, l⟩,
  format.cbrace (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s2 : list format := vp.map (λ ⟨n, l⟩,
  format.cbrace (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s3 : list format := 
let usig : format := "@" ++ to_fmt info.sig_name ++ "." ++ format.cbrace (format.interspace $ us.map to_fmt) in
let vsig : format := "@" ++ to_fmt info.sig_name ++ "." ++ format.cbrace (format.interspace $ vs.map to_fmt) in
let lvl : level := level.normalize $ level.list_max (level.one :: (up ++ vp).map (λ ⟨_,l⟩, l)) in
[ format.paren $ format.interspace $ "sig_1 :" :: usig :: to_fmt <$> prod.fst <$> up
, format.paren $ format.interspace $ "sig_2 :" :: vsig :: to_fmt <$> prod.fst <$> vp
, "extends multi_function_" ++ to_fmt info.num_params
, format.interspace ((up ++ vp).map (λ ⟨n, _⟩, to_fmt n))
, ":"
, "Sort (" ++ to_fmt lvl ++ ")"
, ":="
] in
let s4 : list format := info.ops.map (λ ⟨n, c, d⟩,
  let xs : list name := mk_sub_names `x d.length in
  let rarg : list format := xs.map to_fmt in
  let larg : list format := (d.reverse.zip rarg).map $ λ ⟨i, x⟩, format.paren ("fn_" ++ to_fmt i ++ " " ++ x) in
  let rapp : format := format.interspace (("sig_1." ++ to_fmt n) :: rarg) in
  let rapp : format := "fn_" ++ to_fmt c ++ " " ++ format.paren rapp in
  let lapp : format := format.interspace (("sig_2." ++ to_fmt n) :: larg) in
  if d.length = 0
  then format.paren $ to_fmt n ++ " : " ++ lapp ++ " = " ++ rapp
  else format.paren $ to_fmt n ++ " : ∀ " ++ (format.interspace rarg) ++ ", " ++ lapp ++ " = " ++ rapp
) in
success $ format.interspace (s0 ++ s1 ++ s2 ++ s3 ++ s4)

meta def format_hom_eq (info : signature_info) : exceptional format :=
let us : list name := mk_sub_names `u info.univ_params.length in
let vs : list name := mk_sub_names `v info.univ_params.length in
let ul : list (name × level) := info.univ_params.zip (us.map level.param) in
let vl : list (name × level) := info.univ_params.zip (vs.map level.param) in
let up : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `α k, level.subst.app ul l)
) in
let vp : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `β k, level.subst.app vl l)
) in
let s0 : list format :=
[ "theorem"
, format.cbrace (format.interspace $ (us ++ vs).map to_fmt)
, to_fmt (info.hom_name ++ `eq)
] in
let s1 : list format := (up ++ vp).map (λ ⟨n, l⟩,
  format.cbrace (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s2 : list format :=
[ format.cbrace $ format.interspace 
  [ "s_1 :"
  , "@" ++ to_fmt info.sig_name
  , format.interspace (up.map $ λ ⟨n, _⟩, to_fmt n)
  ]
, format.cbrace $ format.interspace 
  [ "s_2 :"
  , "@" ++ to_fmt info.sig_name
  , format.interspace (vp.map $ λ ⟨n, _⟩, to_fmt n)
  ]
, ":"
, "∀ " ++ (format.dcbrace $ "f g : " ++ to_fmt info.hom_name ++ " s_1 s_2") ++ ","
, "f.to_multi_function_" ++ to_fmt info.num_params
, "="
, "g.to_multi_function_" ++ to_fmt info.num_params
, "→ f = g"
] in
let s3 : list format :=
[ "|"
, "⟨" ++ (format.join $ list.intersperse "," (list.repeat "_" (info.ops.length + 1))) ++ "⟩"
, "⟨" ++ (format.join $ list.intersperse "," (list.repeat "_" (info.ops.length + 1))) ++ "⟩"
, "rfl := rfl"
] in
success $ format.interspace (s0 ++ s1 ++ s2 ++ s3)

meta def format_hom_id (info : signature_info) : exceptional format :=
let us : list name := mk_sub_names `u info.univ_params.length in
let ul : list (name × level) := info.univ_params.zip (us.map level.param) in
let up : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `α k, level.subst.app ul l)
) in
let s0 : list format :=
[ "definition"
, format.cbrace (format.interspace $ us.map to_fmt)
, to_fmt info.hom_name ++ "_id"
] in
let s1 : list format := up.map (λ ⟨n, l⟩,
  format.cbrace (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s2 : list format :=
[ format.paren $ format.interspace 
  [ "s :"
  , "@" ++ to_fmt info.sig_name
  , format.interspace (up.map $ λ ⟨n, _⟩, to_fmt n)
  ]
, ":"
, to_fmt info.hom_name
, "s"
, "s"
, ":="
] in
let s3 : list format :=
[ "{"
, "to_multi_function_" ++ to_fmt info.num_params
, ":="
, "multi_function_" ++ to_fmt info.num_params ++ ".id"
] ++ info.ops.map (λ ⟨n,_⟩,
  ", " ++ to_fmt n ++ " := by intros; reflexivity"
) ++ ["}"] in
success $ format.interspace (s0 ++ s1 ++ s2 ++ s3)

meta def format_hom_comp (info : signature_info) : exceptional format :=
let us : list name := mk_sub_names `u info.univ_params.length in
let vs : list name := mk_sub_names `v info.univ_params.length in
let ws : list name := mk_sub_names `w info.univ_params.length in
let ul : list (name × level) := info.univ_params.zip (us.map level.param) in
let vl : list (name × level) := info.univ_params.zip (vs.map level.param) in
let wl : list (name × level) := info.univ_params.zip (ws.map level.param) in
let up : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `α k, level.subst.app ul l)
) in
let vp : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `β k, level.subst.app vl l)
) in
let wp : list (name × level) := info.param_meta_levels.enum.map (λ ⟨k, l⟩,
  (mk_sub_name `γ k, level.subst.app wl l)
) in
let s0 : list format :=
[ "definition"
, format.cbrace (format.interspace $ (us ++ vs ++ ws).map to_fmt)
, to_fmt info.hom_name ++ "_comp"
] in
let s1 : list format := (up ++ vp ++ wp).map (λ ⟨n, l⟩,
  format.cbrace (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s2 : list format := 
[ format.cbrace $ format.interspace 
  [ "s_1 :"
  , "@" ++ to_fmt info.sig_name
  , format.interspace (up.map $ λ ⟨n, _⟩, to_fmt n)
  ]
, format.cbrace $ format.interspace 
  [ "s_2 :"
  , "@" ++ to_fmt info.sig_name
  , format.interspace (vp.map $ λ ⟨n, _⟩, to_fmt n)
  ]
, format.cbrace $ format.interspace 
  [ "s_3 :"
  , "@" ++ to_fmt info.sig_name
  , format.interspace (wp.map $ λ ⟨n, _⟩, to_fmt n)
  ]
, format.paren $ "f : " ++ to_fmt info.hom_name ++ " s_2 s_3"
, format.paren $ "g : " ++ to_fmt info.hom_name ++ " s_1 s_2"
, ":"
, to_fmt info.hom_name ++ " s_1 s_3"
, ":="
] in
let s3 : list format := 
[ "{"
, "to_multi_function_" ++ to_fmt info.num_params
, ":="
, "multi_function_" ++ to_fmt info.num_params ++ ".comp"
, "f.to_multi_function_" ++ to_fmt info.num_params
, "g.to_multi_function_" ++ to_fmt info.num_params
] ++ info.ops.map (λ ⟨n,_,_⟩,
  ", " ++ to_fmt n ++ " := by intros; rw [f." ++ to_fmt n ++ ", g." ++ to_fmt n ++ "]"
) ++ ["}"] in
success $ format.interspace (s0 ++ s1 ++ s2 ++ s3)

meta def format_expr (info : signature_info) : exceptional format :=
let us : list name := mk_sub_names `u info.num_params in
let ts : list name := mk_sub_names `α info.num_params in
let s0 : list format :=
[ "inductive"
, format.cbrace (format.interspace $ us.map to_fmt)
, to_fmt info.expr_name
] in
let s1 : list format := (list.zip us ts).map (λ ⟨u, n⟩,
  format.paren (to_fmt n ++ " : Sort " ++ to_fmt u)
) in
let s2 : list format :=
let lvl : level := level.normalize $ level.list_max (level.one :: (info.params.map (λ ⟨_,l,_⟩, l))) in
[ ":"
, "nat → Sort (max 1 " ++ format.interspace (us.map to_fmt) ++ ")"
] in
let s3 : list format := ts.enum.map (λ ⟨k, n⟩,
  format.interspace ["| const_" ++ to_fmt k, ":", to_fmt n, "→", to_fmt info.expr_name, to_fmt k] 
) in
let s4 : list format := info.ops.map (λ ⟨n, c, d⟩, 
  let t : format := to_fmt $ info.expr_name in
  let f : format := d.foldl (λ f i, t ++ " " ++ to_fmt i ++ " → " ++ f) (t ++ " " ++ to_fmt c) in
  format.interspace ["|", to_fmt n, ":", f]
) in
success $ format.interspace (s0 ++ s1 ++ s2 ++ s3 ++ s4)

meta def format_expr_eval (info : signature_info) : exceptional format :=
let s0 : list format :=
[ "definition"
, format.cbrace $ format.interspace (info.univ_params.map to_fmt)
, to_fmt (info.expr_name ++ `eval)
] in
let s1 : list format := info.params.map (λ ⟨n, l, _⟩,
  format.cbrace (to_fmt n ++ " : Sort (" ++ to_fmt l ++ ")")
) in
let s2 : list format :=
[ format.paren ("s : @" ++ to_fmt info.sig_name ++ " " ++ format.interspace (info.params.map $ λ ⟨n,_⟩, to_fmt n))
, ":"
, to_fmt info.expr_name ++ " " ++ format.interspace (info.params.map $ λ ⟨n,_⟩, to_fmt n)

] in
success $ format.interspace (s0 ++ s1 ++ s2)

meta def format_trans (info : signature_info) (attr : name) : exceptional format :=
let s0 : list format := 
[ "@[user_attribute]"
, "meta"
, "def"
, to_fmt info.trans_name
, ":"
, "user_attribute"
, ":="
, "{ name := `" ++ to_fmt attr
, ", descr := \"" ++ to_fmt info.to_name ++ " translation attribute\""
, "}"
] in
success $ format.interspace s0

end parse

end signature_info

section signature_command
open lean lean.parser interactive

@[user_command]
meta def signature_command (_ : parse $ tk "signature") : parser unit :=
do {
  info ← signature_info.parse,
  emit (to_string $ info.format_sig),
  emit (to_string $ info.format_hom),
  emit (to_string $ info.format_hom_eq),
  emit (to_string $ info.format_hom_id),
  emit (to_string $ info.format_hom_comp),
  emit (to_string $ info.format_expr),
  full ← tactic.resolve_constant info.sig_name,
  emit (to_string $ info.format_trans $ full.get_prefix ++ info.trans_name.get_suffix),
  pure ()
}

end signature_command
