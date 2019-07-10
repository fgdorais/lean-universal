-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .exceptional
import .name
import .format

namespace level

meta def one : level := level.succ level.zero

meta def list_max : list level → level
| [] := level.zero
| [l] := l
| (l::ls) := level.max l $ list_max ls

meta def params : list name → list level := list.map level.param

meta def num_params (root : name) (len : nat) (fst : nat := 0) : list level :=
params $ mk_num_names root len fst

meta def sub_params (root : name) (len : nat) (fst : nat := 0) : list level :=
params $ mk_sub_names root len fst

meta def mvars : list name → list level := list.map level.mvar

meta def num_mvars (root : name) (len : nat) (fst : nat := 0) : list level :=
mvars $ mk_num_names root len fst

meta def sub_mvars (root : name) (len : nat) (fst : nat := 0) : list level :=
mvars $ mk_sub_names root len fst

meta def metaify : level → list name → level
| (level.succ l) ns := level.succ (l.metaify ns)
| (level.max l₁ l₂) ns := level.max (l₁.metaify ns) (l₂.metaify ns)
| (level.imax l₁ l₂) ns := level.imax (l₁.metaify ns) (l₂.metaify ns)
| l@(level.param nm) (n :: ns) := if nm = n then level.mvar nm else l.metaify ns
| l _ := l

meta def subst : Type := list (name × level) 

namespace subst
open exceptional

meta def nil : subst := []

meta def get : subst → name → level
| ((n, l) :: s) nm := if n = nm then l else get s nm
| [] nm := level.mvar nm

meta def app : subst → level → level
| s (level.mvar n) := s.get n
| s (level.succ l) := level.succ (s.app l)
| s (level.max l₁ l₂) := level.max (s.app l₁) (s.app l₂)
| s (level.imax l₁ l₂) := level.imax (s.app l₁) (s.app l₂)
| s l := l

meta def pop : subst → name → option level × subst
| (i :: s) n := 
  let p := pop s n in
  if i.fst = n
  then (some i.snd, p.snd)
  else (p.fst, i :: p.snd)
| [] nm := (none, [])

meta def new : subst → name := λ s, mk_num_name `_x s.length

meta def delete : subst → name → subst :=
λ s n, let p := pop s n in p.snd

meta def update : subst → name → level → subst :=
λ s n l, (n, l) :: delete s n

meta def unify : subst → level → level → exceptional subst
| s (level.mvar n₁) (level.mvar n₂) :=
  let (l₁, s) := s.pop n₁ in
  let (l₂, s) := s.pop n₂ in
  match l₁, l₂ with
  | some l₁, some l₂ := s.unify l₁ l₂ >>= λ s, success $ (n₁, l₁) :: (n₁, l₁) :: s
  | some l₁, none := success $ (n₂, l₁) :: s
  | none, some l₂ := success $ (n₁, l₂) :: s
  | none, none := success s
  end
| s (level.mvar n) l₂ :=
  let (l₁, s) := s.pop n in
  match l₁ with
  | some l₁ := s.unify l₁ l₂
  | none := success $ (n, level.normalize $ s.app l₂) :: s
  end
| s l₁ l₂@(level.mvar _) := s.unify l₂ l₁

| s l@(level.param _) r := if l = r then success s else fail ""

| s level.zero level.zero := success s
| s l@level.zero r := s.unify r l

| s (level.succ _) (level.zero) := fail ""
| s (level.succ l₁) (level.succ l₂) := s.unify l₁ l₂
| s l@(level.succ _) r := s.unify r l

| s (level.max l₁ l₂) (level.zero) :=
  s.unify l₁ level.zero >>= λ s, s.unify l₂ level.zero
| s (level.max l₁ l₂) (level.succ r) :=
  let n₁ := s.new in let m₁ := level.mvar n₁ in
  s.unify (level.succ m₁) l₁ >>= λ s,
  let n₂ := s.new in let m₂ := level.mvar n₂ in
  s.unify (level.succ m₂) l₂ >>= λ s,
  s.unify (level.max m₁ m₂) r
| s (level.max l₁ l₂) (level.max r₁ r₂) :=
  (s.unify l₁ r₁ >>= λ s, s.unify l₂ r₂) <|>
  (s.unify l₁ r₂ >>= λ s, s.unify l₂ r₁)
| s l@(level.max _ _) r := s.unify r l

| s (level.imax _ l) (level.zero) :=
  s.unify l level.zero
| s (level.imax l₁ l₂) r@(level.succ _) :=
  s.unify (level.max l₁ l₂) r
| s (level.imax l₁ l₂) (level.max r₁ r₂) :=
  s.unify l₂ r₂ >>= λ s, (s.unify l₁ r₂ <|> s.unify l₂ level.zero)
| s (level.imax l₁ l₂) (level.imax r₁ r₂) :=
  s.unify l₁ r₁ >>= λ s, s.unify l₂ r₂
| s l@(level.imax _ _) r := s.unify r l

end subst

meta def to_format' : level → format
| (level.zero) := "0"
| (level.succ l) := 
  format.paren $ format.interspace ["succ", to_format' l]
| (level.max l₁ l₂) := 
  format.paren $ format.interspace ["max", to_format' l₁, to_format' l₂] 
| (level.imax l₁ l₂) := 
  format.paren $ format.interspace ["imax", to_format' l₁, to_format' l₂] 
| (level.param n) := to_fmt n
| (level.mvar n) := "?" ++ to_fmt n

end level
