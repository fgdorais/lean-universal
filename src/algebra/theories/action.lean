-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic

namespace algebra

signature left_action (α : Type*) (β : Type*) := 
(act : α → β → β)

class left_action {α : Type*} {β : Type*} (s : left_action_sig α β) : Prop := intro ::

namespace left_action
variables {α : Type*} {β : Type*} (s : left_action_sig α β)

abbreviation infer : left_action s := left_action.intro s

definition fold : list α → β → β
| [] x := x
| (y::ys) x := s.act y (fold ys x)

@[simp] theorem fold_nil (x) : fold s [] x = x := rfl

@[simp] theorem fold_cons (x y ys) : fold s (y::ys) x = s.act y (fold s ys x) := rfl

@[simp] theorem fold_append (x) : ∀ ys zs, fold s (ys ++ zs) x = fold s ys (fold s zs x)
| [] zs := rfl
| (y::ys) zs :=
  show s.act y (fold s (ys ++ zs) x) = s.act y (fold s ys (fold s zs x)),
  by rw fold_append

end left_action

signature right_action (α : Type*) (β : Type*) := 
(act : β → α → β)

class right_action {α : Type*} {β : Type*} (s : right_action_sig α β) : Prop := intro ::

namespace right_action
variables {α : Type*} {β : Type*} (s : right_action_sig α β) 

abbreviation infer : right_action s := right_action.intro s

definition fold : β → list α → β
| x [] := x
| x (y::ys) := s.act (fold x ys) y

@[simp] theorem fold_nil (x) : fold s x [] = x := rfl

@[simp] theorem fold_cons (x y ys) : fold s x (y::ys) = s.act (fold s x ys) y := rfl

@[simp] theorem fold_append (x) : ∀ ys zs, fold s x (ys ++ zs) = fold s (fold s x zs) ys
| [] zs := rfl
| (y::ys) zs := 
  show s.act (fold s x (ys ++ zs)) y = s.act (fold s (fold s x zs) ys) y,
  by rw fold_append

end right_action

end algebra