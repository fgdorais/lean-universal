-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.


theorem not_exists_of_forall_not {α : Sort*} {p : α → Prop} :
(∀ x, ¬ p x) → ¬ (∃ x, p x) := λ h ⟨x, hx⟩, h x hx

theorem not_exists_iff_forall_not {α : Sort*} (p : α → Prop) :
¬ (∃ x, p x) ↔ (∀ x, ¬ p x) := ⟨forall_not_of_not_exists, not_exists_of_forall_not⟩
