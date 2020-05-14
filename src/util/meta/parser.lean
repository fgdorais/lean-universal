-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.


meta def lean.parser.of_exceptional {α} : exceptional α → lean.parser α
| (exceptional.success x) := pure x
| (exceptional.exception m) := failure

meta instance (α) : has_coe_to_sort (exceptional α) := ⟨_, lean.parser.of_exceptional⟩

meta def lean.parser.emit : string → lean.parser unit :=
λ str, lean.parser.with_input lean.parser.command_like str >>= 
λ ⟨_, str⟩, if str.length = 0 then pure () else lean.parser.emit str
