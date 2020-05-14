-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

namespace exceptional

meta def orelse (α : Type) : exceptional α → exceptional α → exceptional α
| (success x) _ := success x
| (exception _) (success x) := success x
| (exception m₁) (exception m₂) := exception (λ o, m₁ o ++ "; " ++ m₂ o)

meta instance : has_orelse exceptional := ⟨orelse⟩

end exceptional
