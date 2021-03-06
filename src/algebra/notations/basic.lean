-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .reserved

class {u v} has_lmul (α : Type u) (β : Type v) := (lmul : α → β → β)
infixl ∙ := has_lmul.lmul
