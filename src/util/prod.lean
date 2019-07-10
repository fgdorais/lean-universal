-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.


def prod.eq {α : Type*} {β : Type*} : Π {x y : prod α β}, x.fst = y.fst → x.snd = y.snd → x = y
| ⟨_, _⟩ ⟨_, _⟩ rfl rfl := rfl

def pprod.eq {α : Sort*} {β : Sort*} : Π {x y : pprod α β}, x.fst = y.fst → x.snd = y.snd → x = y
| ⟨_, _⟩ ⟨_, _⟩ rfl rfl := rfl
