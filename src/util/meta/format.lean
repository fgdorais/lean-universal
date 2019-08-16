-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.


meta def binder_info.to_fmt : binder_info → format → format
| binder_info.default := format.paren
| binder_info.implicit := format.cbrace
| binder_info.inst_implicit := format.sbracket
| binder_info.strict_implicit := format.dcbrace
| binder_info.aux_decl := format.paren

meta def format.quote : format → format := format.bracket "\"" "\""

/-- insert spaces between list items -/
meta def format.interspace : list format → format :=
λ l, format.join $ l.intersperse format.space

/-- insert line breaks between list items -/
meta def format.interline : list format → format :=
λ l, format.join $ l.intersperse format.line
