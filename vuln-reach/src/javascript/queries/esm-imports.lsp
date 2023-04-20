; The order of the patterns must be preserved, or maintained alongside the
; users of this query. Unfortunately there is no efficient way of identifying
; a query pattern except its index.

; Pattern #0
;
; import name from "module"
(import_statement
    (import_clause (identifier) @import-default)
    source: (string (string_fragment) @import-source))

; Pattern #1
;
; import * as name from "module"
(import_statement
    (import_clause (namespace_import (identifier) @import-star))
    source: (string (string_fragment) @import-source))

; Pattern #2
;
; import { foo } from "module"
; import { foo as bar } from "module"
(import_statement
    (import_clause (named_imports (import_specifier) @import-spec))
    source: (string (string_fragment) @import-source))
