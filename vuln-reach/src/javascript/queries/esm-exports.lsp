; The order of the patterns must be preserved, or maintained alongside the
; users of this query. Unfortunately there is no efficient way of identifying
; a query pattern except its index.

; Pattern #0
;
; export let name = 1
; export const name = 1
(export_statement
    !source
    declaration: [
        (lexical_declaration (variable_declarator name: (identifier) @export-decl))
        (variable_declaration (variable_declarator name: (identifier) @export-decl))
    ])

; Pattern #1
;
; export function name() {}
; export function* name() {}
; export class ClassName {}
(export_statement
    !source
    declaration: [
        (_
            name: (identifier) @export-decl
            body: (statement_block) @export-scope)
        (class_declaration
            name: (identifier) @export-decl
            body: (class_body) @export-scope)
    ])

; Pattern #2
; export_specifier has a `name` field and, optionally, an `alias` field.
;
; export { foo, bar, baz }
(export_statement
    !source
    (export_clause (export_specifier) @export-list-spec))

; Pattern #3
;
; export default function name() {}
; export default function* name() {}
; export default class ClassName {}
; export default function () {}
; export default function* () {}
; export default class {}
(export_statement
    !source
    value: [
        (function body: (statement_block) @export-scope)
        (generator_function body: (statement_block) @export-scope)
        (class body: (class_body) @export-scope)
    ])

; Pattern #4
;
; export default identifier
(export_statement
    !source
    value: (identifier) @export-name)

; Pattern #5
;
; export const { foo, bar } = baz
; export let { foo, bar } = baz
; export var { foo, bar } = baz
;
; Object pattern is a special case because export names are linked to the
; pattern's RHS rather than getting picked up straight from the scope in which
; they are defined.
(export_statement
    !source
    declaration: (_
        (variable_declarator
            name: (object_pattern [
                (shorthand_property_identifier_pattern) @export-pattern
                (pair_pattern key: (_) @export-pattern)])
            value: (_) @export-source)))

; Pattern #6
;
; export const [foo, bar] = baz
; export let [foo, bar] = baz
; export var [foo, bar] = baz
;
; Same as above
(export_statement
    !source
    declaration: (_
        (variable_declarator
            name: (array_pattern (_) @export-pattern)
            value: (_) @export-source)))

; Pattern #7
;
; export default { a: 1, b: 2 }
;
; Same as above
(export_statement
    !source
    value: (_) @export-value)

; Pattern #8
;
; export * from 'source'
; export { a as b, c } from 'source'
(export_statement
    (export_clause)? @export_clause
    source: (string (string_fragment) @export-source))
