; The order of the patterns must be preserved, or maintained alongside the
; users of this query. Unfortunately there is no efficient way of identifying
; a query pattern except its index.

; Pattern #0
; module.exports = identifier produces an unnamed identifier
(
  (assignment_expression
    left: (member_expression
      object: (identifier) @cjs-module
      property: (property_identifier) @cjs-exports)
    right: (identifier) @target-ident)
  (#eq? @cjs-module "module")
  (#eq? @cjs-exports "exports")
)

; Pattern #1
; module.exports = function () {} produces an unnamed scope
(
  (assignment_expression
    left: (member_expression
      object: (identifier) @cjs-module
      property: (property_identifier) @cjs-exports)
    right: (_ body: (_) @target-scope))
  (#eq? @cjs-module "module")
  (#eq? @cjs-exports "exports")
)

; Pattern #2
; module.exports = { a, b, c } produces [a, b, c]
(
  (assignment_expression
    left: (member_expression
      object: (identifier) @cjs-module
      property: (property_identifier) @cjs-exports)
    right: (object) @target-object)
  (#eq? @cjs-module "module")
  (#eq? @cjs-exports "exports")
)

; Pattern #3
; module.exports.foo = ... produces [foo]
(
  (assignment_expression
    left: (member_expression
      object: (member_expression
        object: (identifier) @cjs-module
        property: (property_identifier) @cjs-exports)
      property: (property_identifier) @target-name)
    right: (_) @target-object)
  (#eq? @cjs-module "module")
  (#eq? @cjs-exports "exports")
)

; Pattern #4
; exports.foo = ... produces [foo] (rare, but happens)
(
  (assignment_expression
    left: (member_expression
      object: (identifier) @cjs-exports
      property: (property_identifier) @target-name)
    right: (_) @target-object)
  (#eq? @cjs-exports "exports")
)
