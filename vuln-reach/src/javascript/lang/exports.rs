//! ESM and CommonJS exports.
use std::collections::{HashMap, HashSet};

use lazy_static::lazy_static;
use tree_sitter::{Node, Query, QueryCursor};

use crate::{Error, Tree, JS};

// CommonJS
//
// All the compatible export statements in CommonJS are the following:
// 1. module.exports = an object, an identifier, or a function
//
//    When this is found, override all previous exports.
//
// 2. module.exports.foo = anything
//
//    When this is found, override exports of the same name only.
//
// 3. exports.foo = anything
//
//    This is compatible with 2., but if there is even one instance of 1., this
//    definition does nothing. This is because the module-global `exports` is a
//    shorthand for `module.exports`, but if something is assigned to
//    `module.exports`, this simply gets cloaked and the reference gets lost.
//
// For the time, we only care about top-level exported objects,
// i.e.:
//
// Ok: module.exports = { a, b, c }
// Ok: module.exports.a = ...
// Ok: exports.a = ...
// No: module.exports.foo.bar = ... (is anyone _that_ evil?)
#[derive(Debug)]
pub enum CommonJsExports<'a> {
    Name(Node<'a>),
    Scope(Node<'a>),
    // The value in this map can either be an identifier or a scope. The
    // pathfinder should match this against its list of scopes first and,
    // failing that, retrieve the correspondingly named identifier and its
    // scope.
    Object(HashMap<&'a str, Node<'a>>),
    None,
}

impl<'a> TryFrom<&'a Tree> for CommonJsExports<'a> {
    type Error = Error;

    fn try_from(tree: &'a Tree) -> Result<Self, Self::Error> {
        let mut cur = QueryCursor::new();

        lazy_static! {
            static ref QUERY: Query =
                Query::new(*JS, include_str!("../queries/commonjs-exports.lsp")).unwrap();
        };

        let mut exports_object = CommonJsExports::Object(Default::default());
        let mut found = false;

        // For a given node, find the one that can track accesses.
        fn exportable_node(node: Node<'_>) -> Node<'_> {
            if let Some(body) = node.child_by_field_name("body") {
                // Function nodes that have a child field called `body` return
                // that, since it's a scope.
                body
            } else {
                // Return the node itself by default. Note: primarily this is
                // intended for identifiers, which are to be looked up as-is,
                // but for the moment it also works the same for other kinds of
                // nodes, should any such edge cases crop up.
                node
            }
        }

        for query_match in cur.matches(&QUERY, tree.root_node(), tree.buf().as_bytes()) {
            match query_match.pattern_index {
                0 => {
                    // module.exports = identifier
                    let target_ident = query_match.captures[2].node;
                    exports_object = CommonJsExports::Name(target_ident);
                    found = true;
                },
                1 => {
                    // module.exports = function () { ... }
                    let target_scope = query_match.captures[2].node;
                    exports_object = CommonJsExports::Scope(target_scope);
                    found = true;
                },
                2 => {
                    // module.exports = { a, b, c ... }
                    //
                    // Parse an object, which can only be one of:
                    // - (pair key: _, value: _) save the statement block iff there is any one
                    //   present under value
                    // - (spread_element) we don't care
                    // - (method_definition name: _ body: (statement_block)) save the statement
                    //   block
                    // - (shorthand_property_identifier) resolve later to surrounding scope
                    let mut object_map = HashMap::default();

                    let target_object = query_match.captures[2].node;
                    let mut cur = target_object.walk();
                    for object_entry in target_object.children(&mut cur) {
                        match object_entry.kind() {
                            "pair" => {
                                let key = object_entry.child_by_field_name("key").unwrap();
                                let value = exportable_node(
                                    object_entry.child_by_field_name("value").unwrap(),
                                );
                                object_map.insert(tree.repr_of(key), value);
                            },
                            "method_definition" => {
                                let name = object_entry.child_by_field_name("name").unwrap();
                                let stmt = object_entry.child_by_field_name("body").unwrap();
                                object_map.insert(tree.repr_of(name), stmt);
                            },
                            "shorthand_property_identifier" => {
                                object_map.insert(tree.repr_of(object_entry), object_entry);
                            },
                            _ => {},
                        }
                    }

                    exports_object = CommonJsExports::Object(object_map);
                    found = true;
                },
                3 => {
                    // module.exports.foo = ...
                    if let CommonJsExports::Object(ref mut object_map) = &mut exports_object {
                        let target_name = query_match.captures[2].node;
                        let target_object = exportable_node(query_match.captures[3].node);
                        object_map.insert(tree.repr_of(target_name), target_object);
                    }
                    found = true;
                },
                4 => {
                    // exports.foo = ...
                    if let CommonJsExports::Object(ref mut object_map) = &mut exports_object {
                        let target_name = query_match.captures[1].node;
                        let target_object = exportable_node(query_match.captures[2].node);
                        object_map.insert(tree.repr_of(target_name), target_object);
                    }

                    // silently fail if module.exports not an object: it will
                    // look like assigning to the properties of a function or a
                    // primitive object, which is, respectively, already accounted
                    // for by the pathfinder, and invalid JS.
                    found = true;
                },
                k => unreachable!("{}: {:#?}", k, query_match),
            }
        }

        Ok(if found { exports_object } else { CommonJsExports::None })
    }
}

// ESM Exports
//
// All the compatible ESM export statements are the following:
// 1. export declaration
//    - export let a, b
//    - export const a = 1, b = 2
//    - XXX export { name: value } is _not_ valid!
// 2. export list
//    - export { a, b, c }
//    - export { a as b, c as "d with spaces" }
//    - export { something as default }
// 3. export default declaration (identifier|object|function|class)
// 4. export default <expression>
//
// Unsupported statements:
// 5. export * from "module" / export { default } from "module" / export { name
// } from "module"
#[derive(Debug, Default)]
pub struct EsmExports<'a> {
    // The nodes in this map can either be identifiers or scopes. The
    // pathfinder should match this against its list of scopes first and,
    // failing that, retrieve the correspondingly named identifier and its
    // scope.
    pub objects: HashMap<&'a str, EsmExport<'a>>,
    pub default: Option<EsmExport<'a>>,
    // Contains a vector of all full-module exports. At this point, we can't
    // know what the exported names are, because we haven't processed the
    // reexported module.
    pub reexports: HashSet<Reexport<'a>>,
}

#[derive(Debug)]
pub enum EsmExport<'a> {
    // Perform a module-scoped symbol lookup of this node.
    Name(Node<'a>),
    // Mark all reachable nodes in this scope as reachable through this export.
    Scope(Node<'a>),
    // Mark all identifier nodes inside of the expression as reachable.
    // XXX needs an expression evaluation module.
    Expression(Node<'a>),
}

impl<'a> EsmExport<'a> {
    pub fn node(&self) -> Node<'a> {
        match self {
            EsmExport::Name(node) | EsmExport::Scope(node) | EsmExport::Expression(node) => *node,
        }
    }

    // Determine if the expression export contains the specified node.
    pub fn expression_contains(&self, node: Node<'a>) -> bool {
        match self {
            EsmExport::Name(_) | EsmExport::Scope(_) => false,
            EsmExport::Expression(export) => {
                export.start_byte() <= node.start_byte() && export.end_byte() >= node.end_byte()
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Reexport<'a> {
    All(&'a str),
    Named(&'a str, Option<&'a str>, &'a str),
}

impl<'a> TryFrom<&'a Tree> for Option<EsmExports<'a>> {
    type Error = Error;

    fn try_from(tree: &'a Tree) -> Result<Self, Self::Error> {
        let mut cur = QueryCursor::new();

        lazy_static! {
            static ref QUERY: Query =
                Query::new(*JS, include_str!("../queries/esm-exports.lsp")).unwrap();
        };

        let mut exports = EsmExports::default();
        let mut found = false;

        for query_match in cur.matches(&QUERY, tree.root_node(), tree.buf().as_bytes()) {
            match query_match.pattern_index {
                0 => {
                    // export let name = 1
                    // export const name = 1
                    let export_decl = query_match.captures[0].node;
                    exports.objects.insert(tree.repr_of(export_decl), EsmExport::Name(export_decl));
                    found = true;
                },
                1 => {
                    // export function name() {}
                    // export function* name() {}
                    // export class ClassName {}
                    //
                    // These are the equivalent of `function name() {}; export name`.
                    let export_name = query_match.captures[0].node;
                    let export_scope = query_match.captures[1].node;

                    // The grammar has a quirk where `export default function foo() {}` will
                    // look exactly like `export function foo() {}`; but that is misleading
                    // because in the former case the exported identifier is `default` and in
                    // the latter it is `foo`. So we need to manually match the first child
                    // of the export statement and confirm that it is in fact the literal
                    // `default`; use this to decide whether to insert the export in the
                    // default slot or in the objects.
                    let parent = export_name.parent().unwrap().parent().unwrap();
                    if let Some("default") = parent.child(1).map(|c| tree.repr_of(c)) {
                        exports.default = Some(EsmExport::Scope(export_scope));
                    } else {
                        exports
                            .objects
                            .insert(tree.repr_of(export_name), EsmExport::Name(export_name));
                    }
                    found = true;
                },
                2 => {
                    // export { foo, bar, baz as quux }
                    let export_spec = query_match.captures[0].node;
                    let name = export_spec.child_by_field_name("name").unwrap();
                    let alias = export_spec.child_by_field_name("alias");
                    exports
                        .objects
                        .insert(tree.repr_of(alias.unwrap_or(name)), EsmExport::Name(name));
                    found = true;
                },
                3 => {
                    // export default function name() {}
                    // export default function* name() {}
                    // export default class ClassName {}
                    // export default function () {}
                    // export default function* () {}
                    // export default class {}
                    let export_scope = query_match.captures[0].node;
                    // Discard previous export, if it exists: there can only
                    // ever be a single default export.
                    exports.default = Some(EsmExport::Scope(export_scope));
                    found = true;
                },
                4 => {
                    // export default identifier
                    let export_ident = query_match.captures[0].node;
                    // Discard previous export, if it exists: there can only
                    // ever be a single default export.
                    exports.default = Some(EsmExport::Name(export_ident));
                    found = true;
                },
                5 | 6 => {
                    // export const { foo, bar } = baz
                    let export_pattern = query_match.captures[0].node;
                    let export_source = query_match.captures[1].node;
                    exports
                        .objects
                        .insert(tree.repr_of(export_pattern), EsmExport::Name(export_source));
                    found = true;
                },
                7 => {
                    // export default { a: 1, b: 2 }
                    let export_value = query_match.captures[0].node;
                    exports.default = Some(EsmExport::Expression(export_value));
                    found = true;
                },
                8 => {
                    // export * from 'foo'
                    // export { a as b, c } from 'foo'
                    if query_match.captures.len() == 1 {
                        let export_source = tree.repr_of(query_match.captures[0].node);
                        exports.reexports.insert(Reexport::All(export_source));
                    } else {
                        let export_clause = query_match.captures[0].node;
                        let export_source = tree.repr_of(query_match.captures[1].node);

                        for spec in (0..export_clause.named_child_count())
                            .filter_map(|i| export_clause.named_child(i))
                        {
                            let name = tree.repr_of(spec.child_by_field_name(b"name").unwrap());
                            let alias =
                                spec.child_by_field_name(b"alias").map(|node| tree.repr_of(node));
                            exports.reexports.insert(Reexport::Named(name, alias, export_source));
                        }
                    }
                    found = true;
                },
                k => unreachable!("{}: {:#?}", k, query_match),
            }
        }

        Ok(if found { Some(exports) } else { None })
    }
}

#[derive(Debug)]
pub enum Exports<'a> {
    Esm(EsmExports<'a>),
    CommonJs(CommonJsExports<'a>),
    None,
}

impl<'a> Exports<'a> {
    pub fn new(tree: &'a Tree) -> Self {
        if let Ok(Some(esm_exports)) = Option::<EsmExports>::try_from(tree) {
            Exports::Esm(esm_exports)
        } else if let Ok(cjs_exports) = CommonJsExports::try_from(tree) {
            Exports::CommonJs(cjs_exports)
        } else {
            Exports::None
        }
    }
}

// Very coarse grained functions for telling whether a JS file contains an
// export at all.

pub fn has_exports_cjs(tree: &Tree) -> bool {
    let mut cur = QueryCursor::new();

    lazy_static! {
        static ref QUERY: Query = Query::new(
            *JS,
            r#"
            (
                (member_expression
                    object: (identifier) @module
                    property: (property_identifier) @exports)
                (#eq? @module "module")
                (#eq? @exports "exports")
            )
            (
                (identifier) @exports
                (#eq? @exports "exports")
            )
            "#
        )
        .unwrap();
    };

    cur.matches(&QUERY, tree.root_node(), tree.buf().as_bytes()).count() > 0
}

pub fn has_exports_mjs(tree: &Tree) -> bool {
    let mut cur = QueryCursor::new();

    lazy_static! {
        static ref QUERY: Query = Query::new(*JS, r#"(export_statement)"#).unwrap();
    };

    cur.matches(&QUERY, tree.root_node(), tree.buf().as_bytes()).count() > 0
}

#[test]
fn test_module_exports() {
    let tree = Tree::new(r#"module.exports = function () {}"#.to_string()).unwrap();
    assert!(matches!(CommonJsExports::try_from(&tree), Ok(CommonJsExports::Scope(_))));

    let tree = Tree::new(
        r#"
        module.exports = { a, b, c }
        module.exports.foo = function () {}
        "#
        .to_string(),
    )
    .unwrap();
    let exports = CommonJsExports::try_from(&tree).unwrap();
    println!("{:#?}", exports);
    assert!(matches!(exports, CommonJsExports::Object(e) if e.len() == 4));

    let tree = Tree::new(
        r#"
        module.exports = {
            a, b, c,
            foo() {},
            d: function() {},
            e: {}
        }
        "#
        .to_string(),
    )
    .unwrap();
    let exports = CommonJsExports::try_from(&tree).unwrap();
    println!("{:#?}", exports);
    assert!(matches!(exports, CommonJsExports::Object(e) if e.len() == 6));
}

#[test]
fn test_esm_exports() {
    let tree = Tree::new(
        r#"
            // Exporting declarations
            export let name1, name2; // also var
            export const name3 = 1, name4 = 2; // also var, let
            export function functionName() {}
            export class ClassName {}
            export function* generatorFunctionName() {}
            export const { name5, name6: bar } = o;
            export const [ name7, name8 ] = array;

            // Export list
            export { name9, name10 };
            export { variable1 as name11, variable2 as name12, name13 };
            export { variable1 as "string name" };
            export { name14 as default };

            // Default exports
            export default expression;
            export default function defaultFunctionName() {}
            export default class DefaultClassName {}
            export default function* DefaultGeneratorFunctionName() {}
            export default function () {}
            export default class {}
            export default function* () {}
        "#
        .to_string(),
    )
    .unwrap();
    let exports = Option::<EsmExports>::try_from(&tree).unwrap().unwrap();
    println!("{:#?}", exports);

    assert!(matches!(exports.objects.get("name1"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name2"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name3"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name4"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name5"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name6"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name7"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name8"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name9"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name10"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name11"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name12"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.objects.get("name13"), Some(EsmExport::Name(_))));
    assert!(matches!(exports.default, Some(EsmExport::Scope(_))));

    assert!(exports.objects.get("DefaultClassName").is_none());
    assert!(exports.objects.get("defaultFunctionName").is_none());
    assert!(exports.objects.get("defaultGeneratorFunctionName").is_none());

    assert!(exports.objects.get("ClassName").is_some());
    assert!(exports.objects.get("functionName").is_some());
    assert!(exports.objects.get("generatorFunctionName").is_some());

    assert_eq!(exports.objects.len(), 18);
}

#[test]
fn test_esm_reexport() {
    let tree = Tree::new(
        r#"
            // Aggregating modules
            export * from "module-name";
            export { name2, nameN } from "module-name";
            export { import1 as name3, import2 as name4, name5 } from "module-name";
            export { default } from "module-name";
            export { default as foo } from "module-name";
        "#
        .to_string(),
    )
    .unwrap();
    let exports = Option::<EsmExports>::try_from(&tree).unwrap().unwrap();
    println!("{:#?}", exports);

    macro_rules! assert_reexport_contains {
        ($pattern:pat_param) => {
            assert!(exports.reexports.iter().find(|e| matches!(e, $pattern)).is_some());
        };
    }

    assert_eq!(exports.reexports.len(), 8);
    assert_reexport_contains!(Reexport::All("module-name"));
    assert_reexport_contains!(Reexport::Named("name2", None, "module-name"));
    assert_reexport_contains!(Reexport::Named("nameN", None, "module-name"));
    assert_reexport_contains!(Reexport::Named("import1", Some("name3"), "module-name"));
    assert_reexport_contains!(Reexport::Named("import2", Some("name4"), "module-name"));
    assert_reexport_contains!(Reexport::Named("name5", None, "module-name"));
    assert_reexport_contains!(Reexport::Named("default", None, "module-name"));
    assert_reexport_contains!(Reexport::Named("default", Some("foo"), "module-name"));
}
