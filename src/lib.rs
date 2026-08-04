//! Scala parser plugin — full-parse mode.
//!
//! Handles `.scala` and `.sc` files.
//! The plugin parses source with Tree-sitter inside Rust/Wasm.
//!
//! Semantic model:
//! - `class_definition`, `trait_definition`, `object_definition`, `case_class_definition`,
//!   `enum_definition`                        → class-like
//! - `function_definition`, `val_definition`  → method-like (when inside a class body)
//! - `function_definition` at top level       → method-like (Scala allows top-level defs)
//! - Labels: definitions → first identifier child.

use intentumdiff_plugin_sdk::{
    cst::CstNode,
    hash::structural_hash_with_memo,
    tree::{SemanticNode, SemanticNodeBuilder},
};

wit_bindgen::generate!({
    path: "wit/plugin.wit",
    world: "parser-plugin",
});

use crate::exports::intentumdiff::plugin::parser::ExamplePair;
use crate::exports::intentumdiff::plugin::parser::Guest;
use crate::exports::intentumdiff::plugin::parser::LanguageInfoRecord;
use crate::exports::intentumdiff::plugin::parser::ParserMode;

const PLUGIN_METADATA: &str = include_str!("../plugin_metadata.info");

fn language_info_for(ids: Vec<String>) -> Vec<LanguageInfoRecord> {
    let metadata = intentumdiff_plugin_sdk::metadata::parse_plugin_metadata(PLUGIN_METADATA);
    ids.into_iter()
        .map(|language_id| {
            let info = metadata.language_or_default(&language_id);
            LanguageInfoRecord {
                language_id: info.language_id,
                language_name: info.language_name,
                language_short_name: info.language_short_name,
                monaco_language: info.monaco_language,
                default_filename: info.default_filename,
                language_file_extensions: info.language_file_extensions,
                author: metadata.author().to_string(),
                plugin_version: metadata.plugin_version().to_string(),
                last_updated: metadata.last_updated().to_string(),
            }
        })
        .collect()
}
struct ScalaParser;

const TRIVIA: &[&str] = &["comment", "line_comment", "block_comment", "scala_doc"];

const SEMANTIC_TYPES: &[&str] = &[
    // Root
    "compilation_unit",
    // Package / import
    "package_clause",
    "package_object",
    "import_declaration",
    // Type definitions (class-like)
    "class_definition",
    "trait_definition",
    "object_definition",
    "case_class_definition",
    "enum_definition",
    "given_definition",
    // Members / functions (method-like)
    "function_definition",
    "function_declaration",
    "val_definition",
    "val_declaration",
    "var_definition",
    "var_declaration",
    "type_definition",
    "type_declaration",
    // Template body
    "template_body",
    "extends_clause",
    "derives_clause",
    // Statements
    "if_expression",
    "match_expression",
    "case_clause",
    "for_expression",
    "while_expression",
    "try_expression",
    "catch_clause",
    "finally_clause",
    "throw_expression",
    "return_expression",
    "block",
    "indented_block",
    // Expressions
    "call_expression",
    "generic_function",
    "field_expression",
    "assignment_expression",
    "infix_expression",
    "prefix_expression",
    "postfix_expression",
    "lambda_expression",
    "anonymous_function",
    "tuple_expression",
    "interpolated_string",
    "string",
    "char_literal",
    "integer_literal",
    "floating_point_literal",
    "boolean_literal",
    "null_literal",
    // Names
    "identifier",
    "stable_identifier",
    "type_identifier",
    // Patterns
    "pattern",
    "typed_pattern",
    "case_class_pattern",
    // Parameters
    "parameters",
    "parameter",
    "implicit_parameters",
    "using_parameters",
];

fn is_semantic(node_type: &str) -> bool {
    SEMANTIC_TYPES.contains(&node_type)
}

fn is_class_like(node_type: &str) -> bool {
    matches!(
        node_type,
        "class_definition"
            | "trait_definition"
            | "object_definition"
            | "case_class_definition"
            | "enum_definition"
            | "package_object"
    )
}

fn is_method_like(node_type: &str) -> bool {
    matches!(
        node_type,
        "function_definition" | "function_declaration" | "val_definition" | "val_declaration"
    )
}

fn label_for(node: &CstNode) -> String {
    if node.is_leaf() {
        return node.text_or_empty().to_string();
    }
    // Literal containers label with their captured source text (SDK-shared, issue #47).
    if let Some(label) = intentumdiff_plugin_sdk::ts_convert::literal_label(node) {
        return label;
    }
    match node.node_type.as_str() {
        "class_definition"
        | "trait_definition"
        | "object_definition"
        | "case_class_definition"
        | "enum_definition"
        | "package_object"
        | "given_definition" => {
            for child in &node.children {
                if matches!(child.node_type.as_str(), "identifier" | "type_identifier") {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "function_definition" | "function_declaration" => {
            for child in &node.children {
                if matches!(
                    child.node_type.as_str(),
                    "identifier" | "operator_identifier"
                ) {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "val_definition" | "val_declaration" | "var_definition" | "var_declaration" => {
            // `val foo: Type = value` — first identifier
            for child in &node.children {
                if matches!(child.node_type.as_str(), "identifier" | "pattern") {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "type_definition" | "type_declaration" => {
            for child in &node.children {
                if matches!(child.node_type.as_str(), "identifier" | "type_identifier") {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "package_clause" => {
            for child in &node.children {
                if matches!(child.node_type.as_str(), "stable_identifier" | "identifier") {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "import_declaration" => {
            if let Some(first) = node.children.first() {
                return first.text_or_empty().to_string();
            }
        }
        "call_expression" => {
            if let Some(first) = node.children.first() {
                return first.text_or_empty().to_string();
            }
        }
        _ => {}
    }
    for child in &node.children {
        if matches!(child.node_type.as_str(), "identifier" | "type_identifier") {
            return child.text_or_empty().to_string();
        }
    }
    node.node_type.clone()
}

fn convert(
    node: &CstNode,
    id_prefix: &str,
    parent_class: Option<&str>,
    memo: &mut std::collections::HashMap<usize, String>,
) -> Option<SemanticNode> {
    convert_semantic_classed(
        node,
        id_prefix,
        parent_class,
        memo,
        &|t| TRIVIA.contains(&t),
        &is_semantic,
        &is_class_like,
        &is_method_like,
        &label_for,
    )
}



use intentumdiff_plugin_sdk::ts_convert::{convert_semantic_classed, node_to_cst};

fn parse_source(source: &str) -> Result<CstNode, String> {
    let mut parser = tree_sitter::Parser::new();
    let lang = tree_sitter_scala::LANGUAGE.into();
    parser
        .set_language(&lang)
        .map_err(|_| "Failed to load scala grammar".to_string())?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| "Parse failed".to_string())?;
    Ok(node_to_cst(tree.root_node(), source.as_bytes()))
}

fn process_impl(source: &str) -> String {
    let root: CstNode = match parse_source(source) {
        Ok(n) => n,
        Err(e) => return format!(r#"{{\"error\":\"{}\"}}"#, e),
    };
    let mut memo = std::collections::HashMap::new();
    let sem = match convert(&root, "0", None, &mut memo) {
        Some(n) => n,
        None => return r#"{"error":"Empty semantic tree"}"#.to_string(),
    };
    match serde_json::to_string(&sem) {
        Ok(s) => s,
        Err(e) => format!(r#"{{"error":"Serialisation error: {}"}}"#, e),
    }
}

impl Guest for ScalaParser {
    fn get_parser_mode() -> ParserMode {
        ParserMode::FullParse
    }
    fn grammar_id() -> String {
        "scala".to_string()
    }
    fn detect_language(filename: String, _content: String) -> String {
        let lower = filename.to_lowercase();
        if lower.ends_with(".scala") || lower.ends_with(".sc") {
            return "scala".to_string();
        }
        String::new()
    }
    fn preprocess_source(source: String) -> String {
        source
    }
    fn process(input: String, _language: String, _filename: String) -> String {
        process_impl(&input)
    }
    fn trivia_node_types() -> Vec<String> {
        TRIVIA.iter().map(|s| s.to_string()).collect()
    }
    fn language_ids() -> Vec<String> {
        vec!["scala".to_string()]
    }
    fn language_info() -> Vec<LanguageInfoRecord> {
        language_info_for(Self::language_ids())
    }
    fn priority() -> i32 {
        0
    }

    fn example(_language: String) -> ExamplePair {
        ExamplePair {
            old: "object Main {\n  def greet(name: String): Unit = {\n    println(\"Hello, \" + name)\n  }\n\n  def add(a: Int, b: Int): Int = a + b\n}\n".to_string(),
            new: "object Main {\n  def greet(name: String): Unit = {\n    println(s\"Hello, $name!\")\n  }\n\n  def add(x: Int, y: Int): Int = x + y\n\n  def multiply(x: Int, y: Int): Int = x * y\n}\n".to_string(),
        }
    }
}
export!(ScalaParser);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exports::intentumdiff::plugin::parser::Guest;
    use intentumdiff_plugin_sdk::testing as t;

    #[test]
    fn grammar_id_nonempty() {
        assert!(!ScalaParser::grammar_id().is_empty());
    }

    #[test]
    fn language_ids_contain_grammar_id() {
        let gid = ScalaParser::grammar_id();
        let ids = ScalaParser::language_ids();
        assert!(
            ids.contains(&gid),
            "language_ids {:?} must contain {:?}",
            ids,
            gid
        );
    }

    #[test]
    fn detect_language_known_ext() {
        let r = ScalaParser::detect_language("test.scala".to_string(), "".to_string());
        assert_eq!(r.as_str(), "scala");
    }

    #[test]
    fn detect_language_unknown_ext() {
        let r =
            ScalaParser::detect_language("test.xyz_notareal_ext_9z8y".to_string(), "".to_string());
        assert_eq!(r.as_str(), "");
    }

    #[test]
    fn parser_mode_is_full_parse() {
        assert!(matches!(
            ScalaParser::get_parser_mode(),
            ParserMode::FullParse
        ));
    }

    #[test]
    fn process_impl_accepts_raw_example_source() {
        let example = ScalaParser::example(ScalaParser::grammar_id());
        let out = process_impl(&example.old);
        t::assert_valid_json(&out, "process(raw example)");
        assert!(!out.contains("\"error\""), "{out}");
    }
    #[test]
    fn process_impl_empty_returns_valid_json() {
        let out = process_impl("");
        t::assert_valid_json(&out, "process(empty)");
    }

    #[test]
    fn process_impl_whitespace_returns_valid_json() {
        let out = process_impl("   \n  ");
        t::assert_valid_json(&out, "process(whitespace)");
    }
}
