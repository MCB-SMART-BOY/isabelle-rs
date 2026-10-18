// Each integration binary compiles this shared fixture module with a different helper subset.
#![allow(dead_code)]

use serde_json::{Value, json};
use sha1::{Digest, Sha1};
use xtask::reference::common::digest_bytes;
use xtask::reference::decode_inventory::ROOTS;

#[derive(Clone)]
pub struct Element {
    pub tag: String,
    pub attrs: Vec<(String, String)>,
    pub body: Vec<Fragment>,
}
#[derive(Clone)]
pub enum Fragment {
    Text(String),
    Node(Element),
}
impl Element {
    pub fn new(tag: &str) -> Self {
        Self { tag: tag.into(), attrs: vec![], body: vec![] }
    }
    pub fn attrs(mut self, fields: &[(&str, &str)]) -> Self {
        self.attrs = fields.iter().map(|(key, value)| ((*key).into(), (*value).into())).collect();
        self
    }
    pub fn nodes(mut self, children: Vec<Element>) -> Self {
        self.body = children.into_iter().map(Fragment::Node).collect();
        self
    }
    pub fn text(mut self, text: &str) -> Self {
        self.body.push(Fragment::Text(text.into()));
        self
    }
    pub fn node(&mut self, index: usize) -> &mut Element {
        match &mut self.body[index] {
            Fragment::Node(node) => node,
            _ => panic!("expected fixture element"),
        }
    }
    pub fn set(&mut self, key: &str, value: &str) {
        self.attrs.iter_mut().find(|field| field.0 == key).expect("fixture attribute").1 =
            value.into();
    }
    pub fn serialize(&self) -> String {
        let mut raw = format!("\u{5}\u{6}{}", self.tag);
        for (key, value) in &self.attrs {
            raw.push_str(&format!("\u{6}{key}={value}"));
        }
        raw.push('\u{5}');
        for part in &self.body {
            match part {
                Fragment::Text(text) => raw.push_str(text),
                Fragment::Node(node) => raw.push_str(&node.serialize()),
            }
        }
        raw.push_str("\u{5}\u{6}\u{5}");
        raw
    }
}
pub fn element(tag: &str, fields: &[(&str, &str)]) -> Element {
    Element::new(tag).attrs(fields)
}
pub fn write_source(root: &std::path::Path, path: &str, data: &[u8]) {
    let destination = root.join(path);
    std::fs::create_dir_all(destination.parent().expect("fixture parent"))
        .expect("create fixture dir");
    std::fs::write(destination, data).expect("write fixture bytes");
}
pub fn source_workspace(root: &std::path::Path) -> (Value, String) {
    let mut theories = vec![];
    let mut hashes = serde_json::Map::new();
    for name in std::iter::once("Pure").chain(ROOTS) {
        let relative = format!("src/{}.thy", name.replace('.', "/"));
        let bytes = format!("theory {name}\nbegin\nend\n");
        write_source(root, &relative, bytes.as_bytes());
        hashes.insert(relative.clone(), json!(digest_bytes(bytes.as_bytes())));
        theories.push(json!({"name":name,"source":relative}));
    }
    let resource = "src/HOL/Tools/probe.ML";
    write_source(root, resource, b"val observed = true;\n");
    (
        json!({"schema_version":1,"reference":"Isabelle2025","roots":ROOTS,"theories":theories,"source_sha256":hashes}),
        resource.into(),
    )
}
pub fn sha1_hex(bytes: &[u8]) -> String {
    base16ct::lower::encode_string(&Sha1::digest(bytes))
}
pub fn command(name: &str, source: &str, line: &str, offset: &str, files: Vec<Element>) -> Element {
    element(
        "command",
        &[
            ("name", name),
            ("source", source),
            ("line", line),
            ("offset", offset),
            ("skipped", "false"),
        ],
    )
    .nodes(files)
}
