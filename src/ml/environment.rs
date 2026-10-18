use super::Value;
use super::value::Namespace;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

/// Lexical values and SML identifier status travel together into closures.
#[derive(Clone, Debug, Default)]
pub(super) struct ValueEnvironment {
    values: BTreeMap<String, Value>,
    constructors: BTreeSet<String>,
}

impl Deref for ValueEnvironment {
    type Target = BTreeMap<String, Value>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl ValueEnvironment {
    pub fn insert(&mut self, name: String, value: Value) -> Option<Value> {
        self.constructors.remove(&name);
        self.values.insert(name, value)
    }

    pub fn mark_constructor(&mut self, name: &str) {
        self.constructors.insert(name.to_owned());
    }

    pub fn is_constructor(&self, name: &str) -> bool {
        self.constructors.contains(name)
    }

    pub fn extend(&mut self, values: impl IntoIterator<Item = (String, Value)>) {
        for (name, value) in values {
            self.insert(name, value);
        }
    }

    pub fn extend_exports(&mut self, values: Self) {
        self.extend(values.values);
        self.constructors.extend(values.constructors);
    }

    pub fn retain(&mut self, mut keep: impl FnMut(&str, &Value) -> bool) {
        self.values.retain(|name, value| keep(name, value));
        self.constructors.retain(|name| self.values.contains_key(name));
    }

    pub fn clear(&mut self) {
        self.values.clear();
        self.constructors.clear();
    }

    pub fn select(&self, names: &BTreeSet<String>) -> Self {
        let mut selected = Self::default();
        for name in names {
            if let Some(value) = self.values.get(name) {
                selected.insert(name.clone(), value.clone());
                if self.is_constructor(name) {
                    selected.mark_constructor(name);
                }
            }
        }
        selected
    }

    pub fn bind_namespace(&mut self, path: &str, namespace: &Namespace) {
        let prefix = format!("{path}.");
        self.retain(|name, _| !name.starts_with(&prefix));
        self.append_namespace(&prefix, namespace);
    }

    fn append_namespace(&mut self, prefix: &str, namespace: &Namespace) {
        for (name, value) in namespace.values.iter() {
            let qualified = format!("{prefix}{name}");
            if namespace.values.is_constructor(name) {
                self.constructors.insert(qualified.clone());
            }
            self.values.insert(qualified, value.clone());
        }
        for (name, nested) in &namespace.structures {
            self.append_namespace(&format!("{prefix}{name}."), nested);
        }
    }
}
