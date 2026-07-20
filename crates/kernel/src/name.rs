use std::{fmt, sync::Arc};

/// Internable logical name used by the strict kernel nucleus.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(Arc<str>);

impl Name {
    pub fn as_str(&self) -> &str {
        self.0.as_ref()
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Self {
        Name(Arc::from(value))
    }
}

impl From<String> for Name {
    fn from(value: String) -> Self {
        Name(Arc::from(value))
    }
}

impl From<Arc<str>> for Name {
    fn from(value: Arc<str>) -> Self {
        Name(value)
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Name").field(&self.0).finish()
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
