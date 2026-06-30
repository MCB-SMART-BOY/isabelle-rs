use std::fmt;

use super::{KernelError, Name};

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TyKind {
    Type { name: Name, args: Vec<Ty> },
}

/// Strict kernel type.
///
/// There is deliberately no `dummy` constructor. The reserved name `dummy` is
/// rejected by public constructors so compatibility uncertainty cannot enter
/// the new TCB as a normal type.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ty(TyKind);

impl Ty {
    pub fn base(name: impl Into<Name>) -> Result<Self, KernelError> {
        Self::apply(name, vec![])
    }

    pub fn apply(name: impl Into<Name>, args: Vec<Ty>) -> Result<Self, KernelError> {
        let name = name.into();
        if name.as_str() == "dummy" {
            return Err(KernelError::ReservedDummyType);
        }
        Ok(Ty(TyKind::Type { name, args }))
    }

    pub fn prop() -> Self {
        Ty(TyKind::Type { name: Name::from("prop"), args: vec![] })
    }

    pub fn arrow(from: Ty, to: Ty) -> Self {
        Ty(TyKind::Type { name: Name::from("fun"), args: vec![from, to] })
    }

    pub fn dest_arrow(&self) -> Option<(&Ty, &Ty)> {
        match &self.0 {
            TyKind::Type { name, args } if name.as_str() == "fun" && args.len() == 2 => {
                Some((&args[0], &args[1]))
            },
            _ => None,
        }
    }

    pub fn is_prop(&self) -> bool {
        self == &Ty::prop()
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            TyKind::Type { name, args } if args.is_empty() => write!(f, "{name}"),
            TyKind::Type { name, args } if name.as_str() == "fun" && args.len() == 2 => {
                write!(f, "({:?} => {:?})", args[0], args[1])
            },
            TyKind::Type { name, args } => f.debug_tuple(name.as_str()).field(args).finish(),
        }
    }
}
