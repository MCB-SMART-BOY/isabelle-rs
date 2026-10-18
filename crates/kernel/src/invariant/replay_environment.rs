use std::collections::BTreeSet;

use crate::{CProp, CTerm, InstEntry, KernelError, Name, ProofContext, Ty, TypeInstantiation};

const SOURCE_SCOPE_DEPTH: usize = 0;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FreeGrant {
    name: Name,
    ty: Ty,
    scope_depth: usize,
}

/// Lexical replay permissions, never part of a public proof context or owner.
#[derive(Clone)]
pub(super) struct ReplayEnvironment {
    pub(super) context: ProofContext,
    frees: BTreeSet<FreeGrant>,
    scope_depth: usize,
}

impl ReplayEnvironment {
    pub(super) fn new(context: &ProofContext) -> Self {
        let frees = context
            .replay_frees()
            .into_iter()
            .map(|(name, ty)| FreeGrant { name, ty, scope_depth: SOURCE_SCOPE_DEPTH })
            .collect();
        Self { context: context.clone(), frees, scope_depth: SOURCE_SCOPE_DEPTH }
    }

    pub(super) fn context_for_bound(&self) -> std::borrow::Cow<'_, ProofContext> {
        self.context.for_replay(
            self.frees.iter().map(|grant| (grant.name.clone(), grant.ty.clone())).collect(),
        )
    }

    pub(super) fn validate_cprop(&self, prop: &CProp, is_erased: bool) -> Result<(), KernelError> {
        self.context.validate_replay_cprop(
            prop,
            &mut |name, ty| self.require_free(name, ty),
            is_erased,
        )
    }

    pub(super) fn validate_cterm(&self, term: &CTerm) -> Result<(), KernelError> {
        self.context.validate_replay_cterm(term, &mut |name, ty| self.require_free(name, ty))
    }

    pub(super) fn with_free(&self, name: &Name, ty: &Ty) -> Result<Self, KernelError> {
        self.context.validate_type(ty)?;
        let mut scoped = self.clone();
        if !self.has_free(name, ty) {
            scoped.frees.insert(FreeGrant {
                name: name.clone(),
                ty: ty.clone(),
                scope_depth: SOURCE_SCOPE_DEPTH,
            });
        }
        scoped.validate_identities()?;
        Ok(scoped)
    }

    pub(super) fn bind_free(&self, name: &Name, ty: &Ty) -> Result<Self, KernelError> {
        self.context.validate_type(ty)?;
        let scope_depth = self
            .scope_depth
            .checked_add(1)
            .ok_or_else(|| KernelError::Invariant("replay binder depth exhausted".into()))?;
        let mut scoped = self.clone();
        scoped.scope_depth = scope_depth;
        scoped.frees.insert(FreeGrant { name: name.clone(), ty: ty.clone(), scope_depth });
        scoped.validate_identities()?;
        Ok(scoped)
    }

    pub(super) fn without_binding(mut self, original: &Self) -> Self {
        // A binding's descendants retain its origin through every type mapping.
        // Sibling scopes reuse depths only after all grants from that scope expire.
        self.frees.retain(|grant| grant.scope_depth <= original.scope_depth);
        self.scope_depth = original.scope_depth;
        self
    }

    pub(super) fn generalize(
        &self,
        types: &BTreeSet<Name>,
        terms: &BTreeSet<Name>,
        index: usize,
    ) -> Result<Self, KernelError> {
        let frees = self
            .frees
            .iter()
            .filter(|grant| !terms.contains(&grant.name))
            .map(|grant| {
                Ok(FreeGrant {
                    name: grant.name.clone(),
                    ty: grant.ty.generalize_type(types, index)?,
                    scope_depth: grant.scope_depth,
                })
            })
            .collect::<Result<_, KernelError>>()?;
        let mapped = Self { context: self.context.clone(), frees, scope_depth: self.scope_depth };
        mapped.validate_identities()?;
        Ok(mapped)
    }

    pub(super) fn instantiate(
        &self,
        types: &TypeInstantiation,
        subst: &[InstEntry],
    ) -> Result<Self, KernelError> {
        self.context.validate_type_instantiation(types)?;
        let frees = self
            .frees
            .iter()
            .map(|grant| {
                Ok(FreeGrant {
                    name: grant.name.clone(),
                    ty: grant.ty.subst_type_vars(types)?,
                    scope_depth: grant.scope_depth,
                })
            })
            .collect::<Result<_, KernelError>>()?;
        let mut mapped =
            Self { context: self.context.clone(), frees, scope_depth: self.scope_depth };
        // replay_rule already certified every RHS in this source environment.
        // Term replacements enter after the type pass and are not rewritten again.
        for entry in subst {
            crate::bound_proof::visit_free_variables(
                entry.replacement().term(),
                &mut |name, ty| {
                    mapped.frees.extend(
                        self.frees
                            .iter()
                            .filter(|grant| &grant.name == name && &grant.ty == ty)
                            .cloned(),
                    );
                },
            );
        }
        mapped.validate_identities()?;
        Ok(mapped)
    }

    pub(super) fn merge(&mut self, other: &Self) -> Result<(), KernelError> {
        super::require_same_context(self.context.stamp(), other.context.stamp())?;
        if !self.context.has_same_type_scope(&other.context) || other.scope_depth > self.scope_depth
        {
            return Err(KernelError::AcceptanceReplayMismatch);
        }
        self.frees.extend(other.frees.iter().cloned());
        self.validate_identities()
    }

    fn require_free(&self, name: &Name, ty: &Ty) -> Result<(), KernelError> {
        if self.has_free(name, ty) {
            return Ok(());
        }
        Err(KernelError::UndeclaredFree(name.clone()))
    }

    fn has_free(&self, name: &Name, ty: &Ty) -> bool {
        self.frees.iter().any(|grant| &grant.name == name && &grant.ty == ty)
    }

    fn validate_identities(&self) -> Result<(), KernelError> {
        let mut identities = crate::typ::TypeIdentityMap::default();
        for grant in &self.frees {
            self.context.validate_type(&grant.ty)?;
            identities.validate(&grant.ty)?;
        }
        Ok(())
    }
}
