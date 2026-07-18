// Classification: design-only standalone template; not production code.
#![allow(dead_code)]

macro_rules! marker {
    ($($name:ident),+ $(,)?) => { $(
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct $name;
    )+ };
}

marker!(
    CheckedCProp,
    HolNormalizationProvenance,
    ParsedProposition,
    CheckedHolSignature,
    CheckedProofContext,
    SyntaxPath,
    SourceName,
    ConstantId,
    TermKind,
    TypeScheme,
    Typ,
    SourceSymbol,
    KernelError,
);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedHolProposition {
    pub proposition: CheckedCProp,
    pub provenance: HolNormalizationProvenance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HolPropositionNormalizationError {
    MissingSourceProposition,
    UnexpectedSkeleton { path: SyntaxPath },
    AmbiguousName { path: SyntaxPath, name: SourceName },
    WrongHeadKind { path: SyntaxPath, expected: ConstantId, actual: TermKind },
    MissingDeclaration { constant: ConstantId },
    DeclarationMismatch { constant: ConstantId, expected: TypeScheme, actual: Typ },
    ExplicitAnnotationConflict { path: SyntaxPath, expected: Typ, actual: Typ },
    VariableKindMismatch { symbol: SourceSymbol, expected: TermKind, actual: TermKind },
    TypeConstraintConflict { left: SyntaxPath, right: SyntaxPath, left_type: Typ, right_type: Typ },
    UnresolvedType { path: SyntaxPath },
    PureObjectEqualityConfusion { path: SyntaxPath },
    LegacySourceMismatch,
    UnsupportedSyntax { path: SyntaxPath },
    SkeletonMismatch,
    CertificationFailed(KernelError),
}

/// The function is intentionally non-theorem-producing.
pub fn normalize_checked_hol_proposition(
    _parsed: &ParsedProposition,
    _signature: &CheckedHolSignature,
    _context: &CheckedProofContext,
) -> Result<CheckedHolProposition, HolPropositionNormalizationError> {
    Err(HolPropositionNormalizationError::MissingSourceProposition)
}
