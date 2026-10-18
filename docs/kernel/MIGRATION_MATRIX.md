# Core-to-Kernel Migration Matrix

## Status

Initial migration matrix, maintained as a current boundary inventory alongside
the dated 2026-10-03 `HOL::TrueI` transitional experiment below. On
2026-10-07 an audited projection of the bundled `HOL::TrueI` source reaches
`KernelTrustedClosed: 1/125`, `TransitionalStrictClosed: 0/125`. The two
standalone accepted fixtures do not enter the sampled count; unrelated HOL/ML
commands are not executed.

This inventory does not certify P2/P3/P4 native compatibility, despite resumed
implementation and separately executed Rust THM consumer closures. Its 125-case
counts predate the automation migration; no fresh sampled source acceptance
follows from those consumer runs or the historical official reference inventory.
Consult [current delivery state](../status/PROJECT_STATUS.md#current-delivery-state)
and the [Rust THM inventory](../status/NATIVE_THM_INTERFACE_INVENTORY.md).

## Migration Principles

- `crates/kernel` is the TCB; `src/kernel/mod.rs` is its root re-export.
- `src/core` remains a legacy proof engine, to be shrunk into compatibility,
  automation, diagnostics, and migration adapters.
- Core changes are allowed only when they harden boundaries, improve
  diagnostics, or enable migration.
- The current `ProofOutcome::TransitionalStrictClosed` is transitional legacy accounting;
  final acceptance must converge on a distinct `KernelTrustedClosed` result
  carrying a context-bound `src/kernel::TrustedTheorem` with `CProp : prop`.
- The current Cargo workspace (`root`, `isabelle-kernel`,
  `isabelle-evidence`, `xtask`) is not a proof-session/runtime workspace split;
  offline evidence and build orchestration grant no theorem authority. APP,
  general LSP/PIDE parity, HPC, Burn, and CubeCL are not delivered by it.

## Matrix

The target-architecture and next-step columns below are migration planning,
not completed capability or permission to add trusted rules. Dated native
consumer evidence and outstanding gates live in
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19).

| Area | Current state | Risk | Target architecture | Next migration step | Blocking tests |
|---|---|---|---|---|---|
| Isar method export | Shared `proof_result` checks actual Strict/checked results, the complete proposition, permitted hypotheses, and scoped export. Source methods are checked without implicit Auto fallback. | Legacy Strict is not a new-kernel accepted token; unsupported composition fails. | Migrate each caller atomically to exact-owner acceptance. | Preserve closed-result and scope invariants during sampled migration. | `legacy_proof_contract`, `legacy_proof_state_contract`, `legacy_pure_rule_contract`. |
| Simplifier | Core/HOL rewriting checks cached endpoints, instantiates the whole theorem, and composes App/Abs/deep certificates. Conditional/open/admitted rules reject. | Compatibility search remains untrusted; conditional rewriting is not implemented. | Automation supplies candidates whose full evidence is checked. | Keep Free rigid and preserve trust without promoting Compat. | `automation_rewrite_contract`. |
| Theorem database acceptance | HOL/global/theory tables filter legacy closed results with `is_strict_closed_proved()`. The sampled `HOL::TrueI` projection separately returns an accepted token; standalone fixtures are outside the sample. | Searchable legacy facts can be misread as kernel proof progress. | Final trusted tables accept only `KernelTrustedClosed` values bound to immutable theory/logic context; searchable and transitional databases preserve taint. | Connect other production HOL storage only after migrating its source, basis, and definition checks. | Reports show `TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125`; the projection is not whole-theory compilation. |
| Proofterm replay | `src/core/proofterm.rs` supports a small replay subset; `src/kernel` replays current strict derivations with exact context stamps, scoped Pure binder introduction, and accepted-token theorem references. | Replay success can still be confused with closed theorem acceptance. | Replay is an independent check in the exact immutable owner ancestry, never a replacement for closed acceptance. | Maintain owner-local scoping and dependency replay while broadening frontend coverage. | Existing replay/tampering, stale/sibling token, scoped binder, dependency-order/kind, and deterministic-ID attacks. |
| Parser / certifier | Strict source supports standalone HOL TrueI, explicit PROP Pure identity by assumption, and audited sampled `HOL::TrueI` projection. The strict signature declares type constructors and arities before use; basis installation checks complete axiom schemas and replay checks definition certificates. Legacy term/type parsing consumes complete inputs and binds lexical variables as Bound. | Search diagnostics may retain explicitly incomplete terms; neither AST nor spans grant authority. | Owner-aware elaboration and certification, without equating a projection to whole-theory source loading. | Extend syntax only with complete consumption and declarations. | `kernel_declaration_boundary`, strict source rejection tests, `tests/sampled_true_i.rs`. |
| HOL loader | `HolTheoremDb` remains a searchable legacy fact index. For sampled `HOL::TrueI` alone, a bound complete source yields an audited projection and a distinct accepted token. | Searchable facts can be mistaken for new-kernel trusted facts. | HOL loader keeps searchable facts separate from context-bound kernel-trusted facts. | Extend source-backed integration beyond `TrueI`, preserving exclusive token classification. | `KernelTrustedClosed` increases only from a context-bound new-kernel theorem, never a legacy outcome label. |
| Resolution family | Strict kernel has conservative `resolve1_match`/`subst_premise`/`bicompose` plus separate checked `bicompose_candidate`, `lift_rule` and assumption paths. | Limited Rust bound-proof candidates and partial lifting do not implement complete Isabelle/ML bicompose, general higher-order unification or `Seq`. | Kernel-backed `proof_search` owns trusted resolution transitions; core resolution remains legacy/adapters. | Extend only with source-backed need and separate rule review; a Rust THM consumer does not authorize general HOL resolution. | Existing bicompose/subst and `pure_composition` regression suites; full ML resolution acceptance remains open. |
| Tools / simp front-end | `src/tools/simp.rs` consumes legacy rewrite rules and facts. | Tool success may be confused with a trusted theorem derivation. | Tools produce candidates, scripts, or proof terms; strict replay accepts or rejects. | Keep tool outputs classified as search/automation until replayed. | Tool tests must assert no open/admitted rule is treated as unconditional proved rewrite. |
| Complete theory loading | `TheoryProcessor` publishes only complete single-import files; real types persist in the signature. Session registry is rebuilt per run. | Broad declarations/multi-imports remain unsupported; independent session files are not one atomic transaction. | Headless checked document runtime after the kernel milestone. | Preserve failure isolation without pretending unsupported commands succeeded. | `theory_load_contract`, `session_load_contract`. |
| ATP/Metis/Meson | Complete goal and proof burden are checked at result boundaries. ATP steps consume actual named evidence; bad evidence never falls back to local search. | Supported proof syntax/rules are narrow; external process status is not proof authority. | Replayable automation candidates, not trusted search hits. | Keep unknown rules, duplicate names, and mismatched formulas fail-closed. | `automation_proof_contract`, `sledgehammer_e2e`. |

## Completed Transitional Strict-Closed Experiment

At the 2026-10-03 checkpoint (separate from the two accepted standalone
HOL/Pure fixtures), the sampled legacy result was:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

The checked legacy `HOL::TrueI` theorem was bool-valued, not an accepted
`CProp : prop`. The historical synthetic Pure identity `A ==> A` did not count
in the sample. The legacy object-reflexivity and definition-transport bridge
were subsequently removed. The last recorded bundled sample was
`TransitionalStrictClosed: 0/125`, `KernelTrustedClosed: 1/125`: only the
audited source-backed `HOL::TrueI` projection obtains an exact-owner accepted
token in that sample. Neither standalone fixture nor later external Rust THM
consumer contributes to that total.

The 2026-10-03 diagnostic scan of 125 candidates found no parsed proposition
of the form `A ==> A` / `P ==> P`; this scan is not current telemetry.

Candidate slices:

| Candidate | Why it is useful | Required pieces | First-slice suitability |
|---|---|---|---|
| Pure reflexivity `t == t` | Smallest strict kernel theorem construction path. | Checked term certification, `KernelRules::reflexive`, closed acceptance. | Good kernel/acceptance smoke test, but may not map directly to a current core lemma. |
| Pure implication identity `A ==> A` | Exercises assumption introduction and legal discharge. | Checked `CProp`, `KernelRules::assume`, `KernelRules::implies_intr`, context-bound acceptance. | Existing synthetic smoke; reuse next for correct/wrong-context acceptance tests, not as a sampled HOL result. |
| Simple equality reflexivity exposed through HOL | Potential later user-visible reuse. | Source-aware elaboration, HOL basis, immutable context, generic replay. | Not a second transitional slice and not current work. |
| `HOL::TrueI` | First sampled HOL lemma with a small proof: `unfolding True_def by (rule refl)`. | Audited exact source declaration/proof projection, HOL `refl` basis, generic conservative `True_def`, Pure transport and owner replay. | Accepted only as a narrow sampled projection (`1/125`); not whole-theory HOL compilation. |

### Historical `HOL::TrueI` Transitional Slice Contract (2026-10-03)

Target source theorem:

```isabelle
lemma TrueI: True
  unfolding True_def by (rule refl)
```

Historical 2026-10-03 targeted diagnostic (no longer the current verifier):

| Item | Then-observed state |
|---|---|
| Source theory | `theories/HOL/HOL.thy` |
| Parsed theorem | `TrueI`, prop `True`, proof `unfolding True_def by (rule refl)` |
| Legacy `verify_lemma` result | bool-valued legacy theorem, `TransitionalStrictClosed` |
| `True_def` checked payload | separate from theorem facts |
| HOL object-equality/reflexivity bridge | then implemented; since removed |
| `try_strict_hol_refl` / `try_strict_hol_true_i` | then implemented; since removed |
| Checked-definition fold-back | then implemented for checked `True_def`; since removed |

The following legacy checks describe only that historical experiment:

- theorem name is exactly `TrueI`;
- parsed proposition is exactly the declared HOL constant `True`;
- the source proof is exactly the supported shape
  `unfolding True_def by (rule refl)`;
- `True_def` is available as a checked definition, not merely as a declaration
  side effect;
- unfolding `True_def` produces the expected reflexive object equality
  `((λx::bool. x) = (λx. x))`;
- the reflexive equality is constructed by a strict path, not by the compat
  `refl` fact then stored in `HolTheoremDb`;
- the final legacy result has no hypotheses, no unresolved `tpairs`, no
  oracle/admit footprint, no dummy types, and satisfies
  `is_strict_closed_proved()`.

These conditions did not make that result kernel-trusted: its conclusion was
`HOL.True : bool`, without immutable theory/logic identity or a
`src/kernel::TrustedTheorem` over `CProp : prop`.

The former adapter rejected into the explicit admitted path, without entering
legacy proof fallback, if:

- `True_def` is missing from the checked definition environment;
- `True_def` or the unfolded RHS contains dummy/compat-only certification;
- the unfolded RHS is not a reflexive equality of the same term;
- the available `refl` fact is compat/admitted/open;
- any ambient hypothesis, unresolved `tpair`, oracle/admit footprint, or dummy
  type would remain.

Current conclusion: the historical legacy adapter was replaced by a
source-bound `try_strict_adapter` in `src/isar/method.rs`. Its
`Proved(TrustedTheory, TrustedTheorem)` result is accepted after audited
bundled-source projection and exact-owner replay; failed shape hits reject
without falling back to legacy proof. See
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) for the
remaining boundary; do not revive the theorem-specific legacy bridge.

The ranked scan of the remaining 124 sampled theorems is recorded in
[NEXT_STRICT_SLICE_CANDIDATES.md](../design/NEXT_STRICT_SLICE_CANDIDATES.md). It recommends
`HOL::trans` only as the first consumer of a reusable checked HOL equality
substitution slice, not as another theorem-specific primitive or direct branch.

That consumer is blocked on the theorem-independent contract in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](../design/CHECKED_HOL_PROPOSITION_NORMALIZATION.md)
and the Proposed object-logic boundary in
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).
The diagnostic confirms that `HOL::trans` needs shared polymorphic type
constraints, checked `HOL.Trueprop` judgment extraction, and exact preservation
of its `Pure.imp` / `HOL.eq` skeleton before any proof rule is considered.

### HOL Object-Equality / Reflexivity Bridge Contract

This bridge is removed. See
[HOL_OBJECT_EQUALITY_BRIDGE.md](../design/HOL_OBJECT_EQUALITY_BRIDGE.md) for
its historical contract. It did not reuse compat `refl` or Pure reflexivity
as if they directly proved HOL object equality.

The historical narrow bridge was:

```text
try_strict_hol_refl(t)
  input:
    checked HOL term t : α
  required declarations:
    HOL.eq : α => α => bool
  output:
    legacy transitional theorem for HOL.eq t t : bool, with no hyps, tpairs,
    oracle/admit footprint, or dummy types
```

That bridge was documented as a HOL object-logic primitive/bridge, not a
rewrite, simp, unfolding, or general object-logic prover.

It had to reject:

- undeclared or dummy-typed `HOL.eq`;
- unchecked, compat, or dummy-tainted input terms;
- non-reflexive `HOL.eq lhs rhs` shapes;
- any attempt to derive HOL object equality by treating `Pure.eq` as
  interchangeable with `HOL.eq`;
- any compat/admitted/open `refl` fact.

Completed transitional sequence (retained as migration history, not the target
kernel-trust sequence):

```text
1. strict Pure implication identity as a direct parser/certifier/export smoke test (done)
2. make `True_def` available as a checked definition source (done; non-theorem input only)
3. implement the strict HOL object-equality/reflexivity bridge needed by `TrueI` (done)
4. implement checked-definition transport/fold-back for checked `True_def` (done)
5. implement strict `HOL::TrueI` only as a narrow adapter over those checked pieces (done)
```

## Next Engineering Gates

1. Preserve exact-owner acceptance for the audited sampled `HOL::TrueI`
   projection and the two independent fixtures; no legacy trust upgrade.
2. Extend declaration-aware source elaboration to other sampled lemmas only
   with complete syntax, basis and proof checks.
3. Reconsider general `HOL::trans` only after the shared checked HOL equality
   contract is available; no theorem-specific trusted HOL constructors.
4. Resume admitted-reason reduction without widening legacy trusted power.
