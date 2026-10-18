# HPC Symbolic Compute Design

Status: deferred, untrusted-only proposal. No packed compute module,
Burn/CubeCL dependency or accelerator-to-theorem API is implemented.
The two standalone source-backed fixture tokens are outside the historical
bundled HOL sample. Its audited `HOL::TrueI` projection yielded
`KernelTrustedClosed: 1/125` (`TransitionalStrictClosed: 0/125`); the
subsequently resumed P2/P3/P4 native closure implementation has not rerun
this sampler. Neither that result nor historical official reference observations
authorize this optional performance track. See
[ROADMAP.md](../status/ROADMAP.md).

## Goal

Add a future backend-agnostic high-performance symbolic compute layer for
mechanical proof-assistant workloads:

```text
term/fact fingerprinting
fact prefiltering
rewrite-rule candidate filtering
finite-domain counterexample search
batch proof-obligation quick rejection
```

This is not an AI chat-assistant track and not a neural-premise-ranking track,
although neural ranking may later use the same packed representations. The
first objective is Rust-native CPU/GPU/multi-backend acceleration of mechanical
symbolic computation around proof search.

## Non-Goals

Do not use this track to build:

```text
GPU trusted kernel
GPU theorem acceptance
GPU full unification
GPU full bicompose
GPU complete simplifier
GPU proofterm replay as a trusted gate
```

The separate CPU `isabelle-kernel` crate is the only authority for checked
theorem acceptance. Compute backends may generate candidates, scores,
fingerprints or certificate drafts; they may never create a
`TrustedTheorem`, accepted token, or legacy proof result on their own.

## Backend Positioning

Burn and CubeCL are candidates for a future backend, not current dependencies.

Burn is a Rust dynamic deep-learning framework that also emphasizes runtime
optimization, JIT compilation, tensor operation streams, auto-tuning, and
portable compute efficiency. CubeCL is the lower-level Rust compute language,
compiler, and runtime layer behind Burn's accelerated backends; its stated
target is writing kernels once in Rust and running them across backends such as
CUDA, ROCm/HIP, Metal, SPIR-V/Vulkan/WGPU/WGSL, and CPU SIMD.

References:

```text
https://burn.dev/
https://github.com/tracel-ai/burn
https://github.com/tracel-ai/cubecl
```

The project should evaluate these as optional symbolic-compute substrates only
after a deterministic CPU baseline and packed symbolic IR exist.

## Trust Boundary

The mandatory data flow is:

```text
Existing term/fact/rule indexes
  -> untrusted packed candidate representation
  -> optional CPU/GPU compute
  -> candidate ids / scores / fingerprints / certificate drafts
  -> lookup exact source objects and perform CPU proof/search step
  -> strict kernel certification and owner-bound replay/acceptance
  -> TrustedTheorem only on success
```

## Hard Invariants

These are trust-boundary requirements, not implementation suggestions:

1. `crates/kernel` must not depend on compute, Burn, CubeCL or backend crates.
2. Compute must not construct `KernelThm`, `ClosedThm`, `OpenThm`,
   `TrustedTheorem`, or legacy `Thm` as proof evidence.
3. Compute must not construct certified `CTerm` or `CProp`.
4. Compute must not call `CTerm::from_certified_subterm` or another
   kernel-crate-private certified-by-origin helper.
5. Its outputs are candidate IDs, scores, fingerprints, diagnostics or drafts.
6. CPU proof/search code must re-check any suggested substitution, rewrite or
   proof step before theorem state changes.
7. Hash/fingerprint equality is never term equality or a proof.
8. Packed IR is an index/cache, not a certified AST; unpacked theorem-facing
   terms require ordinary declaration-aware certification and derivation.
9. Candidate IDs must resolve to existing, authorized source facts, rules or
   subterms. They confer no owner/theorem-reference authority.
10. Backend nondeterminism may affect only search order after deterministic
    tie-breaking, never theorem acceptance.

## Candidate-Only Output Model

The compute layer can only narrow or rank work for trusted CPU paths. Its
outputs must point back to existing source objects:

The shared candidate and backend design types are maintained in the
design-only standalone
[symbolic_compute_backend.rs](../../scripts/templates/symbolic_compute_backend.rs)
template. Its compilation does not validate a production compute API.

The follow-up CPU path must:

```text
candidate id
  -> lookup original fact/rule/subterm
  -> exact CPU match / rewrite / resolution attempt
  -> kernel rule / replay / check
```

It must not do:

```text
candidate generated term
  -> CTerm / CProp
  -> theorem
```

unless the generated term is re-parsed or re-certified through the normal
trusted boundary and then proved by existing kernel rules.

## Target Layering

Future target modules or crates may look like:

```text
isabelle-kernel (existing crates/kernel)
  trusted CPU LCF kernel; no compute dependency

isabelle-index (proposed)
  packed views and search indexes, no theorem authority

isabelle-compute
  backend-agnostic symbolic compute traits and CPU baseline

isabelle-compute-burn
  optional Burn/CubeCL backend, feature-gated

isabelle-automation
  simp/auto/metis-like orchestration; consumes index/compute candidates

isabelle-session
  incremental checking and cache
```

## Dependency Direction

Allowed dependency direction:

```text
automation/search/index -> compute
automation/search       -> kernel
compute                 -> packed symbolic data only
kernel                  -> no compute dependency
```

This preserves ADR-0001: compatibility/search layers can be untrusted and
useful, while theorem construction remains confined to the kernel.

Forbidden dependency direction:

```text
kernel -> compute
kernel -> Burn/CubeCL/GPU backend
compute -> kernel theorem constructors
compute -> strict CTerm/CProp constructors
```

## Isabelle-Style User Experience

This track must not change the proof language users see.

The surface remains:

```isabelle
lemma ...
  by simp
```

or:

```isabelle
proof
  ...
qed
```

Internally, proof methods may later call symbolic compute services:

```text
proof command
  -> proof state
  -> packed term/fact/rewrite index
  -> CPU/GPU candidate prefilter
  -> exact proof method step
  -> strict kernel replay/check
```

The visible methods remain `simp`, `auto`, `blast`, `metis`-like tools, and
future Sledgehammer-style suggestions. The acceleration is an implementation
detail, not a new trust model.

## First-Stage Workloads

### 1. Term and Fact Fingerprinting

Compute stable fingerprints for terms and facts:

```text
head symbol
symbol multiset / small fixed histogram
type fingerprint
arity fingerprint
subterm count
depth buckets
alpha-normalized structural hash where feasible
```

Use case: quickly reject facts or rules that cannot plausibly match a goal.

### 2. Fact Prefilter

Input:

```text
goal fingerprint
many PackedFact entries
limit
```

Output:

```text
top-k FactCandidate values
```

Possible score components:

```text
head-symbol compatibility
symbol overlap
type overlap
arity compatibility
subterm fingerprint overlap
constant-frequency score
```

This does not prove anything. The CPU proof-search path still performs exact
matching/resolution and the kernel still validates theorem construction.

### 3. Rewrite Candidate Filtering

Input:

```text
goal subterm fingerprints
simp rule lhs fingerprints
```

Output:

```text
RewriteCandidate { subterm_id, rule_id, score, reason_bits }
```

The exact matcher and simplifier decide whether the rewrite actually applies.

### 4. Finite-Domain Counterexample Search

For bounded domains, batch-evaluate candidate assignments to quickly find
counterexamples or reject impossible branches.

Output is diagnostic or search guidance. It is not a theorem.

### 5. Batch Proof-Obligation Quick Rejection

For many independent obligations, use cheap fingerprint/type/head-symbol tests
to reject impossible candidate facts before invoking expensive proof search.

## Packed Data Structures

The current kernel term representation is tree/enum-oriented and CPU-friendly.
GPU and SIMD backends need packed, array-oriented data.

Initial design:

The packed structs and `PackedTrustClass` are centralized in
[symbolic_compute_backend.rs](../../scripts/templates/symbolic_compute_backend.rs).

`PackedTrustClass` is advisory. It helps ranking and filtering, but cannot be
used for theorem acceptance. In particular, it has no `KernelTrustedClosed`
variant: final trust requires an owner-bound
`isabelle-kernel::TrustedTheorem`, not packed metadata.

`PackedTermArena` must not become a second source of theorem terms. It is
derived from existing terms for indexing and batching. Any conversion from
packed representation back into theorem-facing syntax must be treated like
ordinary raw input and certified again.

## Backend Trait

Design the trait before implementing GPU support:

The same design-only template centralizes the proposed
`SymbolicComputeBackend` trait. This avoids duplicated sketches; standalone
compilation does not establish compatibility with future production modules.

Implementation order:

```text
1. CpuSymbolicBackend
2. correctness tests against simple hand-built terms/facts
3. integration with non-trusted fact/rewrite indexes
4. benchmark harness
5. optional BurnSymbolicBackend behind a feature flag
```

The CPU backend is required even if the GPU backend becomes the performance
target. It provides deterministic behavior, test oracles, and portability.

## Acceptance Gates

### Phase 0: Design Only

Gate:

- no production compute or dependency changes in this design phase;
- no trusted constructor exposed to packed IR;
- existing strict-kernel checks stay independent of this proposal.

### Phase 1: Packed IR CPU Baseline

Gate:

- `PackedTermArena` has deterministic encoding tests;
- symbol/type IDs are stable for a fixed input order;
- round-trip or lookup tests prove packed IDs refer back to original terms;
- no theorem construction API is available from packed data;
- all tests run without GPU dependencies.

### Phase 2: CPU Fact/Rewrite Prefilter

Gate:

- `CpuSymbolicBackend` returns only `FactCandidate` / `RewriteCandidate`;
- exact CPU matching/rewrite/resolution still runs after prefiltering;
- tests compare prefilter output against naive scan behavior;
- benchmarks compare prefilter plus exact check against naive scan;
- any lossy filter is explicitly marked as heuristic and cannot be used where
  completeness is required.

### Phase 3: Optional Burn/CubeCL Backend

Gate:

- backend is behind an optional feature flag;
- CPU backend remains default and fallback;
- GPU/backend output is deterministic after host-side sorting/tie-breaking;
- output is equal to CPU baseline, a documented superset, or a documented
  heuristic subset depending on the mode;
- CPU strict replay/check remains mandatory;
- `isabelle-kernel` dependency graph is unchanged.

### General Backend Gates

Before adding an optional GPU backend:

- Packed IR round-trips to stable ids and fingerprints.
- CPU backend is deterministic and tested.
- Candidate filtering is monotonic for configured safe prefilters: a filter
  marked "must keep possible matches" must not drop exact CPU matches.
- Every exact proof-producing path still calls the CPU kernel.
- Benchmarks show enough batch size to amortize packing and device dispatch.

Before enabling any backend by default:

- Same candidate set or an explicitly documented superset/subset contract
  relative to CPU baseline.
- Deterministic ordering after tie-breaking.
- No new dependency in `isabelle-kernel`.
- No trusted theorem construction in compute modules.

## Determinism And Reproducibility

The first CPU backend must be deterministic. Future GPU/multi-backend code must
normalize its output before consumers observe it:

- integer scores preferred over floating-point scores;
- stable sort by `(score desc, candidate id asc, reason_bits asc)`;
- explicit tie-breaking for equal scores;
- no reliance on backend iteration order;
- no theorem acceptance decision based on candidate order.

If two backends disagree, exact CPU proof search plus strict kernel replay is
the authority. Backend disagreement is a performance or completeness issue, not
a trusted-theorem issue.

## Failure Semantics

Compute failure must fail closed:

| Failure | Required behavior |
|---|---|
| Backend unavailable | Fall back to CPU backend or naive scan. |
| Backend panic/error | Drop acceleration result and run exact CPU path. |
| Candidate list empty | Treat as search guidance only unless the mode is explicitly complete and tested. |
| Candidate IDs invalid | Reject candidate batch and report index/corruption diagnostic. |
| CPU/GPU mismatch | Prefer CPU baseline and log backend mismatch. |
| Nondeterministic ordering | Sort deterministically before use. |
| Timeout | Return partial candidates only in heuristic mode; exact proof search remains responsible for theorem state. |

No compute failure may be converted into a proof success, admitted theorem, or
trusted theorem.

## Threat Model

Assume a compute backend may be buggy, nondeterministic, lossy, malicious, or
running on unreliable hardware. The architecture must remain sound under these
faults.

Threats and mitigations:

| Threat | Mitigation |
|---|---|
| Backend fabricates a candidate fact/rule | Candidate ID must resolve to an existing fact/rule in the CPU index. |
| Backend fabricates a term | Generated terms are not accepted; theorem-facing terms require certification and proof. |
| Backend confuses two terms via hash collision | Hash/fingerprint is prefilter only; exact CPU term equality/matching decides. |
| Backend drops a useful fact | This may hurt completeness/performance only; it cannot prove a false theorem. |
| Backend returns wrong substitution | CPU strict matcher/certifier rechecks substitutions before use. |
| Backend returns candidates in nondeterministic order | Host-side stable sorting before proof search. |
| Backend-specific dependency leaks into kernel | Firewall/dependency checks must reject kernel dependency on compute/backend crates. |
| Packed IR corrupts ids | Candidate lookup validates IDs before exact proof search. |

## Risks

- Packing and GPU transfer overhead may dominate small proof states.
- Tree/DAG terms with binders are hard to encode efficiently.
- De Bruijn substitution and exact matching are branch-heavy.
- Floating-point scoring can create nondeterministic ranking; prefer integer
  scores and stable tie-breaking for first versions.
- Backend portability varies by driver and runtime.

The first implementation should therefore target coarse, batched, untrusted
prefiltering rather than fine-grained kernel steps.

## Relationship To AI / Neural Work

Neural premise selection, embeddings, tactic ranking, and proof repair can be
future consumers of the same packed term/fact representations. They are not the
first reason for this layer.

The main architectural idea is:

```text
high-performance symbolic compute first
neural ranking later as an optional application
kernel trust boundary unchanged
```
