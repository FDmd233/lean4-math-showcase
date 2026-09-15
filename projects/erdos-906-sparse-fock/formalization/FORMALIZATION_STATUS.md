# Formalization status

Latest audited snapshot: Aristotle Round 4, September 13, 2026.

## Current verified/audited theorem layer

The supplied Lean project contains unconditional theorem statements for:

- `erdos906_sparse_fock_p32`
- `annular_covering_rate_p32`
- `model_disk_zero_count_one_p32`
- `annular_zero_exclusion_p32`
- `annular_zeros_simple_p32`
- `annular_zeros_simple_deriv_p32`
- `model_disks_pairwise_disjoint_p32`
- `zero_count_model_disk_union_p32`

The Round 4 audit reports 6727 lines of Lean under `RequestProject/`.

## Integrity scan

A static scan of the supplied project found no occurrences of:

- `sorry`
- `admit`
- custom `axiom` declarations
- `unsafe`
- `native_decide`
- `@[implemented_by]`

The supplied Aristotle report states that a clean `lake build` succeeded (8061 jobs) and that principal theorems depend only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

Important qualification: the current ChatGPT audit runtime did not contain `lake`, so that clean-build claim was not independently reproduced there.

## What the current p = 3/2 formalization establishes

Subject to an independent successful clean build of the supplied archive, the formalized layer goes beyond mere existence/covering. It captures the structural classification that, for sufficiently high derivatives in a fixed annulus:

- every zero lies in the model-disk family;
- every admissible model disk contains a unique zero;
- that zero is simple;
- the relevant disks are pairwise disjoint;
- finite unions contain exactly the expected number of **distinct** zeros.

The theorem `zero_count_model_disk_union_p32` uses `Set.ncard`, so it counts distinct zeros rather than a multiplicity-valued divisor object. This is consistent with multiplicity one because the corresponding simplicity theorems are also present, but multiplicity is not separately encoded as a dedicated divisor/order theorem.

## Manuscript claims not yet covered by this formalization

The latest audit records the following as still outside the Lean development:

- the sector zero-count asymptotic for `p=3/2`;
- the limiting zero measure;
- the full structural theorem for general `4/3 < p < 2`;
- the critical `p=4/3` compactness argument;
- the lower bound proving exact order 2 and exact type 1/2.

## Source archive status

The authoritative latest Lean source is the Aristotle Round 4 archive

`a74c257c-73f0-41c3-ba42-cb04d1fbc24b-aristotle (3).tar.gz`.

At the time this GitHub publication directory was created, the archive existed in the user's ChatGPT Library, but the connector exposed it as a Project file without an authorized raw-byte export path. For that reason, the source archive has **not** been reconstructed from summaries or replaced by placeholder Lean code here.

When the archive is uploaded manually or becomes exportable, it should be added verbatim under a dedicated subdirectory such as `formalization/lean/`, followed by an independent `lake build` and axiom audit.

## Documentation warning

An older file named `ARISTOTLE_SUMMARY.md` in the supplied archive described an earlier incomplete stage and should not be presented as the current status without a superseded label. The Round 4 report and this document are the relevant status summaries.
