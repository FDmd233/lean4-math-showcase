# Reproducibility notes

This file records the commands and consistency checks relevant to the fixed (p=3/2) manuscript.

## Paper

The manuscript source is `paper_en.tex`, and the compiled version is `paper_en.pdf`.

The proof uses:

- the explicit sparse series (F(z)=sum z^{lfloor j^{3/2}floor}/sqrt{lfloor j^{3/2}floor!});
- the exact tail estimate with its polynomial left-tail factor;
- compatible constants in the local existence and uniqueness arguments;
- the left-transition/right-transition/one-term-dominance annular trichotomy;
- distinct-zero counting on finite unions of pairwise disjoint model disks;
- a separate treatment of the possible zero at the origin.

## Lean

From the Lean project directory:

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

The project is pinned by its `lean-toolchain` and Lake manifest. `RequestProject/Main.lean` imports the declaration chain used by the paper and prints the corresponding axiom dependencies.

## Cross-reference files

- `formalization/formalization_map.md` gives the paper-to-Lean declaration map.
- `formalization/FORMALIZATION_STATUS.md` states the machine-verification boundary.
- `paper/PRIORITY_AND_SCOPE.md` records the historical and priority scope.

Research material in `research/` is separate from the fixed theorem package.
