# Release checklist for the Erdős 906 website submission

This checklist applies only to the canonical `p = 3/2` submission in `paper/` and `formalization/`. The research directory is not part of the release.

## 1. Mathematical scope

Before publishing, verify that the canonical paper claims only:

- the explicit series `F(z) = sum z^(floor(j^(3/2))) / sqrt(floor(j^(3/2))!)`;
- cofinite zero hitting;
- `O(n^(-1/6))` annular covering;
- one simple zero per model disk;
- exhaustion of annular zeros;
- eventual annular simplicity;
- pairwise disjoint model disks;
- exact finite distinct-zero counts;
- the analytic facts and origin multiplicity listed in the formalization crosswalk.

No general-`p`, endpoint, limiting-measure, exact-order/type, or support-profile statement belongs in the website submission.

## 2. Paper audit

The release build must satisfy all of the following:

- `paper_en.tex` compiles successfully;
- no undefined citation or reference appears in the final LaTeX log;
- no LaTeX error or overfull horizontal box appears;
- the compiled PDF opens and is visually inspected page by page;
- equation (3.2) retains the polynomial left-tail factor from `tail_sum_bound`;
- the local existence and uniqueness constants are compatible;
- the exclusion proof uses the left-transition/right-transition/one-term-dominance trichotomy;
- distinct-zero counting is not silently replaced by multiplicity counting;
- no global simplicity statement is made at the origin.

The details are recorded in `REFEREE_AUDIT.md` and `PAGE_BY_PAGE_GUIDE.md`.

## 3. Formalization audit

On the exact release commit:

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

The GitHub Actions workflow `Check Erdos 906 formalization` must be green. `Main.lean` must include the declarations in `formalization_map.md`, including `origin_multiplicity`.

The static integrity scan must also be green.

## 4. Citation and priority audit

The public release makes no first-solution claim. Keep the distinction among:

- Erdős's increasing-sequence dense-union formulation;
- Barth-Schneider's discrete interpolation theorem with chosen derivative orders;
- Gethner's infinitely-many-derivatives final-set notion;
- Hou's probabilistic cofinite construction.

The checked source roles are recorded in `PRIORITY_AND_SCOPE.md`.

## 5. GitHub release state

Do not post the `main` URL until the audited branch has been merged into `main`.

After merge:

1. verify that both the paper and Lean workflows are green on the release state;
2. open `paper/paper_en.pdf` from `main` and confirm that it is the final six-page manuscript;
3. open the paper-to-Lean map and confirm that all links resolve;
4. use the `main` repository URL in the website comment.

## 6. Recommended website post

> I have posted a manuscript giving a solution to Erdős Problem 906 using the explicit sparse Fock series
> \[
> F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}.
> \]
> For every nonempty open set `U` in the complex plane, I prove that there is `N(U)` such that `F^(n)` has a zero in `U` for every `n >= N(U)`. On fixed annuli the proof also gives `O(n^(-1/6))` covering, one simple zero per pairwise disjoint model disk, exhaustion of the annular zeros, and exact finite distinct-zero counts. The `p = 3/2` theorem package and its proof chain are accompanied by a Lean 4/Mathlib formalization.
>
> Manuscript and formalization:
> https://github.com/FDmd233/lean4-math-showcase/tree/main/projects/erdos-906-sparse-fock
>
> I make no first-solution priority claim. Comments, corrections, and references to overlapping work are welcome.

This wording states the theorem precisely without making a historical claim that the paper does not establish.
