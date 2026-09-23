# Research extensions

This directory contains mathematical work beyond the fixed `p = 3/2` paper and its Lean formalization. Material here should not be read as part of the machine-checked theorem package unless explicitly stated.

## Archived general-parameter manuscript

An earlier manuscript studied
[
F_p(z)=sum_{jge1}rac{z^{lfloor j^pfloor}}{sqrt{lfloor j^pfloor!}},
qquad rac43le p<2.
]

A pre-split version is preserved in repository history at commit
`d23fed4692bd04195555d9f176a2ca31e6405918`.

It contains arguments for a broader parameter range, including the noncritical two-term regime and a critical (p=4/3) compactness argument. These results are not part of the current (p=3/2) formalization.

## Macroscopic questions

One direction studies high derivatives through normalized logarithmic potentials and the geometry of the active Taylor support. For power supports (
u_j=lfloor j^pfloor), the goal is to understand limiting radial potentials and zero measures across (1<p<2).

Related questions include:

- support-profile descriptions of limiting zero measures;
- circular components produced by gaps in limiting support profiles;
- identric-mean formulas for crossing radii in factorially normalized models;
- weaker local or mesoscopic sparsity hypotheses;
- Le Roy-type factorial normalizations;
- realization and inverse problems for radial zero measures.

These topics are research directions rather than claims of the canonical formalized paper.

## Microscopic questions

The local zero geometry has a separate scale.

- The direct two-term regime is governed by adjacent-term dominance and local zero localization.
- At (p=4/3), the archived manuscript develops a bilateral-Gaussian compactness mechanism.
- For (1<p<4/3), a dual Poisson/Stokes description remains under investigation.

The subcritical microscopic regime is not presently a theorem of the project.

## Scope

The `research/` directory does not assert that the general (1<p<2) theory, support-profile results, Le Roy extensions, mesoscopic-sparsity statements, or microscopic phase diagram have been formally verified or externally refereed.

The fixed (p=3/2) theorem package is contained in `../paper/` and `../formalization/`.
