# Priority and scope

Literature audit date: 2026-09-12.

I do **not** claim that this is the first solution of Erdős Problem #906, and I do not take failure to find the same formula in a search as evidence of originality.

I keep three questions separate:

1. **Are the stated theorems correct?** The manuscript gives self-contained arguments for its mathematical claims.
2. **Who first solved #906?** I make no first-solution claim. Earlier probabilistic constructions exist, including Eric Hou's 2026 work.
3. **Is the explicit sparse-Fock construction, or its local zero geometry, new?** I regard this as still open on the literature side, mainly because some older lacunary-entire-function sources have not yet been checked in full.

## Sources checked

The literature audit directly checked or located:

- P. Erdős (1982), *Some of my favourite problems which recently have been solved*, p. 72, IV.1(i).
- K. F. Barth and W. J. Schneider (1972), on the related interpolation problem.
- Eric Hou, *Cofinite zeros of high derivatives*, arXiv:2607.20816v5, including the accompanying public Lean repository.
- R. M. Gethner (1985), *On the zeros of the derivatives of some entire functions of finite order*.
- A. C. Offord (1993), *Lacunary entire functions*; only the publisher material was available during this audit, not a full line-by-line comparison of the paper.
- G. R. MacLane (1952), *Sequences of derivatives and normal families*.
- Earlier 2026 proposed solutions cited by Hou, including Almeida and Chojecki.

## Remaining priority risk

Here `nu_j = floor(j^p)` satisfies `nu_(j+1)/nu_j -> 1`, so the support is not a classical Hadamard-gap sequence, although `nu_j/j -> infinity` gives a Fabry-type sparsity. Those labels alone do not tell me whether an older theorem already contains part of the present localization picture.

The main literature risks are still Offord's full hypotheses, older derivative-zero results for sparse/lacunary series, and later pits-effect work. Until those are checked properly, the public claim stays deliberately narrow:

> The paper gives an explicit deterministic sparse-Fock construction for the cofinite formulation of Erdős Problem #906 and derives quantitative local zero geometry from it, without a first-solution or historical-priority claim.

## Comparison with Hou

Both constructions give cofinite zero-hitting with order-two finite-type growth. Hou's construction is probabilistic and comes with a public formalization. The present construction specifies its sparse coefficients directly and obtains a detailed annular localization picture. I do not use the numerical type constant as a superiority claim, since rescaling changes it.
