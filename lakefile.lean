import Lake
open Lake DSL

package «lean4-math-showcase» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
  @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib Lean4MathShowcase where
  roots := #[`Lean4MathShowcase]