import Lake
open Lake DSL

package «lean-showcase» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
  @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib LeanShowcase where
  roots := #[`LeanShowcase]