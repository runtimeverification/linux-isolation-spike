import Lake
open Lake DSL

-- The Aeneas Lean standard library, at the pinned commit this spike uses:
-- AeneasVerif/aeneas c2015b86, charon-pin 909ff09a (LLBC v0.1.220),
-- Lean/mathlib v4.31.0.
--
-- Pointed at the LOCAL checkout rather than fetched from git, for two reasons:
-- ~/aeneas-project/aeneas is the checkout whose binary produced the extraction
-- (~/aeneas is a NEWER checkout whose binary rejects v0.1.220 LLBC — see
-- ROADMAP.md §6), and its backends/lean/.lake is already built with the
-- matching mathlib, so `lake build` needs no network.
--
-- For a clean clone elsewhere, replace with:
--   require aeneas from git
--     "https://github.com/AeneasVerif/aeneas.git"
--       @ "c2015b8668ba6d5b41f5f19d00a881c12bbb0b5d" / "backends/lean"
-- and run `lake exe cache get` before `lake build`.
require aeneas from "/home/natalie/aeneas-project/aeneas/backends/lean"

package «uidmap_verif» where

-- The Aeneas-generated model. Verbatim copy of
-- Uidmap-charon-909ff09a-v0.1.220.lean, which is kept under its pinned name as
-- the provenance record (the hyphens are not a legal Lean module name).
@[default_target] lean_lib «Uidmap» where
