/-
Counterexample to `UidmapAlgebra.bsearch_complete` (Algebra.lean:281) as currently stated.

All hypotheses of the lemma hold for this input:
  n = 2 ≤ 340; first(arr[0]) = 0 < 10 = first(arr[1]) (strictly sorted);
  counts 100 and 1 are ≥ 1 and nothing wraps; key.count = 1; id 50 ∈ arr[0] = [0, 100).
Yet `bsearch_extent` returns `none`: the pivot is arr[1] = [10, 11), 50 lies above it, the
search moves right and runs out. The statement is missing a disjointness hypothesis
(the lemma's own doc comment says it needs one). Real kernel maps are disjoint.

Run (from verify/lean):  lake env lean counterexamples/BsearchComplete.lean
Expected output:         "bsearch returned none (MISS)"
Found by Gemini 4 Argon during a proof attempt (2026-11-05); confirmed by this run.
-/
import Uidmap
open Aeneas Aeneas.Std uidmap
def u32 (n : Nat) : Std.U32 := ⟨BitVec.ofNat _ n⟩
def usz (n : Nat) : Std.Usize := ⟨BitVec.ofNat _ n⟩
def z : UidGidExtent := { first := u32 0, lower_first := u32 0, count := u32 0 }
-- arr[0] = [0,100), arr[1] = [10,11): firsts strictly sorted (0 < 10), count ≥ 1, no wrap.
-- They OVERLAP. id 50 lies in arr[0].
def arr : Result (Array UidGidExtent 340#usize) :=
  Array.update (Array.repeat 340#usize z) (usz 0) { first := u32 0, lower_first := u32 1000, count := u32 100 } >>= fun a =>
  Array.update a (usz 1) { first := u32 10, lower_first := u32 2000, count := u32 1 }
#eval match (arr >>= fun a => bsearch_extent { map_up := false, id := u32 50, count := u32 1 } a (usz 2)) with
  | .ok none => "bsearch returned none (MISS)" | .ok (some e) => s!"found first={e.first.val}" | _ => "fail/div"
