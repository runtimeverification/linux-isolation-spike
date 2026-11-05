/-
Counterexample to `UidmapWritePath.remap_install_fun` (WritePath.lean:731) as currently stated.

parent  = one extent [0, 1) -> [0, 1)          (WellFormed; checked by hand)
new_map = one extent [5, 6), lower_first 5     (PreRemap, Nodup, nr_extents = 1)
ret     = 1                                    (the statement puts no constraint on ret)
Remapping lower_first 5 through the parent fails, so the loop returns `ret` unchanged:
r.1 = 1, which is neither < 0 nor = 0, contradicting the postcondition.
The statement is missing `(hret : ret < 0#i32)`, which its only caller, `lines_loop_fun`,
already has in scope (it would pass `hret` at WritePath.lean:847).

Run (from verify/lean):  lake env lean counterexamples/RemapInstallFun.lean
Expected output:         "r.1 = 1 ..."
Found by Gemini 4 Argon during a proof attempt (2026-11-05); confirmed by this run.
-/
import Uidmap
open Aeneas Aeneas.Std uidmap
def u32 (n : Nat) : Std.U32 := ⟨BitVec.ofNat _ n⟩
def usz (n : Nat) : Std.Usize := ⟨BitVec.ofNat _ n⟩
/-- A base-arm map holding the given extents (≤ 5). -/
def mk (es : List (Nat × Nat × Nat)) : Result UidGidMap :=
  UidGidMap.zeroed >>= fun m =>
  es.zipIdx.foldlM (fun acc (p, i) => Array.update acc (usz i)
      { first := u32 p.1, lower_first := u32 p.2.1, count := u32 p.2.2 }) m.extent >>= fun a =>
  .ok { m with extent := a, nr_extents := u32 es.length }
-- parent: [0,1) -> [0,1)   (WellFormed: 1 extent, count 1, no wrap)
-- new_map: [5,6) with lower_first 5   (PreRemap: count 1, no wrap, trivially disjoint; Nodup; nr_extents = 1)
-- ret = 1   (the statement puts no constraint on ret)
#eval match (mk [(0,0,1)] >>= fun parent => mk [(5,5,1)] >>= fun nm => UidGidMap.zeroed >>= fun z =>
    map_write_body_loop0_loop0 z.extent z.forward z.reverse false false (u32 0) parent
      nm.extent nm.forward nm.reverse nm.forward_live nm.reverse_live nm.nr_extents 1#i32 0#u32) with
  | .ok r => s!"r.1 = {r.1.val}  (postcondition needs r.1 < 0, or r.1 = 0 ∧ WellFormed)"
  | .fail e => s!"fail {repr e}" | .div => "div"
