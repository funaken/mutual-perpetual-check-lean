import MPC.Pieces.BishopFrontEdge
import Lean
/-!
# MPC.Tests.BishopFrontEdge

Concrete checks for , for the first player (`τ = 1`).

- The front-edge candidates for the king, for `σ = 1`: `(2, 2)` for `t = 2`, and
  `(2, 1)` and `(1, 2)` for `t = 1` (`KingCandidate` with `ρ = τ`).
- Why the three-rook count applies only to the front edges. Behind a file square in
  front of the enemy king, the glaring piece slides back toward its own side,
  along `(0, -1)`, so it is a rook or a dragon. Behind a file square at the enemy
  king's back, it slides forward, along `(0, 1)`, and may be a lance, which is not
  a rook or a dragon. So the back edges (the paper's Table 1) remain.

The periodic theorems are not exercised: no periodic mutual-check trace is
constructed.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Bishop front-edge verification must not import GameSeq"

namespace MPC
namespace BishopFrontEdgeTests

example : KingCandidate 1 1 1 2 (2, 2) ∧ KingCandidate 1 1 1 1 (2, 1) ∧
    KingCandidate 1 1 1 1 (1, 2) := by
  unfold KingCandidate
  decide

-- Sliding backwards along a file: a rook or a dragon.
example (pt : PieceType) (h : ((0, -1) : Dir) ∈ pt.slideDirs.map (Dir.forPlayer · .sente)) :
    pt = .rook ∨ pt = .dragon :=
  rookDragon_of_slideDir pt .sente (0, -1) h (Or.inl rfl) (by decide)

-- Sliding forward along a file: a lance can, and it is not a rook or a dragon.
example : ((0, 1) : Dir) ∈ PieceType.lance.slideDirs.map (Dir.forPlayer · .sente) ∧
    ¬ (PieceType.lance = .rook ∨ PieceType.lance = .dragon) := by decide

end BishopFrontEdgeTests
end MPC
