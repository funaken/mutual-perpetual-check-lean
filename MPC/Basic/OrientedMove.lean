import MPC.Basic.Move
/-!
# MPC.Basic.OrientedMove

Direction/path conditions with owner-relative directions: sente moves forward
in positive y, gote in negative y. The legacy canMoveTo is left unchanged.
Neither predicate expresses complete move legality; pathClear is reused as is.
-/

namespace MPC

/-- Compare the board displacement with directions transformed once for the
    piece owner. Source presence, destination ownership, and promotion/drop
    legality are separate conditions. -/
def canMoveToOriented (board : Board) (owner : Player) (pt : PieceType)
    (src dst : Pos) : Prop :=
  let d := Pos.dirTo src dst
  (d ∈ pt.stepDirs.map (Dir.forPlayer · owner)) ∨
  (∃ sd ∈ pt.slideDirs.map (Dir.forPlayer · owner),
    d.normalize = sd ∧
    ∃ k : ℕ, 1 ≤ k ∧ d.1 = ↑k * sd.1 ∧ d.2 = ↑k * sd.2 ∧
    pathClear board src dst)

theorem canMoveToOriented_pawn_iff (board : Board) (owner : Player) (src dst : Pos) :
    canMoveToOriented board owner .pawn src dst ↔
      Pos.dirTo src dst = Dir.forPlayer (0, 1) owner := by
  simp [canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs]

theorem canMoveToOriented_not_self (board : Board) (owner : Player)
    (pt : PieceType) (src : Pos) : ¬ canMoveToOriented board owner pt src src := by
  intro h
  rcases h with hs | ⟨sd, hsd, hn, _⟩
  · cases owner <;> cases pt <;>
      simp [PieceType.stepDirs, Dir.forPlayer, Dir.flip, Pos.dirTo, Prod.ext_iff] at hs
  · have hz : sd = (0, 0) := by simpa [Pos.dirTo, Dir.normalize] using hn.symm
    rw [hz] at hsd
    cases owner <;> cases pt <;>
      simp [PieceType.slideDirs, Dir.forPlayer, Dir.flip, Prod.ext_iff] at hsd

end MPC
