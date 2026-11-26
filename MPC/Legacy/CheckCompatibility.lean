import MPC.Basic.OrientedCheck
import MPC.Legacy.Check
import MPC.Legacy.MoveCompatibility
/-! Legacy check compatibility under symmetric piece types. -/
namespace MPC

/-- Compatibility is restricted to pieces with owner-symmetric direction tables. -/
theorem attacksOriented_iff_attacks_of_symmetric (board : Board) (owner : Player)
    (pt : PieceType) (src dst : Pos)
    (h : pt = .king ∨ pt = .rook ∨ pt = .bishop ∨ pt = .dragon ∨ pt = .horse) :
    attacksOriented board owner pt src dst ↔ attacks board owner pt src dst :=
  canMoveToOriented_iff_canMoveTo_of_symmetric board owner pt src dst h

/-- Check compatibility when every present opposing piece has symmetric directions.
    No restriction is imposed on pieces belonging to the target's owner. -/
theorem inCheckOriented_iff_inCheck_of_symmetric (board : Board)
    (player : Player) (kingPos : Pos)
    (h_types : ∀ (pos : Pos) (piece : Piece), board.grid pos = some piece →
      piece.owner = player.opponent →
      piece.pieceType = .king ∨ piece.pieceType = .rook ∨ piece.pieceType = .bishop ∨
      piece.pieceType = .dragon ∨ piece.pieceType = .horse) :
    inCheckOriented board player kingPos ↔ inCheck board player kingPos := by
  constructor
  · rintro ⟨pos, piece, hp, ho, ha⟩
    exact ⟨pos, piece, hp, ho,
      (attacksOriented_iff_attacks_of_symmetric board _ _ _ _ (h_types pos piece hp ho)).mp ha⟩
  · rintro ⟨pos, piece, hp, ho, ha⟩
    exact ⟨pos, piece, hp, ho,
      (attacksOriented_iff_attacks_of_symmetric board _ _ _ _ (h_types pos piece hp ho)).mpr ha⟩

end MPC
