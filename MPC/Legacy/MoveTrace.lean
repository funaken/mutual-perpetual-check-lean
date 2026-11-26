import MPC.Trace.MoveTrace
import MPC.Legacy.Move
/-! Historical trace condition for the legacy direction predicate. -/
namespace MPC.MoveTrace

/-- Direction/path condition using the source piece's type before promotion.
    Existence and ownership are supplied separately by BoardMoveSourcesOwned.
    No condition on dropMove, capture legality, or promotion legality is asserted. -/
def BoardMovesFollowCanMoveTo (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (src dst : Pos) (promote : Bool) (piece : Piece),
    tr.moves i = .boardMove src dst promote →
    (tr.before i).board.grid src = some piece →
      canMoveTo (tr.before i).board piece.owner piece.pieceType src dst

end MPC.MoveTrace
