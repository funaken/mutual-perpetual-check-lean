import MPC.Basic.Defs
/-!
# MPC.Basic.Demote

The original piece of a promoted piece.

In shogi a captured promoted piece goes into the capturer's hand as its original
piece: a tokin as a pawn, a dragon as a rook, a horse as a bishop, and so on.

- `PieceType.demote`: the original piece of a promoted type; other types are unchanged.
- `demote_demote`: demoting twice is demoting once.

`demote` imports only the piece types, so that the transition `applyMove` can use it. Its relation to promotion and to the piece families of  is in
`MPC.Basic.DemoteFamily`.

-/

namespace MPC

/-- The original piece of a promoted piece; other pieces are unchanged. -/
def PieceType.demote : PieceType → PieceType
  | .dragon         => .rook
  | .horse          => .bishop
  | .promotedSilver => .silver
  | .promotedKnight => .knight
  | .promotedLance  => .lance
  | .tokin          => .pawn
  | other           => other

/-- Demoting twice is demoting once. -/
theorem PieceType.demote_demote (pt : PieceType) : pt.demote.demote = pt.demote := by
  cases pt <;> rfl

end MPC
