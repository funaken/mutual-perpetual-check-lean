import MPC.Trace.KingPlacement
/-!
# MPC.Trace.KingPlacementPreservation

One-step preservation of exact king placement under local sufficient conditions.
After-state consistency is derived. These conditions do not certify move legality
and impose no trace-wide or GameSeq assumptions.
-/

namespace MPC

/-- Update the position of a king at the source; leave other kings in place. -/
def kingPosAfterBoardMove (kingPos : Player → Pos) (src dst : Pos) : Player → Pos :=
  fun owner => if kingPos owner = src then dst else kingPos owner

/-- The existing promotion update neither creates kings nor changes their type.
    This is an update property, not a criterion for legal promotion. -/
theorem PieceType.promote_eq_king_iff (pt : PieceType) : pt.promote = .king ↔ pt = .king := by
  cases pt <;> simp [PieceType.promote]

private theorem boardMove_dst_king_iff (bs : BoardState) (src dst : Pos)
    (promote : Bool) (owner : Player) :
    (applyMove bs (.boardMove src dst promote)).board.grid dst = some ⟨owner, .king⟩ ↔
      bs.board.grid src = some ⟨owner, .king⟩ := by
  rw [applyMove_boardMove_grid_dst]
  cases hs : bs.board.grid src with
  | none => simp
  | some piece =>
    cases piece with
    | mk p pt => cases promote <;> simp [Piece.mk.injEq, PieceType.promote_eq_king_iff]

/-- Avoiding both king positions at the destination suffices for preservation.
    No source-presence/ownership, movement, or distinct-endpoint premise is needed. -/
theorem KingsWellPlaced.applyMove_boardMove {bs : BoardState} {kingPos : Player → Pos}
    (hk : KingsWellPlaced bs.board kingPos) (src dst : Pos) (promote : Bool)
    (hd : ∀ owner, dst ≠ kingPos owner) :
    KingsWellPlaced (applyMove bs (.boardMove src dst promote)).board
      (kingPosAfterBoardMove kingPos src dst) := by
  intro owner pos
  by_cases hdst : pos = dst
  · subst pos
    rw [boardMove_dst_king_iff, hk owner src]
    by_cases hsrc : kingPos owner = src
    · simp [kingPosAfterBoardMove, hsrc]
    · simp [kingPosAfterBoardMove, hsrc, Ne.symm hsrc, hd owner]
  · by_cases hsrc : pos = src
    · subst pos
      rw [applyMove_boardMove_grid_src bs src dst promote hdst]
      by_cases hs : kingPos owner = src
      · simp [kingPosAfterBoardMove, hs, hdst]
      · simp [kingPosAfterBoardMove, hs, Ne.symm hs]
    · rw [applyMove_boardMove_grid_other bs src dst promote pos hsrc hdst, hk owner pos]
      by_cases hs : kingPos owner = src
      · simp [kingPosAfterBoardMove, hs, hsrc, hdst]
      · simp [kingPosAfterBoardMove, hs]

/-- Dropping a non-king outside both king positions preserves placement.
    The destination need not be empty; availability in hand is not asserted. -/
theorem KingsWellPlaced.applyMove_dropMove {bs : BoardState} {kingPos : Player → Pos}
    (hk : KingsWellPlaced bs.board kingPos) (pt : PieceType) (dst : Pos)
    (hpt : pt ≠ .king) (hd : ∀ owner, dst ≠ kingPos owner) :
    KingsWellPlaced (applyMove bs (.dropMove pt dst)).board kingPos := by
  intro owner pos
  by_cases hdst : pos = dst
  · subst pos
    rw [applyMove_dropMove_grid_dst]
    simp [Piece.mk.injEq, hpt, hd owner]
  · rw [applyMove_dropMove_grid_other bs pt dst pos hdst]
    exact hk owner pos

end MPC
