import MPC.Trace.MoveTraceCheck
/-!
# MPC.Trace.CheckerLocation

Partition current check witnesses by their position relative to a move's
destination. The two existence propositions may both hold. An other-position
checker need not be newly enabled by the move, including for drops.
-/

namespace MPC

/-- The destination of either kind of move. -/
def Move.destination : Move → Pos
  | .boardMove _ dst _ => dst
  | .dropMove _ dst => dst

/-- A present opposing piece at the destination attacks the supplied target.
    Its type comes from the current board; target king presence is separate. -/
def hasDestinationCheckerOriented (board : Board) (move : Move)
    (kingOwner : Player) (kingPos : Pos) : Prop :=
  ∃ piece : Piece, board.grid move.destination = some piece ∧
    piece.owner = kingOwner.opponent ∧
    attacksOriented board piece.owner piece.pieceType move.destination kingPos

/-- A present opposing checker away from the destination. This also covers
    pre-existing checks and does not assert discovered-check causation. -/
def hasOtherCheckerOriented (board : Board) (move : Move)
    (kingOwner : Player) (kingPos : Pos) : Prop :=
  ∃ pos : Pos, pos ≠ move.destination ∧ ∃ piece : Piece,
    board.grid pos = some piece ∧ piece.owner = kingOwner.opponent ∧
    attacksOriented board piece.owner piece.pieceType pos kingPos

theorem inCheckOriented_of_destinationChecker (board : Board) (move : Move)
    (kingOwner : Player) (kingPos : Pos)
    (h : hasDestinationCheckerOriented board move kingOwner kingPos) :
    inCheckOriented board kingOwner kingPos := by
  obtain ⟨piece, hp, ho, ha⟩ := h
  exact ⟨move.destination, piece, hp, ho, ha⟩

theorem inCheckOriented_of_otherChecker (board : Board) (move : Move)
    (kingOwner : Player) (kingPos : Pos)
    (h : hasOtherCheckerOriented board move kingOwner kingPos) :
    inCheckOriented board kingOwner kingPos := by
  obtain ⟨pos, _, piece, hp, ho, ha⟩ := h
  exact ⟨pos, piece, hp, ho, ha⟩

/-- Inclusive disjunction: different checkers may occur in both locations.
    No transition, legality, or before-state non-check premise is needed. -/
theorem inCheckOriented_iff_destination_or_other (board : Board) (move : Move)
    (kingOwner : Player) (kingPos : Pos) :
    inCheckOriented board kingOwner kingPos ↔
      hasDestinationCheckerOriented board move kingOwner kingPos ∨
      hasOtherCheckerOriented board move kingOwner kingPos := by
  constructor
  · rintro ⟨pos, piece, hp, ho, ha⟩
    by_cases heq : pos = move.destination
    · subst pos; exact Or.inl ⟨piece, hp, ho, ha⟩
    · exact Or.inr ⟨pos, heq, piece, hp, ho, ha⟩
  · rintro (h | h)
    · exact inCheckOriented_of_destinationChecker board move kingOwner kingPos h
    · exact inCheckOriented_of_otherChecker board move kingOwner kingPos h

theorem hasOtherCheckerOriented_of_inCheck_of_not_destination (board : Board) (move : Move)
    (kingOwner : Player) (kingPos : Pos)
    (hc : inCheckOriented board kingOwner kingPos)
    (hd : ¬ hasDestinationCheckerOriented board move kingOwner kingPos) :
    hasOtherCheckerOriented board move kingOwner kingPos :=
  ((inCheckOriented_iff_destination_or_other board move kingOwner kingPos).mp hc).resolve_left hd

/-- Lift the positional split to `EveryMoveChecksOpponent`, retaining its before-state
    mover and after-state board/positions. Placement is required separately when
    interpreting the supplied targets as actual kings. -/
theorem MoveTrace.everyMoveChecksOpponent_iff_destination_or_other (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos) :
    tr.EveryMoveChecksOpponent kingPos ↔ ∀ i : Fin tr.len,
      hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kingPos i.succ (tr.before i).turn.opponent) ∨
      hasOtherCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kingPos i.succ (tr.before i).turn.opponent) := by
  exact forall_congr' fun i => inCheckOriented_iff_destination_or_other _ _ _ _

end MPC
