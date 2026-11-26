import MPC.Trace.SourceUnblocking
import MPC.Trace.DropCheck
/-!
# MPC.Trace.CheckOrigin

Combine board-move source unblocking with drop unblocking exclusion.
For a previously unchecked fixed target, every after-check has a destination
checker or, for board moves only, a retained checker whose path was cleared by
the source. No GameSeq, legality, or global immovability premise is used.
-/

namespace MPC

/-- Board moves have a present source piece; drops impose no condition.
    Ownership, movement rules, and hand availability are separate. -/
def Move.SourcePresent (board : Board) : Move → Prop
  | .boardMove src _ _ => ∃ piece : Piece, board.grid src = some piece
  | .dropMove _ _ => True

/-- A retained opposing checker away from both board-move endpoints whose path
    contains the source, avoids the destination, and changes from blocked to
    clear. Drops never have one. A destination checker may also exist. -/
def hasUnblockedCheckerOriented (before after : Board) (move : Move)
    (kingOwner : Player) (target : Pos) : Prop :=
  match move with
  | .boardMove src dst _ =>
      ∃ pos piece, pos ≠ src ∧ pos ≠ dst ∧ before.grid pos = some piece ∧
        after.grid pos = some piece ∧ piece.owner = kingOwner.opponent ∧
        attacksOriented after piece.owner piece.pieceType pos target ∧
        src.toInt ∈ slidePath pos target ∧ dst.toInt ∉ slidePath pos target ∧
        ¬ pathClear before pos target ∧ pathClear after pos target
  | .dropMove _ _ => False

/-- An unblocked checker is an after-board other-position checker. -/
theorem hasOtherCheckerOriented_of_unblockedChecker (before after : Board) (move : Move)
    (kingOwner : Player) (target : Pos)
    (h : hasUnblockedCheckerOriented before after move kingOwner target) :
    hasOtherCheckerOriented after move kingOwner target := by
  cases move with
  | boardMove src dst promote =>
    obtain ⟨pos, piece, _, hd, _, hp, ho, ha, _⟩ := h
    exact ⟨pos, hd, piece, hp, ho, ha⟩
  | dropMove pt dst => exact h.elim

/-- From an unchecked fixed target, other-position checkers after any move are
    exactly unblocked checkers: board moves use source presence, and drops have
    none. Before-destination emptiness and full legality are not assumed. -/
theorem applyMove_otherChecker_iff_unblockedChecker (bs : BoardState) (move : Move)
    (kingOwner : Player) (target : Pos)
    (hs : move.SourcePresent bs.board)
    (hbefore : ¬ inCheckOriented bs.board kingOwner target) :
    hasOtherCheckerOriented (applyMove bs move).board move kingOwner target ↔
      hasUnblockedCheckerOriented bs.board (applyMove bs move).board move kingOwner target := by
  refine ⟨fun h => ?_, hasOtherCheckerOriented_of_unblockedChecker _ _ move kingOwner target⟩
  cases move with
  | boardMove src dst promote =>
    obtain ⟨moving, hsrc⟩ := hs
    exact applyMove_boardMove_otherChecker_source_unblocking bs src dst target promote
      moving kingOwner hsrc hbefore h
  | dropMove pt dst =>
    exact applyMove_dropMove_not_otherChecker_of_not_inCheck bs pt dst target kingOwner hbefore h

/-- Combined classification for either move kind. Both disjuncts may hold
    together (double check); neither is claimed to exclude the other. -/
theorem applyMove_inCheck_iff_destination_or_unblocked (bs : BoardState) (move : Move)
    (kingOwner : Player) (target : Pos)
    (hs : move.SourcePresent bs.board)
    (hbefore : ¬ inCheckOriented bs.board kingOwner target) :
    inCheckOriented (applyMove bs move).board kingOwner target ↔
      hasDestinationCheckerOriented (applyMove bs move).board move kingOwner target ∨
      hasUnblockedCheckerOriented bs.board (applyMove bs move).board move kingOwner target := by
  rw [inCheckOriented_iff_destination_or_other _ move,
    applyMove_otherChecker_iff_unblockedChecker bs move kingOwner target hs hbefore]

/-- Apply the combined classification at any trace index. Target equality is
    explicit; actual king interpretation needs separate placement consistency. -/
theorem MoveTrace.inCheck_iff_destination_or_unblocked (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (kp : Fin (tr.len + 1) → Player → Pos) (i : Fin tr.len) (owner : Player)
    (hs : (tr.moves i).SourcePresent (tr.before i).board)
    (hk : kp i.succ owner = kp i.castSucc owner)
    (hb : ¬ inCheckOriented (tr.before i).board owner (kp i.castSucc owner)) :
    inCheckOriented (tr.after i).board owner (kp i.succ owner) ↔
      hasDestinationCheckerOriented (tr.after i).board (tr.moves i) owner (kp i.succ owner) ∨
      hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
        owner (kp i.succ owner) := by
  have hb' : ¬ inCheckOriented (tr.before i).board owner (kp i.succ owner) := by
    simpa only [hk] using hb
  rw [ht i]
  exact applyMove_inCheck_iff_destination_or_unblocked (tr.before i) (tr.moves i) owner
    (kp i.succ owner) hs hb'

/-- Owned board-move sources are present; drops satisfy the condition trivially. -/
theorem MoveTrace.sourcePresent_of_boardMoveSourcesOwned (tr : MoveTrace)
    (h : tr.BoardMoveSourcesOwned) (i : Fin tr.len) :
    (tr.moves i).SourcePresent (tr.before i).board := by
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · obtain ⟨piece, hp, _⟩ := h i src dst promote hm
    exact ⟨piece, hp⟩
  · exact trivial

/-- Lift the classification to `EveryMoveChecksOpponent`. Before-non-check
    and target equality are explicit per-index premises, not derived here from
    self-safety, initial safety, or generated positions. -/
theorem MoveTrace.everyMoveChecksOpponent_iff_destination_or_unblocked (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned)
    (hk : ∀ i : Fin tr.len, kp i.succ (tr.before i).turn.opponent =
      kp i.castSucc (tr.before i).turn.opponent)
    (hb : ∀ i : Fin tr.len, ¬ inCheckOriented (tr.before i).board (tr.before i).turn.opponent
      (kp i.castSucc (tr.before i).turn.opponent)) :
    tr.EveryMoveChecksOpponent kp ↔ ∀ i : Fin tr.len,
      hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) ∨
      hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
  forall_congr' fun i => tr.inCheck_iff_destination_or_unblocked ht kp i _
    (tr.sourcePresent_of_boardMoveSourcesOwned hs i) (hk i) (hb i)

end MPC
