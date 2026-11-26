import MPC.Trace.CheckerLocation
/-!
# MPC.Trace.DropCheck

Drops cannot newly enable fixed-position attacks by other pieces. Clearance and
attacks transfer from the after-board to the before-board, even for occupied
destinations. This is a board-update fact, not a full drop-legality condition.
-/

namespace MPC

private theorem empty_before (bs : BoardState) (pt : PieceType) (dst q : Pos)
    (h : (applyMove bs (.dropMove pt dst)).board.grid q = none) :
    bs.board.grid q = none := by
  by_cases he : q = dst
  · subst q
    rw [applyMove_dropMove_grid_dst] at h
    contradiction
  · rwa [applyMove_dropMove_grid_other bs pt dst q he] at h

/-- Clearance transfers backwards: a drop fills or replaces its destination,
    and does not empty any square. The reverse implication need not hold. -/
theorem applyMove_dropMove_pathClear_before (bs : BoardState) (pt : PieceType) (dst pos target : Pos)
    (h : pathClear (applyMove bs (.dropMove pt dst)).board pos target) :
    pathClear bs.board pos target :=
  pathClear_mono_of_empty_preserved _ _ (empty_before bs pt dst) pos target h

/-- The piece information and attack/target positions are fixed on both boards.
    Actual attack-source presence and target king placement remain separate. -/
theorem applyMove_dropMove_attacksOriented_before (bs : BoardState) (pt : PieceType) (dst : Pos)
    (owner : Player) (pieceType : PieceType) (pos target : Pos)
    (h : attacksOriented (applyMove bs (.dropMove pt dst)).board owner pieceType pos target) :
    attacksOriented bs.board owner pieceType pos target :=
  attacksOriented_mono_of_empty_preserved _ _ (empty_before bs pt dst) owner pieceType pos target h

/-- Every after-board other-position checker already checked the same target
    before the drop. Its exact piece contents are preserved away from dst. -/
theorem applyMove_dropMove_otherChecker_before (bs : BoardState) (pt : PieceType) (dst target : Pos) (owner : Player)
    (h : hasOtherCheckerOriented (applyMove bs (.dropMove pt dst)).board (.dropMove pt dst) owner target) :
    hasOtherCheckerOriented bs.board (.dropMove pt dst) owner target := by
  obtain ⟨pos, hn, pc, hp, ho, ha⟩ := h
  refine ⟨pos, hn, pc, ?_, ho, applyMove_dropMove_attacksOriented_before bs pt dst pc.owner pc.pieceType pos target ha⟩
  rwa [applyMove_dropMove_grid_other bs pt dst pos hn] at hp

/-- An initially unchecked fixed target has no other-position checker after a drop. -/
theorem applyMove_dropMove_not_otherChecker_of_not_inCheck (bs : BoardState) (pt : PieceType) (dst target : Pos) (owner : Player)
    (hbefore : ¬ inCheckOriented bs.board owner target) :
    ¬ hasOtherCheckerOriented (applyMove bs (.dropMove pt dst)).board (.dropMove pt dst) owner target := by
  intro h
  exact hbefore (inCheckOriented_of_otherChecker _ _ _ _ (applyMove_dropMove_otherChecker_before bs pt dst target owner h))

/-- For an initially unchecked fixed target, after-check is precisely destination
    check. No destination-emptiness or hand-availability premise is needed. -/
theorem applyMove_dropMove_inCheck_iff_destinationChecker (bs : BoardState) (pt : PieceType) (dst target : Pos) (owner : Player)
    (hbefore : ¬ inCheckOriented bs.board owner target) :
    inCheckOriented (applyMove bs (.dropMove pt dst)).board owner target ↔
    hasDestinationCheckerOriented (applyMove bs (.dropMove pt dst)).board (.dropMove pt dst) owner target := by
  rw [inCheckOriented_iff_destination_or_other _ (.dropMove pt dst)]
  simp only [applyMove_dropMove_not_otherChecker_of_not_inCheck bs pt dst target owner hbefore, or_false]

/-- Lift the conditional equivalence to any trace index with explicit target
    equality. Actual king interpretation requires separate placement consistency. -/
theorem MoveTrace.dropMove_inCheck_iff_destinationChecker (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (kp : Fin (tr.len + 1) → Player → Pos) (i : Fin tr.len)
    (pt : PieceType) (dst : Pos) (owner : Player)
    (hm : tr.moves i = .dropMove pt dst)
    (hk : kp i.succ owner = kp i.castSucc owner)
    (hb : ¬ inCheckOriented (tr.before i).board owner (kp i.castSucc owner)) :
    inCheckOriented (tr.after i).board owner (kp i.succ owner) ↔
    hasDestinationCheckerOriented (tr.after i).board (tr.moves i) owner (kp i.succ owner) := by
  have hb' : ¬ inCheckOriented (tr.before i).board owner (kp i.succ owner) := by
    simpa only [hk] using hb
  rw [ht i, hm]
  exact applyMove_dropMove_inCheck_iff_destinationChecker (tr.before i) pt dst (kp i.succ owner) owner hb'

end MPC
