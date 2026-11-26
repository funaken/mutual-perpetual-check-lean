import MPC.Invariants.PieceFamilyStep
import MPC.Glare.NonGlaringKind
/-!
# MPC.Invariants.DropDestinations

Drops land on empty squares in any periodic trace whose drops come from the hand.

`DropDestinationsEmpty` (drops land on empty squares) is a premise of the main
theorem through `MutualPerpetualCheck`;  showed it is needed, with a
trace that re-drops a rook from an empty hand onto the other side's rook. With
's `DropsFromHand` it follows from periodicity:

- Count every piece on the board and in both hands: 's family total for the
  family of all piece types (`PieceType.IsAny`), which promotion keeps trivially.
- A board move keeps the total (`boardMove_familyTotal`). A drop from the hand
  satisfies "total after + the indicator of the drop square = total before"
  (`dropMove_familyTotal_add`): it moves a piece from the hand to the board, and a
  piece on the drop square is overwritten and lost.
- The trace returns to its first state, so the total never changes
  (`count_eq_initial_of_step_le`). So the drop square was empty
  (`dropDestinationsEmpty_of_dropsFromHand`).

The premises are the transitions, owned sources, distinct endpoints (a board move
onto its own square would put the moved piece into the hand), drops from the hand
and periodicity. No other premise of `MutualPerpetualCheck` is used.

-/

namespace MPC

/-- The family of all piece types. -/
def PieceType.IsAny (_ : PieceType) : Prop := True

instance : DecidablePred PieceType.IsAny := fun _ => isTrue trivial

/-- Promotion keeps every type in the family of all types. -/
theorem promoteStable_any : PromoteStable PieceType.IsAny := fun _ => Iff.rfl

/-- The indicator of the family of all types is `1` exactly on occupied squares. -/
theorem familyInd_any_eq_zero_iff (sq : Square) :
    familyInd PieceType.IsAny sq = 0 ↔ sq = none := by
  cases sq with
  | none => simp [familyInd]
  | some p => simp [familyInd, PieceType.IsAny]

namespace MoveTrace

/-- A drop from the hand: the family total after it, plus the indicator of the drop
    square before it, is the total before it. The piece moves from the hand to the
    board, and a piece on the drop square is overwritten and lost. -/
theorem dropMove_familyTotal_add (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hdrop : tr.DropsFromHand) (F : PieceType → Prop) [DecidablePred F] (i : Fin tr.len)
    (pt : PieceType) (dst : Pos) (hmv : tr.moves i = .dropMove pt dst) :
    (tr.after i).board.familyTotal F + familyInd F ((tr.before i).board.grid dst) =
      (tr.before i).board.familyTotal F := by
  have hdst := tr.dropMove_grid_dst ht i pt dst hmv
  have hsum := sum_add_one_eq (fun q => familyInd F ((tr.after i).board.grid q))
    (fun q => familyInd F ((tr.before i).board.grid q)) dst
    (fun q hq => by
      rw [tr.dropMove_grid_other ht i pt dst q hmv hq])
  simp only [hdst] at hsum
  have hhand : (tr.after i).board.handFamilyCount F + (if F pt then 1 else 0) =
      (tr.before i).board.handFamilyCount F := by
    rw [ht i, hmv]
    exact applyMove_dropMove_handFamilyCount _ pt dst F (hdrop i pt dst hmv)
  unfold Board.familyTotal
  unfold Board.familyCount
  simp only [familyInd] at hsum
  simp only [familyInd] at hhand ⊢
  split at hsum <;> omega

/-- In a periodic trace whose drops come from the hand, drops land on empty squares. -/
theorem dropDestinationsEmpty_of_dropsFromHand (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hd : tr.BoardMoveEndpointsDistinct)
    (hdrop : tr.DropsFromHand) (hp : tr.IsPeriodic) : tr.DropDestinationsEmpty := by
  intro i pt dst hmv
  let f : Fin (tr.len + 1) → ℕ := fun k => (tr.states k).board.familyTotal PieceType.IsAny
  have hstep : ∀ j : Fin tr.len, f j.succ ≤ f j.castSucc :=
    fun j => tr.familyTotal_succ_le ht hs hd hdrop _ promoteStable_any j
  have hlast : f (Fin.last tr.len) = f 0 := by
    show (tr.states (Fin.last tr.len)).board.familyTotal _ = (tr.states 0).board.familyTotal _
    rw [hp]
  have e1 := count_eq_initial_of_step_le tr.len f hstep hlast i.succ
  have e2 := count_eq_initial_of_step_le tr.len f hstep hlast i.castSucc
  have hadd := tr.dropMove_familyTotal_add ht hdrop PieceType.IsAny i pt dst hmv
  have hzero : familyInd PieceType.IsAny ((tr.before i).board.grid dst) = 0 := by
    have : f i.succ = f i.castSucc := e1.trans e2.symm
    change (tr.after i).board.familyTotal _ = (tr.before i).board.familyTotal _ at this
    omega
  exact (familyInd_any_eq_zero_iff _).mp hzero

end MoveTrace
end MPC
