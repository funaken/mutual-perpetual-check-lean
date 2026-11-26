import MPC.Basic.Lemmas
import MPC.Trace.CheckOrigin
/-!
# MPC.Trace.CheckOriginTrace

Derive the per-index check-origin premises. All-state king placement and owned
board-move sources fix the non-mover's king position across each move. Initial
non-mover safety and post-move self-safety make every pre-move non-mover safe.
No GameSeq, complete legality, or global immovability premise is used.
-/

namespace MPC.MoveTrace

/-- The player not to move in the initial state is safe at its supplied position.
    This is an external condition; it is not implied by transitions or placement. -/
def InitialOpponentKingSafe (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) : Prop :=
  ¬ inCheckOriented (tr.states 0).board (tr.states 0).turn.opponent
    (kp 0 (tr.states 0).turn.opponent)

/-- A move never relocates the non-mover's king: the destination receives a
    mover-owned piece and a vacated source is empty. No king-capture or drop-type
    condition is needed beyond consistent placement in both states. -/
theorem opponentKingPos_succ_eq (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (i : Fin tr.len) :
    kp i.succ (tr.before i).turn.opponent = kp i.castSucc (tr.before i).turn.opponent := by
  apply (hk i.castSucc (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)).mp
  have ha : (tr.after i).board.grid (kp i.succ (tr.before i).turn.opponent) =
      some { owner := (tr.before i).turn.opponent, pieceType := .king } :=
    (hk i.succ).king_present _
  change (tr.before i).board.grid _ = _
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · obtain ⟨piece, hp, ho⟩ := hs i src dst promote hm
    by_cases hd : kp i.succ (tr.before i).turn.opponent = dst
    · rw [hd, tr.boardMove_grid_dst ht i src dst promote hm, hp] at ha
      have he := congrArg (Option.map Piece.owner) ha
      simp only [Option.map_some] at he
      exact absurd (ho.symm.trans (Option.some.inj he)).symm (Player.opponent_ne_self _)
    · by_cases hsrc : kp i.succ (tr.before i).turn.opponent = src
      · have hne : src ≠ dst := fun he => hd (hsrc.trans he)
        rw [hsrc, tr.boardMove_grid_src ht i src dst promote hm hne] at ha
        cases ha
      · rwa [tr.boardMove_grid_other ht i src dst promote _ hm hsrc hd] at ha
  · by_cases hd : kp i.succ (tr.before i).turn.opponent = dst
    · rw [hd, tr.dropMove_grid_dst ht i pt dst hm] at ha
      exact absurd (congrArg Piece.owner (Option.some.inj ha)).symm (Player.opponent_ne_self _)
    · rwa [tr.dropMove_grid_other ht i pt dst _ hm hd] at ha

/-- Every state's non-mover is safe exactly when the initial non-mover is safe
    and every move leaves its mover's king safe. -/
theorem everyStateOpponentSafe_iff (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) :
    (∀ k : Fin (tr.len + 1), ¬ inCheckOriented (tr.states k).board (tr.states k).turn.opponent
      (kp k (tr.states k).turn.opponent)) ↔
    tr.InitialOpponentKingSafe kp ∧ tr.EveryMoveLeavesOwnKingSafe kp := by
  have hstep (j : Fin tr.len) : (tr.states j.succ).turn.opponent = (tr.before j).turn := by
    change (tr.after j).turn.opponent = _
    rw [tr.turn_after_move ht j, Player.opponent_opponent]
  constructor
  · intro h
    refine ⟨h 0, fun j => ?_⟩
    have hj := h j.succ
    rw [hstep j] at hj
    exact hj
  · rintro ⟨h0, hsafe⟩ k
    induction k using Fin.cases with
    | zero => exact h0
    | succ j =>
      rw [hstep j]
      exact hsafe j

/-- The before-non-check premise at every index. -/
theorem before_opponent_not_inCheck (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hsafe : tr.EveryMoveLeavesOwnKingSafe kp)
    (h0 : tr.InitialOpponentKingSafe kp) (i : Fin tr.len) :
    ¬ inCheckOriented (tr.before i).board (tr.before i).turn.opponent
      (kp i.castSucc (tr.before i).turn.opponent) :=
  (tr.everyStateOpponentSafe_iff kp ht).mpr ⟨h0, hsafe⟩ i.castSucc

/-- The check-origin classification without per-index premises: with consistent
    placement, owned sources, self-safety, and initial non-mover safety, every move
    checks the opponent iff each check comes from the destination or an unblocked
    checker. The two kinds of check may coexist. -/
theorem everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp) :
    tr.EveryMoveChecksOpponent kp ↔ ∀ i : Fin tr.len,
      hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) ∨
      hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
  tr.everyMoveChecksOpponent_iff_destination_or_unblocked kp ht hs
    (tr.opponentKingPos_succ_eq kp ht hs hk) (tr.before_opponent_not_inCheck kp ht hsafe h0)

/-- Generated king positions: initial placement and the destination and non-king-drop conditions
    supply placement; initial safety is stated at the supplied initial positions. -/
theorem everyMoveChecksOpponent_kingPositionsFrom_iff_destination_or_unblocked (tr : MoveTrace)
    (initial : Player → Pos) (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned)
    (ha : tr.MoveDestinationsAvoidKings) (hd : tr.DropMovesAreNonKings)
    (hp : MPC.KingsWellPlaced (tr.states 0).board initial)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe (tr.kingPositionsFrom initial))
    (h0 : ¬ inCheckOriented (tr.states 0).board (tr.states 0).turn.opponent
      (initial (tr.states 0).turn.opponent)) :
    tr.EveryMoveChecksOpponent (tr.kingPositionsFrom initial) ↔ ∀ i : Fin tr.len,
      hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (tr.kingPositionsFrom initial i.succ (tr.before i).turn.opponent) ∨
      hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (tr.kingPositionsFrom initial i.succ (tr.before i).turn.opponent) := by
  have h0' : tr.InitialOpponentKingSafe (tr.kingPositionsFrom initial) := by
    unfold InitialOpponentKingSafe
    rw [kingPositionsFrom_zero]
    exact h0
  exact tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe _ ht hs
    (tr.kingsWellPlaced_kingPositionsFrom initial ht ha hd hp) hsafe h0'

end MPC.MoveTrace
