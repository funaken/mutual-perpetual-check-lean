import MPC.Chess.CheckerReduction

/-! The paper's glare retains immovable pieces, rather than clearing the whole
board. Immovability is defined from the move history and proved to preserve
contents; identical replacement is still a touch. -/

namespace MPC.Chess

/-- Squares used by a move, including the captured EP pawn and both castle legs.
The color is the side to move before the update. -/
def Move.Touches (move : Move) (turn : Color) (q : Pos) : Prop :=
  match move with
  | .boardMove src dst _ => q = src ∨ q = dst
  | .enPassant src dst => q = src ∨ q = dst ∨ q = enPassantCaptured src dst
  | .castle side => q = kingHome turn ∨ q = castleKingDestination turn side ∨
      q = rookHome turn side ∨ q = castleRookDestination turn side

instance (move : Move) (turn : Color) (q : Pos) : Decidable (move.Touches turn q) := by
  cases move <;> unfold Move.Touches <;> infer_instance

theorem applyBoard_eq_of_not_touches (b : Board) (c : Color) (move : Move) (q : Pos)
    (h : ¬ move.Touches c q) : applyBoard b c move q = b q := by
  cases move <;> simp only [Move.Touches, not_or] at h
  · exact Board.relocate_other _ _ _ _ _ h.1 h.2
  · simp [applyBoard, Board.relocate, Board.erase, h.1, h.2.1, h.2.2]
  · simp [applyBoard, Board.relocate, h.1, h.2.1, h.2.2.1, h.2.2.2]

namespace MoveTrace

def ImmovableAt (tr : MoveTrace) (q : Pos) : Prop :=
  (tr.states 0).board q ≠ none ∧ ∀ i, ¬ (tr.moves i).Touches (tr.before i).turn q

instance (tr : MoveTrace) (q : Pos) : Decidable (tr.ImmovableAt q) :=
  inferInstanceAs (Decidable ((tr.states 0).board q ≠ none ∧
    ∀ i, ¬ (tr.moves i).Touches (tr.before i).turn q))

def strippedBoard (tr : MoveTrace) (k : Fin (tr.len + 1)) (pos : Pos) : Board :=
  fun q => if q = pos ∨ tr.ImmovableAt q then (tr.states k).board q else none

def GlaresAtEnemyKing (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (k : Fin (tr.len + 1)) (pos : Pos) : Prop :=
  ∃ p, (tr.states k).board pos = some p ∧
    attacks (tr.strippedBoard k pos) p pos (kp k p.owner.opponent)

instance (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (k : Fin (tr.len + 1)) (pos : Pos) : Decidable (tr.GlaresAtEnemyKing kp k pos) :=
  inferInstanceAs (Decidable (∃ p, (tr.states k).board pos = some p ∧
    attacks (tr.strippedBoard k pos) p pos (kp k p.owner.opponent)))

theorem immovable_board_eq (tr : MoveTrace) (hl : tr.FollowsLegalMoves) (q : Pos)
    (hq : tr.ImmovableAt q) (i j : Fin (tr.len + 1)) :
    (tr.states i).board q = (tr.states j).board q := by
  have hz (k : Fin (tr.len + 1)) : (tr.states k).board q = (tr.states 0).board q := by
    induction k using Fin.induction with
    | zero => rfl
    | succ k ih =>
      obtain ⟨_, _, he⟩ := hl k
      change (tr.after k).board q = _
      rw [he]
      exact (applyBoard_eq_of_not_touches _ _ _ q (hq.2 k)).trans ih
  exact (hz i).trans (hz j).symm

theorem glares_of_attacks (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (k : Fin (tr.len + 1)) (pos : Pos) (p : Piece)
    (hs : (tr.states k).board pos = some p)
    (ha : attacks (tr.states k).board p pos (kp k p.owner.opponent)) :
    tr.GlaresAtEnemyKing kp k pos := by
  refine ⟨p, hs, attacks_mono ?_ ha⟩
  intro q he
  simp [strippedBoard, he]

/-- The kings are immovable as a theorem about periodic checking traces, not
as an additional field of the trace or of the glare definition. -/
theorem immovableAt_kingPos_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (k : Fin (tr.len + 1)) (c : Color) :
    tr.ImmovableAt (kp k c) := by
  have he (j : Fin (tr.len + 1)) := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp k j
  constructor
  · rw [he 0, (hk 0).king_present c]; exact nofun
  · intro i
    obtain ⟨src, dst, p, hm, hs, _, hnk, _, _, hd, _⟩ :=
      tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
    rw [hm, Move.Touches, he i.castSucc]
    have hking := (hk i.castSucc).king_present c
    change (tr.before i).board _ = _ at hking
    rintro (h | h)
    · rw [h, hs] at hking
      exact hnk (congrArg Piece.kind (Option.some.inj hking))
    · rw [h, hd] at hking
      contradiction

end MoveTrace
end MPC.Chess
