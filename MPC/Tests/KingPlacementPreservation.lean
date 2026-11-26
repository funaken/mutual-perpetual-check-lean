import MPC.Trace.KingPlacementPreservation
import Lean
/-!
# MPC.Tests.KingPlacementPreservation

After-state placement is obtained from the new preservation theorems.
The local hypotheses deliberately permit updates beyond legal shogi moves.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "King preservation verification must not import GameSeq"

namespace MPC

private def kingPositions : Player → Pos
  | .sente => (0, 0)
  | .gote => (8, 8)

private def noKing (sq : Square) : Prop := ∀ owner, sq ≠ some ⟨owner, .king⟩

private theorem noKing_some (piece : Piece) (h : piece.pieceType ≠ .king) : noKing (some piece) := by
  intro owner heq
  exact h (congrArg Piece.pieceType (Option.some.inj heq))

private def fixture (turn : Player) (source destination : Square) : BoardState :=
  { board :=
      { grid := fun q => if q = (0, 0) then some ⟨.sente, .king⟩
          else if q = (8, 8) then some ⟨.gote, .king⟩
          else if q = (4, 4) then source else if q = (5, 4) then destination else none
        hand := fun _ => ∅ }
    turn := turn }

private theorem fixture_placed (turn : Player) (source destination : Square)
    (hs : noKing source) (hd : noKing destination) :
    KingsWellPlaced (fixture turn source destination).board kingPositions := by
  intro owner q
  have hsource := hs owner
  have hdest := hd owner
  cases owner <;> by_cases h0 : q = (0, 0) <;> by_cases h8 : q = (8, 8) <;>
    by_cases h4 : q = (4, 4) <;> by_cases h5 : q = (5, 4) <;>
    simp_all [fixture, kingPositions]

-- Either owner can move its king to an empty or non-king-occupied destination.
-- Promotion flags are arbitrary update inputs, not claims about legal promotion.
example (owner : Player) (promote : Bool) (destination : Square) (hd : noKing destination) :
    KingsWellPlaced
      (applyMove (fixture owner none destination)
        (.boardMove (kingPositions owner) (5, 4) promote)).board
      (kingPosAfterBoardMove kingPositions (kingPositions owner) (5, 4)) ∧
    kingPosAfterBoardMove kingPositions (kingPositions owner) (5, 4) owner = (5, 4) ∧
    kingPosAfterBoardMove kingPositions (kingPositions owner) (5, 4) owner.opponent =
      kingPositions owner.opponent := by
  refine ⟨(fixture_placed owner none destination (by intro p; simp) hd).applyMove_boardMove
    _ _ promote (by intro p; cases p <;> decide), ?_, ?_⟩
  · simp [kingPosAfterBoardMove]
  · cases owner <;> rfl

-- Non-king movement, capture, and promotion preserve the same king positions.
example (turn : Player) (piece : Piece) (hp : piece.pieceType ≠ .king)
    (destination : Square) (hd : noKing destination) (promote : Bool) :
    KingsWellPlaced
      (applyMove (fixture turn (some piece) destination) (.boardMove (4, 4) (5, 4) promote)).board
      kingPositions := by
  have h := (fixture_placed turn (some piece) destination (noKing_some piece hp) hd).applyMove_boardMove
    (4, 4) (5, 4) promote (by intro p; cases p <;> decide)
  have heq : kingPosAfterBoardMove kingPositions (4, 4) (5, 4) = kingPositions := by
    funext p; cases p <;> rfl
  rwa [heq] at h

-- Empty sources and equal non-king endpoints are allowed by the local theorem.
example (turn : Player) (destination : Square) (hd : noKing destination) :
    KingsWellPlaced
      (applyMove (fixture turn none destination) (.boardMove (4, 4) (5, 4) false)).board
      kingPositions := by
  have h := (fixture_placed turn none destination (by intro p; simp) hd).applyMove_boardMove
    (4, 4) (5, 4) false (by intro p; cases p <;> decide)
  have heq : kingPosAfterBoardMove kingPositions (4, 4) (5, 4) = kingPositions := by
    funext p; cases p <;> rfl
  rwa [heq] at h

example (turn : Player) (piece : Piece) (hp : piece.pieceType ≠ .king) (promote : Bool) :
    KingsWellPlaced
      (applyMove (fixture turn (some piece) none) (.boardMove (4, 4) (4, 4) promote)).board
      kingPositions := by
  have h := (fixture_placed turn (some piece) none (noKing_some piece hp)
    (by intro p; simp)).applyMove_boardMove (4, 4) (4, 4) promote (by intro p; cases p <;> decide)
  have heq : kingPosAfterBoardMove kingPositions (4, 4) (4, 4) = kingPositions := by
    funext p; cases p <;> rfl
  rwa [heq] at h

-- The destination may be empty or contain any non-king, and the hand is empty.
example (turn : Player) (destination : Square) (hd : noKing destination)
    (pt : PieceType) (hpt : pt ≠ .king) :
    KingsWellPlaced (applyMove (fixture turn none destination) (.dropMove pt (5, 4))).board
      kingPositions :=
  (fixture_placed turn none destination (by intro p; simp) hd).applyMove_dropMove
    pt (5, 4) hpt (by intro p; cases p <;> decide)

-- Removing a king in concrete updates leaves no possible consistent placement.
-- These are examples on the independent foundation, not claims about GameSeq.
example (turn : Player) :
    ¬ ∃ kp, KingsWellPlaced
      (applyMove (fixture turn (some ⟨turn, .rook⟩) none)
        (.boardMove (4, 4) (kingPositions turn.opponent) false)).board kp := by
  rintro ⟨kp, hk⟩
  have hp := hk.king_present turn.opponent
  by_cases hd : kp turn.opponent = kingPositions turn.opponent
  · rw [hd, applyMove_boardMove_grid_dst] at hp
    change some (Piece.mk turn .rook) = some ⟨turn.opponent, .king⟩ at hp
    have ht := congrArg Piece.pieceType (Option.some.inj hp)
    cases ht
  · by_cases hs : kp turn.opponent = (4, 4)
    · rw [hs, applyMove_boardMove_grid_src _ _ _ _ (by cases turn <;> decide)] at hp
      cases hp
    · rw [applyMove_boardMove_grid_other _ _ _ _ _ hs hd] at hp
      have hbefore := fixture_placed turn (some ⟨turn, .rook⟩) none
        (noKing_some _ (by change PieceType.rook ≠ .king; decide)) (by intro p; simp)
      exact hd ((hbefore turn.opponent _).mp hp)

example (turn : Player) :
    ¬ ∃ kp, KingsWellPlaced
      (applyMove (fixture turn none none) (.dropMove .pawn (kingPositions turn.opponent))).board kp := by
  rintro ⟨kp, hk⟩
  have hp := hk.king_present turn.opponent
  by_cases hd : kp turn.opponent = kingPositions turn.opponent
  · rw [hd, applyMove_dropMove_grid_dst] at hp
    have ht := congrArg Piece.pieceType (Option.some.inj hp)
    cases ht
  · rw [applyMove_dropMove_grid_other _ _ _ _ hd] at hp
    have hbefore := fixture_placed turn none none (by intro p; simp) (by intro p; simp)
    exact hd ((hbefore turn.opponent _).mp hp)

-- Dropping a king at a new empty square duplicates that owner's existing king.
example (turn : Player) :
    ¬ ∃ kp, KingsWellPlaced (applyMove (fixture turn none none) (.dropMove .king (5, 4))).board kp := by
  rintro ⟨kp, hk⟩
  have hne : kingPositions turn ≠ (5, 4) := by cases turn <;> decide
  have hold := applyMove_dropMove_grid_other (fixture turn none none) .king (5, 4)
    (kingPositions turn) hne
  have hbefore := (fixture_placed turn none none (by intro p; simp) (by intro p; simp)).king_present turn
  have hnew := applyMove_dropMove_grid_dst (fixture turn none none) .king (5, 4)
  exact hne (((hk turn _).mp (hold.trans hbefore)).trans ((hk turn _).mp hnew).symm)

end MPC
