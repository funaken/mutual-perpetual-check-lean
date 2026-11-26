import MPC.Trace.CheckerLocation
import Lean
/-!
# MPC.Tests.CheckerLocation

The location split is inclusive, applies to both move kinds, and uses actual
piece ownership/type. It does not assert that a move newly causes a check.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Checker location verification must not import GameSeq"

namespace MPC

private def pairBoard (owner : Player) (left right : Bool) : Board :=
  { grid := fun q => if q = (3, 4) ∧ left = true then some ⟨owner, .gold⟩
      else if q = (5, 4) ∧ right = true then some ⟨owner, .gold⟩ else none
    hand := fun _ => ∅ }

private theorem pair_destination (owner : Player) (left right : Bool) (move : Move)
    (hm : move.destination = (3, 4)) :
    hasDestinationCheckerOriented (pairBoard owner left right) move owner.opponent (4, 4) ↔
      left = true := by
  constructor
  · rintro ⟨piece, hp, _⟩
    rw [hm] at hp
    by_cases hl : left = true
    · exact hl
    · simp [pairBoard, hl] at hp
  · intro hl
    refine ⟨⟨owner, .gold⟩, ?_, ?_, ?_⟩
    · rw [hm]; simp [pairBoard, hl]
    · cases owner <;> rfl
    · rw [hm]; cases owner <;> left <;> decide

private theorem pair_other (owner : Player) (left right : Bool) (move : Move)
    (hm : move.destination = (3, 4)) :
    hasOtherCheckerOriented (pairBoard owner left right) move owner.opponent (4, 4) ↔
      right = true := by
  constructor
  · rintro ⟨pos, hne, piece, hp, _⟩
    rw [hm] at hne
    by_cases hr : right = true
    · exact hr
    · simp [pairBoard, hne, hr] at hp
  · intro hr
    refine ⟨(5, 4), ?_, ⟨owner, .gold⟩, ?_, ?_, ?_⟩
    · rw [hm]; decide
    · simp [pairBoard, hr]
    · cases owner <;> rfl
    · cases owner <;> left <;> decide

-- All four truth combinations, for either owner, either move kind, and either
-- board-move promotion flag. The supplied target square is empty in this board.
example (owner : Player) (left right drop promote : Bool) :
    let move := if drop then Move.dropMove .gold (3, 4) else .boardMove (3, 3) (3, 4) promote
    (hasDestinationCheckerOriented (pairBoard owner left right) move owner.opponent (4, 4) ↔
      left = true) ∧
    (hasOtherCheckerOriented (pairBoard owner left right) move owner.opponent (4, 4) ↔
      right = true) ∧ (pairBoard owner left right).grid (4, 4) = none := by
  have hm : (if drop then Move.dropMove .gold (3, 4)
    else .boardMove (3, 3) (3, 4) promote).destination = (3, 4) := by cases drop <;> rfl
  exact ⟨pair_destination owner left right _ hm, pair_other owner left right _ hm, rfl⟩

-- Presence alone is insufficient: a same-owner piece cannot check that owner's
-- target, even though the gold's geometric attack is available.
example (owner : Player) :
    attacksOriented (pairBoard owner true false) owner .gold (3, 4) (4, 4) ∧
    ¬ hasDestinationCheckerOriented (pairBoard owner true false)
      (.dropMove .gold (3, 4)) owner (4, 4) := by
  constructor
  · cases owner <;> left <;> decide
  · cases owner <;> simp [hasDestinationCheckerOriented, Move.destination, pairBoard,
      Player.opponent]

private def pawnState (owner : Player) : BoardState :=
  { board := { grid := fun q => if q = (3, 3) then some ⟨owner, .pawn⟩ else none
               hand := fun _ => ∅ }
    turn := owner }

-- After promotion the pawn has a gold-like horizontal attack; without promotion
-- it does not. The classification reads the after-board type, not the old pawn.
example (owner : Player) (promote : Bool) :
    hasDestinationCheckerOriented
      (applyMove (pawnState owner) (.boardMove (3, 3) (3, 4) promote)).board
      (.boardMove (3, 3) (3, 4) promote) owner.opponent (4, 4) ↔ promote = true := by
  cases owner <;> cases promote <;>
    simp [hasDestinationCheckerOriented, Move.destination, applyMove, pawnState,
      Board.setGrid, PieceType.promote, Player.opponent,
      attacksOriented, canMoveToOriented, PieceType.stepDirs, PieceType.slideDirs,
      Dir.forPlayer, Dir.flip, Pos.dirTo]

private def initialPositions (turn : Player) (owner : Player) : Pos :=
  if owner = turn then (0, 0) else (4, 4)

private def initialState (turn : Player) : BoardState :=
  { board :=
      { grid := fun q => if q = (0, 0) then some ⟨turn, .king⟩
          else if q = (4, 4) then some ⟨turn.opponent, .king⟩
          else if q = (5, 4) then some ⟨turn, .gold⟩ else none
        hand := fun _ => ∅ }
    turn := turn }

private theorem initial_placed (turn : Player) :
    KingsWellPlaced (initialState turn).board (initialPositions turn) := by
  intro owner q
  cases turn <;> cases owner <;> by_cases h0 : q = (0, 0) <;>
    by_cases h4 : q = (4, 4) <;> by_cases h5 : q = (5, 4) <;>
    simp_all [initialState, initialPositions, Player.opponent]

private def dropTrace (turn : Player) : MoveTrace :=
  MoveTrace.single (initialState turn) (.dropMove .gold (3, 4))

private theorem drop_placed (turn : Player) :
    (dropTrace turn).KingsWellPlaced ((dropTrace turn).kingPositionsFrom (initialPositions turn)) := by
  apply MoveTrace.kingsWellPlaced_kingPositionsFrom
  · exact MoveTrace.single_followsTransitions _ _
  · intro i owner
    change Fin 1 at i
    have hi := Fin.eq_zero i
    subst i
    cases turn <;> cases owner <;> decide
  · intro i pt dst hm
    simp [dropTrace, MoveTrace.single] at hm
    obtain ⟨rfl, rfl⟩ := hm
    decide
  · exact initial_placed turn

-- An existing other-position check survives a drop, alongside the new
-- destination checker. This trace has actual kings and generated positions;
-- empty hands deliberately make no claim about complete drop legality.
example (turn : Player) :
    let tr := dropTrace turn
    let kp := tr.kingPositionsFrom (initialPositions turn)
    tr.FollowsTransitions ∧ tr.KingsWellPlaced kp ∧
    hasOtherCheckerOriented (tr.before (0 : Fin 1)).board (tr.moves (0 : Fin 1)) turn.opponent (4, 4) ∧
    hasDestinationCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1)) turn.opponent (4, 4) ∧
    hasOtherCheckerOriented (tr.after (0 : Fin 1)).board (tr.moves (0 : Fin 1)) turn.opponent (4, 4) ∧
    tr.EveryMoveChecksOpponent kp := by
  have hd : hasDestinationCheckerOriented (applyMove (initialState turn) (.dropMove .gold (3, 4))).board
      (.dropMove .gold (3, 4)) turn.opponent (4, 4) := by
    refine ⟨⟨turn, .gold⟩, rfl, ?_, ?_⟩
    · cases turn <;> rfl
    · cases turn <;> left <;> decide
  refine ⟨MoveTrace.single_followsTransitions _ _, drop_placed turn, ?_, hd, ?_, ?_⟩
  · refine ⟨(5, 4), by change ((5, 4) : Pos) ≠ (3, 4); decide, ⟨turn, .gold⟩, rfl, ?_, ?_⟩
    · cases turn <;> rfl
    · cases turn <;> left <;> decide
  · refine ⟨(5, 4), by change ((5, 4) : Pos) ≠ (3, 4); decide, ⟨turn, .gold⟩, rfl, ?_, ?_⟩
    · cases turn <;> rfl
    · cases turn <;> left <;> decide
  · apply ((dropTrace turn).everyMoveChecksOpponent_iff_destination_or_other _).mpr
    intro i
    change Fin 1 at i
    have hi := Fin.eq_zero i
    subst i
    cases turn <;> exact Or.inl hd

-- At length zero both the trace condition and its split are vacuous.
example (bs : BoardState) (kp : Fin 1 → Player → Pos) :
    let tr : MoveTrace := { len := 0, states := fun _ => bs, moves := Fin.elim0 }
    tr.EveryMoveChecksOpponent kp ∧ ∀ i : Fin tr.len,
      hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) ∨
      hasOtherCheckerOriented (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

end MPC
