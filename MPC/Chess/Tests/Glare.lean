import MPC.Chess.GlaringMove

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- The move footprint includes special-move effects, for either side to move.
example (c : Color) (choice : Option Promotion) :
    (Move.boardMove (1, 1) (2, 2) choice).Touches c (1, 1) ∧
    (Move.boardMove (1, 1) (2, 2) choice).Touches c (2, 2) ∧
    ¬ (Move.boardMove (1, 1) (2, 2) choice).Touches c (1, 2) := by
  simp [Move.Touches]

example (c : Color) :
    (Move.enPassant (3, 4) (4, 5)).Touches c (3, 4) ∧
    (Move.enPassant (3, 4) (4, 5)).Touches c (4, 5) ∧
    (Move.enPassant (3, 4) (4, 5)).Touches c (4, 4) ∧
    ¬ (Move.enPassant (3, 4) (4, 5)).Touches c (3, 5) := by
  cases c <;> decide

example (c : Color) (side : CastleSide) :
    (Move.castle side).Touches c (kingHome c) ∧
    (Move.castle side).Touches c (castleKingDestination c side) ∧
    (Move.castle side).Touches c (rookHome c side) ∧
    (Move.castle side).Touches c (castleRookDestination c side) ∧
    ¬ (Move.castle side).Touches c (4, 4) := by
  cases c <;> cases side <;> decide

-- Update locality covers every constructor, including malformed raw moves.
example (b : Board) (c : Color) (m : Move) (q : Pos) (h : ¬ m.Touches c q) :
    (applyMove ⟨b, c, {}, none⟩ m).board q = b q :=
  applyBoard_eq_of_not_touches b c m q h

private def prefixBoard (c : Color) : Board := fun q =>
  if q = (7, 7) then some ⟨c, .king⟩
  else if q = (4, 0) then some ⟨c.opponent, .king⟩
  else if q = (0, 0) then some ⟨c, .queen⟩
  else if q = (2, 0) then some ⟨c.opponent, .queen⟩ else none

private def prefixKings (c : Color) : Color → Pos := fun o =>
  if o = c then (7, 7) else (4, 0)

private def prefixMove : ℕ → Move
  | 0 => .boardMove (0, 0) (0, 4) none
  | _ => .boardMove (2, 0) (2, 2) none

private def prefixState (c : Color) : ℕ → Position
  | 0 => ⟨prefixBoard c, c, {}, none⟩
  | n + 1 => applyMove (prefixState c n) (prefixMove n)

private def checkingPrefix (c : Color) : MoveTrace where
  len := 2
  states := fun k => prefixState c k.val
  moves := fun i => prefixMove i.val

-- A legal two-check prefix, including both first and last moves, is not periodic.
example (c : Color) :
    (checkingPrefix c).FollowsLegalMoves ∧
    (checkingPrefix c).KingsWellPlaced (fun _ => prefixKings c) ∧
    (checkingPrefix c).EveryMoveChecksOpponent (fun _ => prefixKings c) ∧
    ¬ (checkingPrefix c).BoardTurnPeriodic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨prefixKings c, ?_, rfl⟩
    have h : ∀ i : Fin 2, LegalMove (prefixState c i.val) (prefixMove i.val) (prefixKings c) := by
      cases c <;> decide
    exact h i
  · change ∀ i : Fin 3, KingsWellPlaced (prefixState c i.val).board (prefixKings c)
    cases c <;> decide
  · change ∀ i : Fin 2, inCheck (prefixState c (i.val + 1)).board
      (prefixState c i.val).turn.opponent (prefixKings c (prefixState c i.val).turn.opponent)
    cases c <;> decide
  · intro h
    have he := congrFun h.1 (0, 0)
    cases c <;> contradiction

-- Glare removes the blocker which moves later, retains the attacker and kings,
-- and can hold even though the real board has no attack on the same target.
example (c : Color) :
    (checkingPrefix c).GlaresAtEnemyKing (fun _ => prefixKings c) 0 (0, 0) ∧
    ¬ attacks (prefixBoard c) ⟨c, .queen⟩ (0, 0) (4, 0) ∧
    (checkingPrefix c).strippedBoard 0 (0, 0) (0, 0) = some ⟨c, .queen⟩ ∧
    (checkingPrefix c).strippedBoard 0 (0, 0) (2, 0) = none ∧
    (checkingPrefix c).ImmovableAt (7, 7) ∧
    (checkingPrefix c).strippedBoard 0 (0, 0) (7, 7) = some ⟨c, .king⟩ := by
  cases c <;> decide

-- Source glare implies destination glare in the first move, but the second
-- move creates a glare. No reverse implication is claimed for a mere prefix.
example (c : Color) :
    (checkingPrefix c).GlaresAtEnemyKing (fun _ => prefixKings c) 1 (0, 4) ∧
    ¬ (checkingPrefix c).GlaresAtEnemyKing (fun _ => prefixKings c) 1 (2, 0) ∧
    (checkingPrefix c).GlaresAtEnemyKing (fun _ => prefixKings c) 2 (2, 2) := by
  cases c <;> decide

-- On an empty trace the occupied blocker is immovable and remains in the glare
-- board. The initial occupancy clause excludes empty squares from immovability.
example (c : Color) :
    let tr := MoveTrace.empty (prefixState c 0)
    tr.ImmovableAt (2, 0) ∧ ¬ tr.ImmovableAt (3, 3) ∧
    tr.strippedBoard 0 (0, 0) (2, 0) = some ⟨c.opponent, .queen⟩ ∧
    ¬ tr.GlaresAtEnemyKing (fun _ => prefixKings c) 0 (0, 0) := by
  cases c <;> decide

-- Identical contents after overwrite do not make a touched square immovable.
-- This is a raw update, deliberately not a legal own-piece capture.
private def overwriteBoard (c : Color) : Board := fun q =>
  if q = (0, 0) ∨ q = (1, 0) then some ⟨c, .rook⟩ else none

example (c : Color) :
    let pos : Position := ⟨overwriteBoard c, c, {}, none⟩
    let mv := Move.boardMove (0, 0) (1, 0) none
    let tr := MoveTrace.single pos (applyMove pos mv) mv
    (tr.before (0 : Fin 1)).board (1, 0) = (tr.after (0 : Fin 1)).board (1, 0) ∧
    mv.Touches c (1, 0) ∧ ¬ tr.ImmovableAt (1, 0) := by
  cases c <;> decide

private def unblockingBoard (c : Color) (doubleCheck : Bool) : Board := fun q =>
  if q = (7, 7) then some ⟨c, .king⟩
  else if q = (7, 3) then some ⟨c.opponent, .king⟩
  else if q = (0, 3) then some ⟨c, .rook⟩
  else if q = (3, 3) then some ⟨c, if doubleCheck then .bishop else .knight⟩ else none

private def unblockDest (doubleCheck : Bool) : Pos := if doubleCheck then (5, 5) else (4, 5)

-- Both colors, a new unblocked checker, and the inclusive double-check case.
example (c : Color) (doubleCheck : Bool) :
    let b := unblockingBoard c doubleCheck
    let dst := unblockDest doubleCheck
    let a := b.relocate (3, 3) dst none
    LegalMove ⟨b, c, {}, none⟩ (.boardMove (3, 3) dst none)
      (fun o => if o = c then (7, 7) else (7, 3)) ∧
    ¬ inCheck b c.opponent (7, 3) ∧
    hasUnblockedChecker b a (3, 3) dst c.opponent (7, 3) ∧
    (hasDestinationChecker a dst c.opponent (7, 3) ↔ doubleCheck = true) := by
  cases c <;> cases doubleCheck <;> decide

-- The public board decomposition and tail-clearance lemmas apply to these
-- nonperiodic examples, without adding an impossible periodicity premise.
example (c : Color) (doubleCheck : Bool) :
    let b := unblockingBoard c doubleCheck
    let dst := unblockDest doubleCheck
    inCheck (b.relocate (3, 3) dst none) c.opponent (7, 3) ∧ pathClear b (3, 3) (7, 3) := by
  have hu : hasUnblockedChecker (unblockingBoard c doubleCheck)
      ((unblockingBoard c doubleCheck).relocate (3, 3) (unblockDest doubleCheck) none)
      (3, 3) (unblockDest doubleCheck) c.opponent (7, 3) := by
    cases c <;> cases doubleCheck <;> decide
  constructor
  · apply (inCheck_relocate_iff_destination_or_unblocked _ _ _
      ⟨c, if doubleCheck then .bishop else .knight⟩ _ _ ?_ ?_ ?_).mpr (Or.inr hu)
    · cases c <;> cases doubleCheck <;> decide
    · cases doubleCheck <;> decide
    · cases c <;> cases doubleCheck <;> decide
  · exact pathClear_source_of_unblockedChecker _ _ _ _ _ hu

-- The first prefix move gives only a destination check. Its source already
-- attacks on the stripped board, so Lemma 2.5's board helper excludes unblocking.
example (c : Color) :
    hasDestinationChecker (prefixState c 1).board (0, 4) c.opponent (4, 0) ∧
    ¬ hasUnblockedChecker (prefixBoard c) (prefixState c 1).board
      (0, 0) (0, 4) c.opponent (4, 0) := by
  constructor
  · cases c <;> decide
  · apply not_unblockedChecker_of_source_attacks _ ((checkingPrefix c).strippedBoard 0 (0, 0))
      (0, 0) (0, 4) (4, 0) c.opponent ⟨c, .queen⟩
    · cases c <;> decide
    · simp
    · cases c <;> decide
    · cases c <;> decide

private def continuingBoard (c : Color) : Board := fun q =>
  if q = (0, 3) then some ⟨c, .rook⟩
  else if q = (1, 0) then some ⟨c, .knight⟩ else none

-- A continuing non-destination check is not new unblocking. Omitting the
-- unchecked-before premise would make the decomposition false here.
example (c : Color) :
    let b := continuingBoard c
    let a := b.relocate (1, 0) (2, 2) none
    inCheck b c.opponent (7, 3) ∧ inCheck a c.opponent (7, 3) ∧
    ¬ hasDestinationChecker a (2, 2) c.opponent (7, 3) ∧
    ¬ hasUnblockedChecker b a (1, 0) (2, 2) c.opponent (7, 3) := by
  cases c <;> decide

private def rayStart (axis : Fin 4) : Pos :=
  match axis.val with | 0 => (0, 3) | 1 => (3, 0) | 2 => (0, 0) | _ => (0, 6)
private def rayEnd (axis : Fin 4) : Pos :=
  match axis.val with | 0 => (6, 3) | 1 => (3, 6) | 2 => (6, 6) | _ => (6, 0)

-- All eight orientations, including points next to the end and board edges.
example (axis : Fin 4) (reverse : Bool) (q : Pos)
    (hq : Between (3, 3) (if reverse then rayStart axis else rayEnd axis) q) :
    Between (if reverse then rayEnd axis else rayStart axis)
      (if reverse then rayStart axis else rayEnd axis) q ∧ q ≠ (3, 3) := by
  have h : ∀ axis : Fin 4, ∀ reverse : Bool,
      (if reverse then rayEnd axis else rayStart axis).aligned
        (if reverse then rayStart axis else rayEnd axis) ∧
      Between (if reverse then rayEnd axis else rayStart axis)
        (if reverse then rayStart axis else rayEnd axis) (3, 3) := by decide
  exact between_of_between_tail (h axis reverse).1 (h axis reverse).2 hq

end MPC.Chess.Tests
