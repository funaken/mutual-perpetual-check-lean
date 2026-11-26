import MPC.Invariants.PieceFamilyStep
import Lean
/-!
# MPC.Tests.CaptureDemote

Concrete checks for : a captured piece enters the capturer's hand as its
original piece.

- In general: a board move onto a square holding `cp` adds `cp.pieceType.demote` to
  the mover's hand and leaves the other hand unchanged (`applyMove_boardMove_hand`).
- Capturing a tokin puts a pawn in the hand, a dragon a rook, a horse a bishop, and a
  promoted silver, knight or lance a silver, knight or lance.
- Capturing a piece that is not promoted puts that piece in the hand: a silver, a gold,
  a rook.
- The captured piece is in the hand as the original piece only: after capturing a
  tokin, the hand holds no tokin, and a pawn can be dropped from it (`DropsFromHand`).
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Capture demote verification must not import GameSeq"

namespace MPC
namespace CaptureDemoteTests

/-! ## The general statement -/

example (bs : BoardState) (src dst : Pos) (promote : Bool) (cp : Piece)
    (h : bs.board.grid dst = some cp) :
    (applyMove bs (.boardMove src dst promote)).board.hand bs.turn =
      bs.board.hand bs.turn + {cp.pieceType.demote} := by
  rw [applyMove_boardMove_hand, h]
  simp

example (bs : BoardState) (src dst : Pos) (promote : Bool) (cp : Piece)
    (h : bs.board.grid dst = some cp) :
    (applyMove bs (.boardMove src dst promote)).board.hand bs.turn.opponent =
      bs.board.hand bs.turn.opponent := by
  rw [applyMove_boardMove_hand, h]
  cases bs.turn <;> rfl

/-! ## Concrete captures -/

/-- A first-player silver on `(4, 4)` and a second-player piece of type `pt` on
    `(4, 5)`, the first player to move, both hands empty. -/
private def facing (pt : PieceType) : BoardState :=
  { board := { grid := fun q =>
                 if q = (4, 4) then some ⟨.sente, .silver⟩
                 else if q = (4, 5) then some ⟨.gote, pt⟩ else none,
               hand := fun _ => ∅ },
    turn := .sente }

/-- The silver captures the piece on `(4, 5)`. -/
private def capture (pt : PieceType) : BoardState :=
  applyMove (facing pt) (.boardMove (4, 4) (4, 5) false)

-- Promoted pieces go back to their original pieces.
example : (capture .tokin).board.hand .sente = {.pawn} := by decide
example : (capture .dragon).board.hand .sente = {.rook} := by decide
example : (capture .horse).board.hand .sente = {.bishop} := by decide
example : (capture .promotedSilver).board.hand .sente = {.silver} := by decide
example : (capture .promotedKnight).board.hand .sente = {.knight} := by decide
example : (capture .promotedLance).board.hand .sente = {.lance} := by decide

-- Pieces that are not promoted enter the hand as they are.
example : (capture .silver).board.hand .sente = {.silver} := by decide
example : (capture .gold).board.hand .sente = {.gold} := by decide
example : (capture .rook).board.hand .sente = {.rook} := by decide

-- The other hand is unchanged, and the silver now stands on `(4, 5)`.
example : (capture .tokin).board.hand .gote = ∅ := by decide
example : (capture .tokin).board.grid (4, 5) = some ⟨.sente, .silver⟩ := by decide

-- After capturing a tokin, the hand holds a pawn and no tokin.
example : PieceType.tokin ∉ (capture .tokin).board.hand .sente := by decide
example : PieceType.pawn ∈ (capture .tokin).board.hand .sente := by decide

/-! ## Dropping the pawn from the hand -/

/-- Capture the tokin, let the second player move a piece out of the way, then drop
    the pawn onto `(0, 0)`. Here the second player has a gold on `(8, 8)` that steps to
    `(8, 7)`. -/
private def withGold : BoardState :=
  { board := { grid := fun q =>
                 if q = (4, 4) then some ⟨.sente, .silver⟩
                 else if q = (4, 5) then some ⟨.gote, .tokin⟩
                 else if q = (8, 8) then some ⟨.gote, .gold⟩ else none,
               hand := fun _ => ∅ },
    turn := .sente }

private def afterCapture : BoardState := applyMove withGold (.boardMove (4, 4) (4, 5) false)
private def afterGold : BoardState := applyMove afterCapture (.boardMove (8, 8) (8, 7) false)
private def afterDrop : BoardState := applyMove afterGold (.dropMove .pawn (0, 0))

private def threeMoves : MoveTrace where
  len := 3
  states := fun j =>
    if j.val = 0 then withGold else if j.val = 1 then afterCapture
    else if j.val = 2 then afterGold else afterDrop
  moves := fun j =>
    if j.val = 0 then .boardMove (4, 4) (4, 5) false
    else if j.val = 1 then .boardMove (8, 8) (8, 7) false else .dropMove .pawn (0, 0)

example : threeMoves.FollowsTransitions := by
  intro ⟨i, hi⟩
  change i < 3 at hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

-- The pawn dropped on the third move came from the hand.
example : threeMoves.DropsFromHand := by
  intro ⟨i, hi⟩ pt dst h
  change i < 3 at hi
  match i, hi with
  | 0, _ => simp [threeMoves] at h
  | 1, _ => simp [threeMoves] at h
  | 2, _ =>
    change Move.dropMove .pawn (0, 0) = .dropMove pt dst at h
    rw [Move.dropMove.injEq] at h
    obtain ⟨rfl, -⟩ := h
    change PieceType.pawn ∈ afterGold.board.hand afterGold.turn
    decide

-- The drop put a first-player pawn on `(0, 0)` and emptied the first player's hand.
example : afterDrop.board.grid (0, 0) = some ⟨.sente, .pawn⟩ := by decide
example : afterDrop.board.hand .sente = ∅ := by decide

end CaptureDemoteTests
end MPC
