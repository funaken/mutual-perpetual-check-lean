import MPC.Legacy.MoveCompatibility
import MPC.Legacy.MoveTrace
import MPC.Trace.MoveTrace
import Lean
/-!
# MPC.Tests.MoveTrace

Constructive checks of the independent foundation. This module is compiled
separately so that the examples cannot use GameSeq or its consequences.
These are sequence-data examples, not periodic mutual-check or legal-shogi games.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "MoveTrace verification must not import GameSeq"

namespace MPC

-- The initial state remains available even when there are no moves.
example (initial : BoardState) :
    let tr : MoveTrace := { len := 0, states := fun _ => initial, moves := Fin.elim0 }
    tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧
      tr.BoardMoveEndpointsDistinct ∧ tr.BoardMovesFollowCanMoveTo := by
  exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

private def rookState (owner : Player) (destination : Square) : BoardState :=
  { board :=
      { grid := fun pos =>
          if pos = (4, 4) then some { owner := owner, pieceType := .rook }
          else if pos = (5, 4) then destination else none
        hand := fun _ => ∅ }
    turn := owner }

-- Adjacent horizontal rook motion works for either owner and any board.
private theorem rook_canMoveTo (board : Board) (owner : Player) :
    canMoveTo board owner .rook (4, 4) (5, 4) := by
  right
  refine ⟨(1, 0), ?_, by decide, 1, by decide, by decide, by decide, ?_⟩
  · cases owner <;> decide
  · simp [pathClear, show slidePath (4, 4) (5, 4) = [] from by decide]

-- Covers both owners, both promotion flags, and empty/occupied destinations.
-- Direction/path compliance uses the pre-promotion rook. In particular, all
-- four conditions coexist with a source whose contents actually change.
example (owner : Player) (promote : Bool) (destination : Square) :
    let tr := MoveTrace.single (rookState owner destination) (.boardMove (4, 4) (5, 4) promote)
    tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧
      tr.BoardMoveEndpointsDistinct ∧ tr.BoardMovesFollowCanMoveTo ∧
      (tr.after (0 : Fin 1)).board.grid (4, 4) ≠
        (tr.before (0 : Fin 1)).board.grid (4, 4) := by
  dsimp only
  refine ⟨MoveTrace.single_followsTransitions _ _, ?_, ?_, ?_, ?_⟩
  · intro i src dst flag h_move
    change Fin 1 at i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change Move.boardMove (4, 4) (5, 4) promote = .boardMove src dst flag at h_move
    cases h_move
    exact ⟨{ owner := owner, pieceType := .rook }, rfl, rfl⟩
  · intro i src dst flag h_move
    change Move.boardMove (4, 4) (5, 4) promote = .boardMove src dst flag at h_move
    cases h_move
    decide
  · intro i src dst flag piece h_move h_piece
    change Fin 1 at i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change Move.boardMove (4, 4) (5, 4) promote = .boardMove src dst flag at h_move
    cases h_move
    change some { owner := owner, pieceType := PieceType.rook } = some piece at h_piece
    cases h_piece
    exact rook_canMoveTo _ owner
  · change (applyMove (rookState owner destination) (.boardMove (4, 4) (5, 4) promote)).board.grid
        (4, 4) ≠ some { owner := owner, pieceType := .rook }
    rw [applyMove_boardMove_grid_src _ _ _ _ (by decide)]
    simp

-- Board-move predicates are vacuous on a drop; they do not validate its hand,
-- destination, or piece type. The state update still has a constructive model.
example (initial : BoardState) (pt : PieceType) (dst : Pos) :
    let tr := MoveTrace.single initial (.dropMove pt dst)
    tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧
      tr.BoardMoveEndpointsDistinct ∧ tr.BoardMovesFollowCanMoveTo ∧
      (tr.after (0 : Fin 1)).board.grid dst = some { owner := initial.turn, pieceType := pt } := by
  dsimp only
  refine ⟨MoveTrace.single_followsTransitions _ _, ?_, ?_, ?_, ?_⟩
  · intro i src dst' flag h_move
    change Move.dropMove pt dst = .boardMove src dst' flag at h_move
    cases h_move
  · intro i src dst' flag h_move
    change Move.dropMove pt dst = .boardMove src dst' flag at h_move
    cases h_move
  · intro i src dst' flag piece h_move
    change Move.dropMove pt dst = .boardMove src dst' flag at h_move
    cases h_move
  · exact applyMove_dropMove_grid_dst initial pt dst

end MPC
