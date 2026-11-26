import MPC.Legacy.MoveCompatibility
import MPC.Legacy.MoveTrace
import MPC.Trace.MoveTrace
import Lean
/-!
# MPC.Tests.OrientedMove

Behavioral checks for the owner-oriented predicate .
These verify direction/path behavior, not complete shogi legality.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Oriented move verification must not import GameSeq"

namespace MPC

private def forward (owner : Player) : Pos :=
  match owner with | .sente => (4, 5) | .gote => (4, 3)

-- Arbitrary boards include blocked and occupied squares. Step moves ignore them.
example (board : Board) (owner : Player) (pt : PieceType)
    (h : pt = .pawn ∨ pt = .silver ∨ pt = .gold ∨ pt = .promotedSilver ∨
      pt = .promotedKnight ∨ pt = .promotedLance ∨ pt = .tokin) :
    canMoveToOriented board owner pt (4, 4) (forward owner) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases owner <;> left <;> decide

example (board : Board) (owner : Player) :
    canMoveToOriented board owner .knight (4, 4)
      (match owner with | .sente => (5, 6) | .gote => (5, 2)) := by
  cases owner <;> left <;> decide

-- Pawn/silver cannot step straight backward; gold-like pieces cannot step
-- diagonally backward; knights cannot jump backward.
example (board : Board) (owner : Player) (pt : PieceType) (h : pt = .pawn ∨ pt = .silver) :
    ¬ canMoveToOriented board owner pt (4, 4) (forward owner.opponent) := by
  rcases h with rfl | rfl <;> cases owner <;>
    simp only [canMoveToOriented, PieceType.slideDirs, List.map_nil,
      List.not_mem_nil, false_and, exists_false, or_false] <;> decide

example (board : Board) (owner : Player) (pt : PieceType)
    (h : pt = .gold ∨ pt = .promotedSilver ∨ pt = .promotedKnight ∨
      pt = .promotedLance ∨ pt = .tokin) :
    ¬ canMoveToOriented board owner pt (4, 4)
      (match owner with | .sente => (5, 3) | .gote => (5, 5)) := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> cases owner <;>
    simp only [canMoveToOriented, PieceType.slideDirs, List.map_nil,
      List.not_mem_nil, false_and, exists_false, or_false] <;> decide

example (board : Board) (owner : Player) :
    ¬ canMoveToOriented board owner .knight (4, 4)
      (match owner with | .sente => (5, 2) | .gote => (5, 6)) := by
  cases owner <;>
    simp only [canMoveToOriented, PieceType.slideDirs, List.map_nil,
      List.not_mem_nil, false_and, exists_false, or_false] <;> decide

example (board : Board) (owner : Player) :
    canMoveToOriented board owner .king (4, 4) (5, 5) ∧
    canMoveToOriented board owner .dragon (4, 4) (5, 5) ∧
    canMoveToOriented board owner .horse (4, 4) (5, 4) := by
  cases owner <;> exact ⟨Or.inl (by decide), Or.inl (by decide), Or.inl (by decide)⟩

private def emptyBoard : Board := { grid := fun _ => none, hand := fun _ => ∅ }

-- Maximum-length slides reach the edge; both players use the same geometry.
example (owner : Player) : canMoveToOriented emptyBoard owner .rook (0, 4) (8, 4) := by
  right
  refine ⟨(1, 0), ?_, by decide, 8, by decide, by decide, by decide, ?_⟩
  · cases owner <;> decide
  · simp [pathClear, emptyBoard]

example (owner : Player) : canMoveToOriented emptyBoard owner .bishop (0, 0) (8, 8) := by
  right
  refine ⟨(1, 1), ?_, by decide, 8, by decide, by decide, by decide, ?_⟩
  · cases owner <;> decide
  · simp [pathClear, emptyBoard]

example (owner : Player) :
    canMoveToOriented emptyBoard owner .lance
      (match owner with | .sente => (4, 0) | .gote => (4, 8))
      (match owner with | .sente => (4, 8) | .gote => (4, 0)) := by
  cases owner
  · exact Or.inr ⟨(0, 1), by decide, by decide, 8, by decide, by decide, by decide,
      by simp [pathClear, emptyBoard]⟩
  · exact Or.inr ⟨(0, -1), by decide, by decide, 8, by decide, by decide, by decide,
      by simp [pathClear, emptyBoard]⟩

-- An occupied intermediate square blocks a slide, independently of its owner/type.
example (board : Board) (owner : Player) (piece : Piece)
    (h_block : board.grid (4, 4) = some piece) :
    ¬ canMoveToOriented board owner .rook (0, 4) (8, 4) := by
  rintro (hs | ⟨_, _, _, _, _, _, _, hc⟩)
  · simp [PieceType.stepDirs] at hs
  · have hclear := hc (4, 4) (by decide)
      (by unfold onBoard; decide) (by unfold onBoard; decide)
    change board.grid (4, 4) = none at hclear
    rw [h_block] at hclear
    cases hclear

example (board : Board) (owner : Player) :
    ¬ canMoveToOriented board owner .lance (4, 4) (forward owner.opponent) := by
  cases owner <;>
    simp [canMoveToOriented, forward, Player.opponent,
      show Pos.dirTo (4, 4) (4, 3) = (0, -1) from by decide,
      show Pos.dirTo (4, 4) (4, 5) = (0, 1) from by decide,
      PieceType.stepDirs, PieceType.slideDirs, Dir.forPlayer, Dir.flip, Dir.normalize]

-- Same normalized direction does not suffice: (1,2) is not a bishop ray.
example (board : Board) (owner : Player) :
    ¬ canMoveToOriented board owner .bishop (4, 4) (5, 6) := by
  rintro (hs | ⟨sd, _, hn, k, _, hx, hy, _⟩)
  · simp [PieceType.stepDirs] at hs
  · have hsd : sd = (1, 1) := by exact hn.symm
    rw [hsd] at hx hy
    change (1 : ℤ) = ↑k * 1 at hx
    change (2 : ℤ) = ↑k * 1 at hy
    omega

-- Legacy diagnostics: pawn steps ignore owner; lance directions are reversed.
example (board : Board) :
    canMoveTo board .sente .pawn (4, 4) (4, 5) ∧
    canMoveTo board .gote .pawn (4, 4) (4, 5) ∧
    ¬ canMoveTo board .gote .pawn (4, 4) (4, 3) := by
  refine ⟨Or.inl (by decide), Or.inl (by decide), ?_⟩
  simp [canMoveTo, show Pos.dirTo (4, 4) (4, 3) = (0, -1) from by decide,
    PieceType.stepDirs, PieceType.slideDirs, Dir.forPlayer, Player.opponent]

example (board : Board) :
    canMoveTo board .sente .lance (4, 4) (4, 3) ∧
    ¬ canMoveTo board .sente .lance (4, 4) (4, 5) := by
  refine ⟨Or.inr ⟨(0, -1), by decide, by decide, 1, by decide, by decide, by decide, ?_⟩, ?_⟩
  · simp [pathClear, show slidePath (4, 4) (4, 3) = [] from by decide]
  · simp [canMoveTo, show Pos.dirTo (4, 4) (4, 5) = (0, 1) from by decide,
      PieceType.stepDirs, PieceType.slideDirs, Dir.forPlayer, Player.opponent, Dir.flip, Dir.normalize]

private def pawnState (owner : Player) (destination : Square) : BoardState :=
  { board :=
      { grid := fun p =>
          if p = (4, 4) then some { owner := owner, pieceType := .pawn }
          else if p = forward owner then destination else none
        hand := fun _ => ∅ }
    turn := owner }

-- Both owners/promotion flags and arbitrary destination contents. Direction/path
-- compliance uses the pawn before promotion; capture/promotion legality is separate.
example (owner : Player) (promote : Bool) (destination : Square) :
    let tr := MoveTrace.single (pawnState owner destination)
      (.boardMove (4, 4) (forward owner) promote)
    tr.FollowsTransitions ∧ tr.BoardMoveSourcesOwned ∧
      tr.BoardMoveEndpointsDistinct ∧ tr.BoardMovesFollowCanMoveToOriented ∧
      (tr.after (0 : Fin 1)).board.grid (4, 4) ≠
        (tr.before (0 : Fin 1)).board.grid (4, 4) := by
  dsimp only
  refine ⟨MoveTrace.single_followsTransitions _ _, ?_, ?_, ?_, ?_⟩
  · intro i src dst flag h_move
    change Fin 1 at i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change Move.boardMove (4, 4) (forward owner) promote = .boardMove src dst flag at h_move
    cases h_move
    exact ⟨{ owner := owner, pieceType := .pawn }, rfl, rfl⟩
  · intro i src dst flag h_move
    change Move.boardMove (4, 4) (forward owner) promote = .boardMove src dst flag at h_move
    cases h_move
    cases owner <;> decide
  · intro i src dst flag piece h_move h_piece
    change Fin 1 at i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change Move.boardMove (4, 4) (forward owner) promote = .boardMove src dst flag at h_move
    cases h_move
    change some { owner := owner, pieceType := PieceType.pawn } = some piece at h_piece
    cases h_piece
    cases owner <;> left <;> decide
  · change (applyMove (pawnState owner destination)
        (.boardMove (4, 4) (forward owner) promote)).board.grid (4, 4) ≠
      some { owner := owner, pieceType := .pawn }
    rw [applyMove_boardMove_grid_src _ _ _ _ (by cases owner <;> decide)]
    simp

example (promote : Bool) (destination : Square) :
    ¬ (MoveTrace.single (pawnState .gote destination)
      (.boardMove (4, 4) (4, 3) promote)).BoardMovesFollowCanMoveTo := by
  intro h
  have hm := h (0 : Fin 1) (4, 4) (4, 3) promote { owner := .gote, pieceType := .pawn } rfl rfl
  simp [canMoveTo, show Pos.dirTo (4, 4) (4, 3) = (0, -1) from by decide,
    PieceType.stepDirs, PieceType.slideDirs, Dir.forPlayer, Player.opponent] at hm

-- No moves, or only a drop: the new board-move condition is vacuous.
example (initial : BoardState) :
    MoveTrace.BoardMovesFollowCanMoveToOriented
      { len := 0, states := fun _ => initial, moves := Fin.elim0 } := fun i => Fin.elim0 i

example (initial : BoardState) (pt : PieceType) (dst : Pos) :
    (MoveTrace.single initial (.dropMove pt dst)).BoardMovesFollowCanMoveToOriented := by
  intro i src dst' flag piece h_move
  change Move.dropMove pt dst = .boardMove src dst' flag at h_move
  cases h_move

end MPC
