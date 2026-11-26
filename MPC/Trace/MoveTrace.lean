import MPC.Basic.MoveLemmas
import MPC.Basic.OrientedMove
/-!
# MPC.Trace.MoveTrace

Finite sequence data. Transition and board-move
conditions are separate propositions, not fields of the data type.
`BoardMovesFollowCanMoveToOriented` checks movement direction and path.
It does not certify complete shogi legality. The historical movement condition
is available separately from `MPC.Legacy.MoveTrace`.
-/

namespace MPC

/-- A finite sequence of states and moves, including sequences of length zero. -/
structure MoveTrace where
  len : Nat
  states : Fin (len + 1) → BoardState
  moves : Fin len → Move

namespace MoveTrace

def before (tr : MoveTrace) (i : Fin tr.len) : BoardState := tr.states i.castSucc

def after (tr : MoveTrace) (i : Fin tr.len) : BoardState := tr.states i.succ

def FollowsTransitions (tr : MoveTrace) : Prop :=
  ∀ i : Fin tr.len, tr.after i = applyMove (tr.before i) (tr.moves i)

def BoardMoveSourcesOwned (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (src dst : Pos) (promote : Bool),
    tr.moves i = .boardMove src dst promote →
      ∃ piece : Piece, (tr.before i).board.grid src = some piece ∧
        piece.owner = (tr.before i).turn

def BoardMoveEndpointsDistinct (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (src dst : Pos) (promote : Bool),
    tr.moves i = .boardMove src dst promote → src ≠ dst

/-- Owner-oriented direction/path condition using the pre-promotion piece type.
    Presence/ownership are separate; this imposes no drop or full-legality rule. -/
def BoardMovesFollowCanMoveToOriented (tr : MoveTrace) : Prop :=
  ∀ (i : Fin tr.len) (src dst : Pos) (promote : Bool) (piece : Piece),
    tr.moves i = .boardMove src dst promote →
    (tr.before i).board.grid src = some piece →
      canMoveToOriented (tr.before i).board piece.owner piece.pieceType src dst

theorem boardMoveEndpointsDistinct_of_oriented (tr : MoveTrace)
    (hsrc : tr.BoardMoveSourcesOwned) (hm : tr.BoardMovesFollowCanMoveToOriented) :
    tr.BoardMoveEndpointsDistinct := by
  intro i src dst promote hmove heq
  obtain ⟨piece, hp, _⟩ := hsrc i src dst promote hmove
  have h := hm i src dst promote piece hmove hp
  subst dst
  exact canMoveToOriented_not_self _ _ _ _ h

theorem turn_after_move (tr : MoveTrace) (h : tr.FollowsTransitions)
    (i : Fin tr.len) : (tr.after i).turn = (tr.before i).turn.opponent := by
  rw [h i]
  cases tr.moves i <;> simp [applyMove]

theorem boardMove_grid_src (tr : MoveTrace) (h : tr.FollowsTransitions)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (h_move : tr.moves i = .boardMove src dst promote) (h_ne : src ≠ dst) :
    (tr.after i).board.grid src = none := by
  rw [h i, h_move]
  exact applyMove_boardMove_grid_src _ src dst promote h_ne

theorem boardMove_grid_dst (tr : MoveTrace) (h : tr.FollowsTransitions)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (h_move : tr.moves i = .boardMove src dst promote) :
    (tr.after i).board.grid dst =
      match (tr.before i).board.grid src with
      | some piece => some { piece with
          pieceType := if promote then piece.pieceType.promote else piece.pieceType }
      | none => none := by
  rw [h i, h_move]
  exact applyMove_boardMove_grid_dst _ src dst promote

theorem boardMove_grid_other (tr : MoveTrace) (h : tr.FollowsTransitions)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool) (pos : Pos)
    (h_move : tr.moves i = .boardMove src dst promote)
    (h_src : pos ≠ src) (h_dst : pos ≠ dst) :
    (tr.after i).board.grid pos = (tr.before i).board.grid pos := by
  rw [h i, h_move]
  exact applyMove_boardMove_grid_other _ src dst promote pos h_src h_dst

theorem dropMove_grid_dst (tr : MoveTrace) (h : tr.FollowsTransitions)
    (i : Fin tr.len) (pt : PieceType) (dst : Pos)
    (h_move : tr.moves i = .dropMove pt dst) :
    (tr.after i).board.grid dst = some { owner := (tr.before i).turn, pieceType := pt } := by
  rw [h i, h_move]
  exact applyMove_dropMove_grid_dst _ pt dst

theorem dropMove_grid_other (tr : MoveTrace) (h : tr.FollowsTransitions)
    (i : Fin tr.len) (pt : PieceType) (dst pos : Pos)
    (h_move : tr.moves i = .dropMove pt dst) (h_ne : pos ≠ dst) :
    (tr.after i).board.grid pos = (tr.before i).board.grid pos := by
  rw [h i, h_move]
  exact applyMove_dropMove_grid_other _ pt dst pos h_ne

/-- Sequence data for one application of applyMove; no move legality is implied. -/
def single (initial : BoardState) (move : Move) : MoveTrace where
  len := 1
  states := fun j => if j.val = 0 then initial else applyMove initial move
  moves := fun _ => move

theorem single_followsTransitions (initial : BoardState) (move : Move) :
    (single initial move).FollowsTransitions := by
  intro i
  change Fin 1 at i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

end MoveTrace
end MPC
