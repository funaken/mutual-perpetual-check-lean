import MPC.Trace.MoveTrace
import MPC.Basic.OrientedCheck
/-!
# MPC.Trace.KingPlacement

Each board has exactly one king of each owner at the supplied positions.
Trace positions may vary by state. Tracking assumes consistency of both states;
it does not establish consistency preservation from the initial board alone.
-/

namespace MPC

/-- Exact king placement; hands and the number of non-king pieces are unrestricted. -/
def KingsWellPlaced (board : Board) (kingPos : Player → Pos) : Prop :=
  ∀ (owner : Player) (pos : Pos),
    board.grid pos = some { owner := owner, pieceType := .king } ↔ pos = kingPos owner

theorem KingsWellPlaced.king_present {board : Board} {kingPos : Player → Pos}
    (h : KingsWellPlaced board kingPos) (owner : Player) :
    board.grid (kingPos owner) = some { owner := owner, pieceType := .king } :=
  (h owner (kingPos owner)).mpr rfl

theorem KingsWellPlaced.positions_injective {board : Board} {kingPos : Player → Pos}
    (h : KingsWellPlaced board kingPos) : Function.Injective kingPos := by
  intro p q heq
  have hp := h.king_present p
  have hq := h.king_present q
  rw [heq] at hp
  exact congrArg Piece.owner (Option.some.inj (hp.symm.trans hq))

theorem KingsWellPlaced.positions_unique {board : Board} {first second : Player → Pos}
    (hfirst : KingsWellPlaced board first) (hsecond : KingsWellPlaced board second) :
    first = second := by
  funext owner
  exact (hsecond owner (first owner)).mp (hfirst.king_present owner)

/-- With consistent placement, the supplied target is exactly the owner's actual king. -/
theorem KingsWellPlaced.inCheckOriented_iff_exists_king {board : Board} {kingPos : Player → Pos}
    (h : KingsWellPlaced board kingPos) (owner : Player) :
    inCheckOriented board owner (kingPos owner) ↔
      ∃ pos : Pos, board.grid pos = some { owner := owner, pieceType := .king } ∧
        inCheckOriented board owner pos := by
  constructor
  · intro hc; exact ⟨kingPos owner, h.king_present owner, hc⟩
  · rintro ⟨pos, hp, hc⟩
    rw [(h owner pos).mp hp] at hc
    exact hc

namespace MoveTrace

/-- External, state-indexed placement condition; no fixed king position is assumed. -/
def KingsWellPlaced (tr : MoveTrace) (kingPos : Fin (tr.len + 1) → Player → Pos) : Prop :=
  ∀ i, MPC.KingsWellPlaced (tr.states i).board (kingPos i)

theorem KingsWellPlaced.positions_unique {tr : MoveTrace}
    {first second : Fin (tr.len + 1) → Player → Pos}
    (hfirst : tr.KingsWellPlaced first) (hsecond : tr.KingsWellPlaced second) : first = second := by
  funext i
  exact (hfirst i).positions_unique (hsecond i)

/-- A king at the source is at the destination afterward, provided the after-state
    placement is consistent. This does not validate capture or promotion legality. -/
theorem kingPos_after_boardMove_king (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kingPos)
    (i : Fin tr.len) (owner : Player) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hp : (tr.before i).board.grid src = some { owner := owner, pieceType := .king }) :
    kingPos i.succ owner = dst := by
  have hd := tr.boardMove_grid_dst ht i src dst promote hm
  rw [hp] at hd
  have hd' : (tr.after i).board.grid dst = some { owner := owner, pieceType := .king } := by
    simpa [PieceType.promote] using hd
  exact ((hk i.succ owner dst).mp hd').symm

/-- Only a non-endpoint king is tracked as stationary by this board-move theorem. -/
theorem kingPos_after_boardMove_of_ne (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kingPos)
    (i : Fin tr.len) (owner : Player) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hs : kingPos i.castSucc owner ≠ src) (hd : kingPos i.castSucc owner ≠ dst) :
    kingPos i.succ owner = kingPos i.castSucc owner := by
  have he := tr.boardMove_grid_other ht i src dst promote (kingPos i.castSucc owner) hm hs hd
  have hp := (hk i.castSucc).king_present owner
  exact ((hk i.succ owner _).mp (he.trans hp)).symm

theorem kingPos_after_dropMove_of_ne (tr : MoveTrace)
    (kingPos : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kingPos)
    (i : Fin tr.len) (owner : Player) (pt : PieceType) (dst : Pos)
    (hm : tr.moves i = .dropMove pt dst)
    (hd : kingPos i.castSucc owner ≠ dst) :
    kingPos i.succ owner = kingPos i.castSucc owner := by
  have he := tr.dropMove_grid_other ht i pt dst (kingPos i.castSucc owner) hm hd
  have hp := (hk i.castSucc).king_present owner
  exact ((hk i.succ owner _).mp (he.trans hp)).symm

end MoveTrace
end MPC
