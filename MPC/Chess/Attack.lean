import MPC.Chess.Basic
import Mathlib.Algebra.Order.Ring.Int

/-! Geometric attacks, independently of move legality. Pinned pieces still
attack; pawn attacks are diagonal, unlike their quiet moves. The source piece
and target king are supplied separately by `inCheck` and `KingsWellPlaced`. -/

namespace MPC.Chess

/-- A board square in the open straight segment, excluding both endpoints. -/
def Between (src dst q : Pos) : Prop :=
  q ≠ src ∧ q ≠ dst ∧
    (q.toInt.1 - src.toInt.1) * (dst.toInt.2 - src.toInt.2) =
      (q.toInt.2 - src.toInt.2) * (dst.toInt.1 - src.toInt.1) ∧
    min src.toInt.1 dst.toInt.1 ≤ q.toInt.1 ∧
    q.toInt.1 ≤ max src.toInt.1 dst.toInt.1 ∧
    min src.toInt.2 dst.toInt.2 ≤ q.toInt.2 ∧
    q.toInt.2 ≤ max src.toInt.2 dst.toInt.2

instance (src dst q : Pos) : Decidable (Between src dst q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def pathClear (board : Board) (src dst : Pos) : Prop :=
  ∀ q, Between src dst q → board q = none

instance (board : Board) (src dst : Pos) : Decidable (pathClear board src dst) :=
  inferInstanceAs (Decidable (∀ q, Between src dst q → board q = none))

@[simp] theorem not_between_source (src dst : Pos) : ¬ Between src dst src := by
  intro h
  exact h.1 rfl

@[simp] theorem not_between_destination (src dst : Pos) : ¬ Between src dst dst := by
  intro h
  exact h.2.1 rfl

theorem pathClear_empty (src dst : Pos) : pathClear Board.empty src dst := by
  intro _ _
  rfl

theorem pathClear_mono {before after : Board} {src dst : Pos}
    (h : ∀ p, before p = none → after p = none)
    (hc : pathClear before src dst) : pathClear after src dst := by
  intro p hp
  exact h p (hc p hp)

def attacks (board : Board) (piece : Piece) (src dst : Pos) : Prop :=
  let dx := (Pos.delta src dst).1
  let dy := (Pos.delta src dst).2
  src ≠ dst ∧ match piece.kind with
    | .king => |dx| ≤ 1 ∧ |dy| ≤ 1
    | .queen => (dx = 0 ∨ dy = 0 ∨ |dx| = |dy|) ∧ pathClear board src dst
    | .rook => (dx = 0 ∨ dy = 0) ∧ pathClear board src dst
    | .bishop => |dx| = |dy| ∧ pathClear board src dst
    | .knight => (|dx| = 1 ∧ |dy| = 2) ∨ (|dx| = 2 ∧ |dy| = 1)
    | .pawn => |dx| = 1 ∧ dy = piece.owner.forward

instance (board : Board) (piece : Piece) (src dst : Pos) :
    Decidable (attacks board piece src dst) := by
  unfold attacks
  cases piece.kind <;> infer_instance

@[simp] theorem attacks_not_self (board : Board) (piece : Piece) (src : Pos) :
    ¬ attacks board piece src src := by
  intro h
  exact h.1 rfl

theorem attacks_mono {before after : Board} {piece : Piece} {src dst : Pos}
    (h : ∀ p, before p = none → after p = none)
    (ha : attacks before piece src dst) : attacks after piece src dst := by
  rcases piece with ⟨owner, kind⟩
  cases kind with
  | king | knight | pawn => exact ha
  | queen | rook | bishop => exact ⟨ha.1, ha.2.1, pathClear_mono h ha.2.2⟩

def inCheck (board : Board) (owner : Color) (target : Pos) : Prop :=
  ∃ src piece, board src = some piece ∧ piece.owner = owner.opponent ∧
    attacks board piece src target

instance (board : Board) (owner : Color) (target : Pos) :
    Decidable (inCheck board owner target) :=
  inferInstanceAs (Decidable (∃ src piece, board src = some piece ∧
    piece.owner = owner.opponent ∧ attacks board piece src target))

theorem inCheck_mono {before after : Board} {owner : Color} {target : Pos}
    (he : ∀ p, before p = none → after p = none)
    (hp : ∀ src piece, before src = some piece → piece.owner = owner.opponent →
      attacks before piece src target → after src = some piece)
    (hc : inCheck before owner target) : inCheck after owner target := by
  obtain ⟨src, piece, hs, ho, ha⟩ := hc
  exact ⟨src, piece, hp src piece hs ho ha, ho, attacks_mono he ha⟩

/-- One king of each color, at exactly the designated squares. -/
def KingsWellPlaced (board : Board) (kingPos : Color → Pos) : Prop :=
  ∀ owner pos, board pos = some ⟨owner, .king⟩ ↔ pos = kingPos owner

theorem KingsWellPlaced.king_present {board : Board} {kingPos : Color → Pos}
    (h : KingsWellPlaced board kingPos) (owner : Color) :
    board (kingPos owner) = some ⟨owner, .king⟩ :=
  (h owner _).mpr rfl

theorem KingsWellPlaced.positions_injective {board : Board} {kingPos : Color → Pos}
    (h : KingsWellPlaced board kingPos) : Function.Injective kingPos := by
  intro a b hab
  have hp := h.king_present a
  rw [hab, h.king_present b] at hp
  exact (congrArg Piece.owner (Option.some.inj hp)).symm

theorem KingsWellPlaced.positions_unique {board : Board} {kp kq : Color → Pos}
    (hp : KingsWellPlaced board kp) (hq : KingsWellPlaced board kq) : kp = kq := by
  funext owner
  exact (hq owner _).mp (hp.king_present owner)

theorem KingsWellPlaced.inCheck_iff_exists_king {board : Board} {kp : Color → Pos}
    (h : KingsWellPlaced board kp) (owner : Color) :
    inCheck board owner (kp owner) ↔
      ∃ p, board p = some ⟨owner, .king⟩ ∧ inCheck board owner p := by
  constructor
  · intro hc
    exact ⟨kp owner, h.king_present owner, hc⟩
  · rintro ⟨p, hp, hc⟩
    rwa [(h owner p).mp hp] at hc

end MPC.Chess
