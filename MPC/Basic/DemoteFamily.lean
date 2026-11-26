import MPC.Basic.Demote
import MPC.Invariants.PieceFamilyCount
/-!
# MPC.Basic.DemoteFamily

Demoting keeps the piece families.

 counts pieces by family and needs each family to be closed under promotion
(`PromoteStable`). Promotion undoes demotion:

- `promote_demote`: `pt.demote.promote = pt.promote` for every type. A promoted type
  is its own promotion, and promoting its original piece gives it back.
- `PromoteStable.demote_iff`: so a promotion-stable family is also closed under
  demotion, `F pt.demote ↔ F pt`.
- `familyInd_demote`: the family indicator of a square does not change when its piece
  is demoted.

 makes `applyMove` put a captured piece into the hand as its original piece; with
these, the family counts of  stay as they are.

-/

namespace MPC

/-- Promoting the original piece gives the promotion of the piece. -/
theorem PieceType.promote_demote (pt : PieceType) : pt.demote.promote = pt.promote := by
  cases pt <;> rfl

/-- A promotion-stable family is closed under demotion. -/
theorem PromoteStable.demote_iff {F : PieceType → Prop} (hF : PromoteStable F)
    (pt : PieceType) : F pt.demote ↔ F pt := by
  have h := hF pt.demote
  rw [PieceType.promote_demote] at h
  exact h.symm.trans (hF pt)

/-- Demoting the piece on a square keeps the indicator of a promotion-stable family. -/
theorem familyInd_demote (F : PieceType → Prop) [DecidablePred F] (hF : PromoteStable F)
    (p : Piece) :
    familyInd F (some { p with pieceType := p.pieceType.demote }) = familyInd F (some p) := by
  simp only [familyInd, hF.demote_iff]

end MPC
