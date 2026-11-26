import MPC.Basic.Grid
/-! Shared player and board-coordinate facts. -/
namespace MPC

/-- Changing sides twice recovers the original player. -/
theorem Player.opponent_opponent (p : Player) : p.opponent.opponent = p := by
  cases p <;> rfl

/-- The opposing player is different. -/
theorem Player.opponent_ne_self (p : Player) : p.opponent ≠ p := by
  cases p <;> decide

/-- Every player is either a given player or its opponent. -/
theorem Player.eq_or_eq_opponent (o p : Player) : o = p ∨ o = p.opponent := by
  cases o <;> cases p <;> simp [Player.opponent]

/-- The integer coordinates of a board position lie on the board. -/
theorem Pos.onBoard_toInt (A : Pos) : onBoard A.toInt := by
  simp only [onBoard, Pos.toInt]
  omega

/-- Converting a board position to integer coordinates and back is identity. -/
theorem Pos.toPos_toInt (A : Pos) (h : onBoard A.toInt) : toPos A.toInt h = A := by
  ext <;> simp [toPos, Pos.toInt]

/-- A king step is a nonzero displacement with each coordinate between -1 and 1. -/
theorem PieceType.mem_king_stepDirs_iff (d : Dir) :
    d ∈ PieceType.king.stepDirs ↔
      -1 ≤ d.1 ∧ d.1 ≤ 1 ∧ -1 ≤ d.2 ∧ d.2 ≤ 1 ∧ ¬ (d.1 = 0 ∧ d.2 = 0) := by
  obtain ⟨x, y⟩ := d
  dsimp only
  constructor
  · intro h
    simp [PieceType.stepDirs] at h
    omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rcases (show x = -1 ∨ x = 0 ∨ x = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show y = -1 ∨ y = 0 ∨ y = 1 by omega) with rfl | rfl | rfl <;>
      simp_all [PieceType.stepDirs]

end MPC
