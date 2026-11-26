import MPC.Basic.Lemmas
import MPC.Pieces.SilverMove
/-! Geometric constraints for the silver case: occupied rays, checker directions,
and the two possible relative king positions. -/

namespace MPC

private theorem slide_mem_king (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.slideDirs.map (Dir.forPlayer · o)) : d ∈ PieceType.king.stepDirs := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), x ∈ PieceType.king.stepDirs := by
    cases o <;> cases pt <;> decide
  exact key d h

theorem forwardSign_opponent (o : Player) : forwardSign o.opponent = -forwardSign o := by
  cases o <;> rfl

theorem forwardSign_cases (o : Player) : forwardSign o = 1 ∨ forwardSign o = -1 := by
  cases o
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The relative coordinates of a half-line point. -/
theorem OnRay.relTo_eq {K q : Pos} {d : Dir} {c : ℤ} (h : OnRay K d c q) :
    relTo K q = (c * d.1, c * d.2) := by
  obtain ⟨_, _, hq⟩ := h
  simp only [relTo, hq]
  ext <;> dsimp only <;> ring

/-- A point whose relative coordinates are a positive multiple of a king direction
    lies on that half-line. -/
theorem OnRay.of_relTo {K q : Pos} {d : Dir} {c : ℤ} (hd : d ∈ PieceType.king.stepDirs)
    (hc : 0 < c) (h : relTo K q = (c * d.1, c * d.2)) : OnRay K d c q := by
  refine ⟨hd, hc, ?_⟩
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [relTo] at h1 h2
  ext <;> dsimp only <;> linarith

/-- Every step is a king step or a knight's jump toward its owner's front. -/
theorem stepDir_unit_or_forward_knight (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.stepDirs.map (Dir.forPlayer · o)) :
    d ∈ PieceType.king.stepDirs ∨ ((d.1 = 1 ∨ d.1 = -1) ∧ d.2 = 2 * forwardSign o) := by
  have key : ∀ x ∈ pt.stepDirs.map (Dir.forPlayer · o), x ∈ PieceType.king.stepDirs ∨
      ((x.1 = 1 ∨ x.1 = -1) ∧ x.2 = 2 * forwardSign o) := by
    cases o <;> cases pt <;> decide
  exact key d h

/-- A sliding attack from `B` on `T` that is not a step slides toward `T` along the
    half-line from `T` through `B`. -/
theorem slideDir_of_attack_not_step (board : Board) (o : Player) (pt : PieceType) (B T : Pos)
    (hatk : attacksOriented board o pt B T)
    (hstep : Pos.dirTo B T ∉ pt.stepDirs.map (Dir.forPlayer · o)) {d : Dir} {n : ℤ}
    (hB : OnRay T d n B) :
    ((-d.1, -d.2) : Dir) ∈ pt.slideDirs.map (Dir.forPlayer · o) := by
  rcases hatk with hst | ⟨sd, hsd, _, k, hk, hx, hy, _⟩
  · exact absurd hst hstep
  obtain ⟨hd, hn, hBe⟩ := hB
  have hx' : (Pos.dirTo B T).1 = -(n * d.1) := by
    have := congrArg Prod.fst hBe
    dsimp [Pos.dirTo, Pos.toInt] at this ⊢
    linarith
  have hy' : (Pos.dirTo B T).2 = -(n * d.2) := by
    have := congrArg Prod.snd hBe
    dsimp [Pos.dirTo, Pos.toInt] at this ⊢
    linarith
  rw [hx'] at hx
  rw [hy'] at hy
  have hsdK := slide_mem_king _ _ sd hsd
  obtain ⟨d1, d2⟩ := d
  obtain ⟨s1, s2⟩ := sd
  rw [PieceType.mem_king_stepDirs_iff] at hd hsdK
  dsimp only at hd hsdK hx hy ⊢
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have key : s1 = -d1 ∧ s2 = -d2 := by
    rcases (show d1 = -1 ∨ d1 = 0 ∨ d1 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show d2 = -1 ∨ d2 = 0 ∨ d2 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show s1 = -1 ∨ s1 = 0 ∨ s1 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show s2 = -1 ∨ s2 = 0 ∨ s2 = 1 by omega) with rfl | rfl | rfl <;>
      omega
  obtain ⟨rfl, rfl⟩ := key
  exact hsd

/-- A slider along a rank or file that does not slide toward its owner's front is a
    rook or a dragon: lances slide only forward, bishops and horses diagonally. -/
theorem rookDragon_of_slideDir (pt : PieceType) (o : Player) (sd : Dir)
    (h : sd ∈ pt.slideDirs.map (Dir.forPlayer · o)) (horth : sd.1 = 0 ∨ sd.2 = 0)
    (hfwd : sd ≠ (0, forwardSign o)) : pt = .rook ∨ pt = .dragon := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), (x.1 = 0 ∨ x.2 = 0) →
      x ≠ (0, forwardSign o) → pt = .rook ∨ pt = .dragon := by
    cases o <;> cases pt <;> decide
  exact key sd h horth hfwd

/-- Corollary 3.4 on the board: the checker `X` on `C` attacks `L`, and `D` is `C` or
    on `X`'s sliding line to `L`. Either `X` stands on `D` and attacks by a step, or
    `X` slides toward `L` along a half-line from `L` through `D`, and every square
    strictly between `L` and `C` is empty. -/
theorem checker_cases (b : Board) (X : Piece) (C L D : Pos)
    (hatk : attacksOriented b X.owner X.pieceType C L)
    (hD : D = C ∨ (D.toInt ∈ slidePath C L ∧
      Pos.dirTo C L ∉ X.pieceType.stepDirs.map (Dir.forPlayer · X.owner))) :
    (D = C ∧ Pos.dirTo C L ∈ X.pieceType.stepDirs.map (Dir.forPlayer · X.owner)) ∨
    (∃ (d : Dir) (n c : ℤ), OnRay L d n C ∧ 1 ≤ c ∧ c ≤ n ∧
      D.toInt = (L.toInt.1 + c * d.1, L.toInt.2 + c * d.2) ∧
      ((-d.1, -d.2) : Dir) ∈ X.pieceType.slideDirs.map (Dir.forPlayer · X.owner) ∧
      ∀ c' : ℤ, 1 ≤ c' → c' < n → ∀ q : Pos,
        q.toInt = (L.toInt.1 + c' * d.1, L.toInt.2 + c' * d.2) → b.grid q = none) := by
  by_cases hst : Pos.dirTo C L ∈ X.pieceType.stepDirs.map (Dir.forPlayer · X.owner)
  · rcases hD with hD | ⟨_, hns⟩
    · exact Or.inl ⟨hD, hst⟩
    · exact absurd hst hns
  · obtain ⟨d, n, hC, hpc, hiff⟩ := ray_of_attack_not_step b _ _ C L hatk hst
    have hslide := slideDir_of_attack_not_step b _ _ C L hatk hst hC
    have hempty : ∀ c' : ℤ, 1 ≤ c' → c' < n → ∀ q : Pos,
        q.toInt = (L.toInt.1 + c' * d.1, L.toInt.2 + c' * d.2) → b.grid q = none := by
      intro c' h1 h2 q hq
      have hmem : q.toInt ∈ slidePath C L := (hiff _).mpr ⟨c', h1, h2, hq⟩
      have h := hpc q.toInt hmem (Pos.onBoard_toInt q) (Pos.onBoard_toInt q)
      rwa [Pos.toPos_toInt] at h
    refine Or.inr ?_
    rcases hD with rfl | ⟨hmem, _⟩
    · exact ⟨d, n, n, hC, by have := hC.2.1; omega, le_refl _, hC.2.2, hslide, hempty⟩
    · obtain ⟨c, hc1, hcn, hDe⟩ := (hiff _).mp hmem
      exact ⟨d, n, c, hC, hc1, hcn.le, hDe, hslide, hempty⟩

/-- Corollary 3.4's constraint on the mover's king `l` relative to the enemy king, at
    a move to `D` from `E`, when the checker's owner has forward sign `-τ`. The king
    sees `D` along a line whose first square past `D` is neither `E` nor the enemy
    king, or an enemy knight on `D` attacks it. -/
def CheckerConstraint (τ : ℤ) (D E l : ℤ × ℤ) : Prop :=
  (∃ sd ∈ PieceType.king.stepDirs, ∃ c : ℤ, 1 ≤ c ∧ l = (D.1 + c * sd.1, D.2 + c * sd.2) ∧
      (2 ≤ c → (D.1 + sd.1, D.2 + sd.2) ≠ E ∧ (D.1 + sd.1, D.2 + sd.2) ≠ (0, 0))) ∨
    ((l.1 = D.1 + 1 ∨ l.1 = D.1 - 1) ∧ l.2 = D.2 - 2 * τ)

/-- The board form of `checker_cases` gives `CheckerConstraint` when the move's source
    `E` and the enemy king's square `K` are occupied before the move. -/
theorem checkerConstraint_of_checker (b : Board) (X : Piece) (C L D E K : Pos)
    (hatk : attacksOriented b X.owner X.pieceType C L)
    (hD : D = C ∨ (D.toInt ∈ slidePath C L ∧
      Pos.dirTo C L ∉ X.pieceType.stepDirs.map (Dir.forPlayer · X.owner)))
    (hE : b.grid E ≠ none) (hK : b.grid K ≠ none) :
    CheckerConstraint (-forwardSign X.owner) (relTo K D) (relTo K E) (relTo K L) := by
  rcases checker_cases b X C L D hatk hD with ⟨rfl, hst⟩ | ⟨d, n, c, hC, hc1, hcn, hDe, _, hempty⟩
  · have hl : relTo K L =
        ((relTo K D).1 + (Pos.dirTo D L).1, (relTo K D).2 + (Pos.dirTo D L).2) := by
      simp only [relTo, Pos.dirTo, Pos.toInt]
      ext <;> dsimp only <;> ring
    rcases stepDir_unit_or_forward_knight _ _ _ hst with hu | ⟨h1, h2⟩
    · refine Or.inl ⟨_, hu, 1, le_refl _, ?_, fun h => absurd h (by norm_num)⟩
      rw [hl]
      ext <;> dsimp only <;> ring
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hl]
        dsimp only
        omega
      · rw [hl]
        dsimp only
        omega
  · refine Or.inl ⟨(-d.1, -d.2), neg_mem_king_stepDirs hC.1, c, hc1, ?_, fun h2 => ⟨?_, ?_⟩⟩
    · simp only [relTo, hDe]
      ext <;> dsimp only <;> ring
    · -- The first square past `D` toward `L` is empty, but `E` is occupied.
      intro h
      apply hE
      apply hempty (c - 1) (by omega) (by omega) E
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [relTo, hDe] at h1 h2
      ext <;> dsimp only <;> linarith
    · intro h
      apply hK
      apply hempty (c - 1) (by omega) (by omega) K
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [relTo, hDe] at h1 h2
      ext <;> dsimp only <;> linarith

/-- The king's position: if the mover's king `l` satisfies Corollary 3.4's
    constraint at both silver moves, between `(σ, 0)` and `(0, τ)`, and is not next to
    the enemy king, then it stands on `(2σ, τ)` or `(σ, 2τ)`. -/
theorem king_position_of_silver (τ σ : ℤ) (hτ : τ = 1 ∨ τ = -1) (hσ : σ = 1 ∨ σ = -1)
    (l : ℤ × ℤ) (hA : CheckerConstraint τ (0, τ) (σ, 0) l)
    (hB : CheckerConstraint τ (σ, 0) (0, τ) l)
    (hfar : ¬ (-1 ≤ l.1 ∧ l.1 ≤ 1 ∧ -1 ≤ l.2 ∧ l.2 ≤ 1)) :
    l = (2 * σ, τ) ∨ l = (σ, 2 * τ) := by
  obtain ⟨l1, l2⟩ := l
  unfold CheckerConstraint at hA hB
  dsimp only at hfar
  rcases hτ with rfl | rfl <;> rcases hσ with rfl | rfl <;>
    rcases hA with ⟨sd, hsd, c, hc, hl, hblk⟩ | hA <;>
    rcases hB with ⟨sd', hsd', c', hc', hl', hblk'⟩ | hB <;>
    (try simp only [PieceType.stepDirs, List.mem_cons, List.not_mem_nil,
      or_false] at hsd) <;>
    (try simp only [PieceType.stepDirs, List.mem_cons, List.not_mem_nil,
      or_false] at hsd') <;>
    (try rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try rcases hsd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Prod.mk.injEq, ne_eq] at * <;>
    omega

end MPC
