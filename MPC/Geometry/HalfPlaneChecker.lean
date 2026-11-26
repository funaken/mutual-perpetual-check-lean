import MPC.Basic.Lemmas
import MPC.Geometry.KingLineChecker
/-!
# MPC.Geometry.HalfPlaneChecker

Half-planes for the paper's Definition 3.7, and the facts about checking pieces
that Proposition 3.8 needs, on periodic traces.

- `lineSide K L q` is the signed area of `K`, `L`, `q`: zero exactly on the line
  through `K` and `L` (`lineSide_eq_zero_iff_collinear`). Its two signs are the
  two half-planes. Along a line it is affine, so a point strictly between a point
  `C` and a point on the line lies on `C`'s side (`lineSide_pos_iff_of_between`).
- At every state there is at most one checking square (`checker_unique_of_periodic`).
  The kings never move, so a single reply cannot lift checks along two different
  lines. Two checks along the same ray would block each other.
- A reply lands on the checker's side (`destination_side_of_checker`). A
  discovered check's checker lies on the moved piece's source side
  (`unblockedChecker_side`).

-/

namespace MPC

private theorem pos_eq_of_toInt {a b : Pos} (h : a.toInt = b.toInt) : a = b := by
  have h1 : (a.1.val : ℤ) = b.1.val := congrArg Prod.fst h
  have h2 : (a.2.val : ℤ) = b.2.val := congrArg Prod.snd h
  exact Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2))

private theorem slide_mem_king (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.slideDirs.map (Dir.forPlayer · o)) : d ∈ PieceType.king.stepDirs := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), x ∈ PieceType.king.stepDirs := by
    cases o <;> cases pt <;> decide
  exact key d h

/-- The signed area of `K`, `L`, `q`: positive on one side of the line through `K`
    and `L`, negative on the other, zero on it. -/
def lineSide (K L q : Pos) : ℤ :=
  (L.toInt.1 - K.toInt.1) * (q.toInt.2 - K.toInt.2) -
    (L.toInt.2 - K.toInt.2) * (q.toInt.1 - K.toInt.1)

theorem lineSide_eq_zero_iff_collinear (K L q : Pos) :
    lineSide K L q = 0 ↔ Geometry.collinear K.toInt L.toInt q.toInt := by
  unfold lineSide Geometry.collinear
  constructor <;> intro h <;> linarith

theorem lineSide_left (K L : Pos) : lineSide K L K = 0 := by
  unfold lineSide
  ring

theorem lineSide_right (K L : Pos) : lineSide K L L = 0 := by
  unfold lineSide
  ring

/-- Along a line the signed area is affine: for `D` at parameter `x` and `Z` at
    parameter `n` from `C`, `n · side D = (n - x) · side C + x · side Z`. -/
theorem lineSide_affine (K L C D Z : Pos) (d : Dir) (x n : ℤ)
    (hD : D.toInt = (C.toInt.1 + x * d.1, C.toInt.2 + x * d.2))
    (hZ : Z.toInt = (C.toInt.1 + n * d.1, C.toInt.2 + n * d.2)) :
    n * lineSide K L D = (n - x) * lineSide K L C + x * lineSide K L Z := by
  unfold lineSide
  rw [hD, hZ]
  ring

/-- A point strictly between `C` and a point `Z` on the line lies on `C`'s side. -/
theorem lineSide_pos_iff_of_between (K L C D Z : Pos) (d : Dir) (x n : ℤ) (s : ℤ)
    (hD : D.toInt = (C.toInt.1 + x * d.1, C.toInt.2 + x * d.2))
    (hZ : Z.toInt = (C.toInt.1 + n * d.1, C.toInt.2 + n * d.2))
    (hZ0 : lineSide K L Z = 0) (hx : 0 < x) (hxn : x < n) :
    0 < s * lineSide K L D ↔ 0 < s * lineSide K L C := by
  have h := lineSide_affine K L C D Z d x n hD hZ
  rw [hZ0, mul_zero, add_zero] at h
  have h' : n * (s * lineSide K L D) = (n - x) * (s * lineSide K L C) := by
    rw [← mul_assoc, mul_comm n s, mul_assoc, h]
    ring
  constructor
  · intro hpos
    have : 0 < (n - x) * (s * lineSide K L C) := by
      rw [← h']
      exact mul_pos (by omega) hpos
    exact pos_of_mul_pos_right this (by omega)
  · intro hpos
    have : 0 < n * (s * lineSide K L D) := by
      rw [h']
      exact mul_pos (by omega) hpos
    exact pos_of_mul_pos_right this (by omega)

/-- Two unit directions reaching the same point from the same point with positive
    step counts are equal, and so are the counts. -/
theorem same_ray (P K : Pos) (d₁ d₂ : Dir) (a b : ℤ)
    (h₁ : d₁ ∈ PieceType.king.stepDirs) (h₂ : d₂ ∈ PieceType.king.stepDirs)
    (ha : 0 < a) (hb : 0 < b)
    (e₁ : K.toInt = (P.toInt.1 + a * d₁.1, P.toInt.2 + a * d₁.2))
    (e₂ : K.toInt = (P.toInt.1 + b * d₂.1, P.toInt.2 + b * d₂.2)) :
    d₁ = d₂ ∧ a = b := by
  have c1 : a * d₁.1 = b * d₂.1 := by
    have := congrArg Prod.fst (e₁.symm.trans e₂)
    simp only at this
    linarith
  have c2 : a * d₁.2 = b * d₂.2 := by
    have := congrArg Prod.snd (e₁.symm.trans e₂)
    simp only at this
    linarith
  obtain ⟨x₁, y₁⟩ := d₁
  obtain ⟨x₂, y₂⟩ := d₂
  rw [PieceType.mem_king_stepDirs_iff] at h₁ h₂
  dsimp only at h₁ h₂ c1 c2 ⊢
  rcases (show x₁ = -1 ∨ x₁ = 0 ∨ x₁ = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show y₁ = -1 ∨ y₁ = 0 ∨ y₁ = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show x₂ = -1 ∨ x₂ = 0 ∨ x₂ = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show y₂ = -1 ∨ y₂ = 0 ∨ y₂ = 1 by omega) with rfl | rfl | rfl <;>
    exact ⟨by first | rfl | (exfalso; omega), by omega⟩

private theorem lineSide_king (kp0 : Player → Pos) (p : Player) :
    lineSide (kp0 .sente) (kp0 .gote) (kp0 p) = 0 := by
  cases p
  · exact lineSide_left _ _
  · exact lineSide_right _ _

namespace MoveTrace

/-- The piece on `q` attacks its enemy king at state `k`. -/
def IsCheckerAt (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (q : Pos) : Prop :=
  ∃ piece : Piece, (tr.states k).board.grid q = some piece ∧
    attacksOriented (tr.states k).board piece.owner piece.pieceType q (kp k piece.owner.opponent)

/-- Before a move, a checker belongs to the side not to move. -/
private theorem checker_owner_before (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hsafe : tr.EveryMoveLeavesOwnKingSafe kp)
    (h0 : tr.InitialOpponentKingSafe kp) (i : Fin tr.len) (q : Pos) (piece : Piece)
    (hp : (tr.before i).board.grid q = some piece)
    (hatk : attacksOriented (tr.before i).board piece.owner piece.pieceType q
      (kp i.castSucc piece.owner.opponent)) :
    piece.owner = (tr.before i).turn.opponent := by
  rcases Player.eq_or_eq_opponent piece.owner (tr.before i).turn with ho | ho
  · exfalso
    apply tr.before_opponent_not_inCheck kp ht hsafe h0 i
    refine ⟨q, piece, hp, by rw [ho, Player.opponent_opponent], ?_⟩
    rw [show piece.owner.opponent = (tr.before i).turn.opponent by rw [ho]] at hatk
    exact hatk
  · exact ho

/-- A sliding attack from `C` to `K` in exact unit steps. -/
private theorem slide_exact (o : Player) (pt : PieceType) (C K : Pos)
    (sd : Dir) (hsd : sd ∈ pt.slideDirs.map (Dir.forPlayer · o))
    (n : ℕ) (hx : (Pos.dirTo C K).1 = ↑n * sd.1) (hy : (Pos.dirTo C K).2 = ↑n * sd.2) :
    sd ∈ PieceType.king.stepDirs ∧ sd ≠ (0, 0) ∧
      K.toInt = (C.toInt.1 + ↑n * sd.1, C.toInt.2 + ↑n * sd.2) := by
  have hsdK := slide_mem_king _ _ sd hsd
  have hu := (PieceType.mem_king_stepDirs_iff sd).mp hsdK
  refine ⟨hsdK, fun h => hu.2.2.2.2 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, Prod.ext ?_ ?_⟩
  · dsimp [Pos.dirTo, Pos.toInt] at hx ⊢
    omega
  · dsimp [Pos.dirTo, Pos.toInt] at hy ⊢
    omega

/-- Before each move there is at most one checking square. -/
private theorem checker_unique_before (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (C₁ C₂ : Pos)
    (h₁ : tr.IsCheckerAt kp i.castSucc C₁) (h₂ : tr.IsCheckerAt kp i.castSucc C₂) : C₁ = C₂ := by
  obtain ⟨X₁, hX₁, hatk₁⟩ := h₁
  obtain ⟨X₂, hX₂, hatk₂⟩ := h₂
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have ho₁ := checker_owner_before tr kp ht hsafe h0 i C₁ X₁ hX₁ hatk₁
  have ho₂ := checker_owner_before tr kp ht hsafe h0 i C₂ X₂ hX₂ hatk₂
  rw [show kp i.castSucc X₁.owner.opponent = kp i.castSucc (tr.before i).turn by
    rw [ho₁, Player.opponent_opponent]] at hatk₁
  rw [show kp i.castSucc X₂.owner.opponent = kp i.castSucc (tr.before i).turn by
    rw [ho₂, Player.opponent_opponent]] at hatk₂
  have hkm : kp i.succ (tr.before i).turn = kp i.castSucc (tr.before i).turn := by
    rw [hkp i.succ, hkp i.castSucc]
  have hc₁ := tr.destination_on_checker_line kp ht hs hsafe i hkm C₁ X₁ hX₁ ho₁ hatk₁
  have hc₂ := tr.destination_on_checker_line kp ht hs hsafe i hkm C₂ X₂ hX₂ ho₂ hatk₂
  obtain ⟨D, hD⟩ : ∃ D, (tr.moves i).destination = D := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = kp i.castSucc (tr.before i).turn := ⟨_, rfl⟩
  rw [hD, ← hK] at hc₁ hc₂
  rw [← hK] at hatk₁ hatk₂
  -- A checker on `D` would block the other checker's slide through `D`.
  have hblock : ∀ (Ca Cb : Pos) (Xa Xb : Piece),
      (tr.before i).board.grid Ca = some Xa →
      attacksOriented (tr.before i).board Xb.owner Xb.pieceType Cb K →
      Ca.toInt ∈ slidePath Cb K →
      Pos.dirTo Cb K ∉ Xb.pieceType.stepDirs.map (Dir.forPlayer · Xb.owner) → False := by
    intro Ca Cb Xa Xb hXa hatk hmem hns
    rcases hatk with st | ⟨_, _, _, _, _, _, _, hpc⟩
    · exact hns st
    · have h := hpc Ca.toInt hmem (Pos.onBoard_toInt _) (Pos.onBoard_toInt _)
      rw [Pos.toPos_toInt, hXa] at h
      cases h
  rcases hc₁ with h1 | ⟨m1, ns1⟩ <;> rcases hc₂ with h2 | ⟨m2, ns2⟩
  · exact h1.symm.trans h2
  · exact (hblock C₁ C₂ X₁ X₂ hX₁ hatk₂ (h1 ▸ m2) ns2).elim
  · exact (hblock C₂ C₁ X₂ X₁ hX₂ hatk₁ (h2 ▸ m1) ns1).elim
  · -- Both checks slide through `D`, hence along one ray to `K`.
    rcases hatk₁ with st | ⟨sd₁, hsd₁, hnorm₁, n₁, hn₁, hx₁, hy₁, hpc₁⟩
    · exact absurd st ns1
    rcases hatk₂ with st | ⟨sd₂, hsd₂, hnorm₂, n₂, hn₂, hx₂, hy₂, hpc₂⟩
    · exact absurd st ns2
    obtain ⟨hk₁, hd₁, e₁⟩ := slide_exact _ _ C₁ K sd₁ hsd₁ n₁ hx₁ hy₁
    obtain ⟨hk₂, hd₂, e₂⟩ := slide_exact _ _ C₂ K sd₂ hsd₂ n₂ hx₂ hy₂
    have hi₁ := mem_slidePath_iff_of_exact_steps C₁ K sd₁ n₁ hd₁ hn₁ hnorm₁
      (congrArg Prod.fst e₁) (congrArg Prod.snd e₁)
    have hi₂ := mem_slidePath_iff_of_exact_steps C₂ K sd₂ n₂ hd₂ hn₂ hnorm₂
      (congrArg Prod.fst e₂) (congrArg Prod.snd e₂)
    obtain ⟨x₁, hx₁1, hx₁n, hD₁⟩ := (hi₁ D.toInt).mp m1
    obtain ⟨x₂, hx₂1, hx₂n, hD₂⟩ := (hi₂ D.toInt).mp m2
    obtain ⟨hsd, hnx⟩ := same_ray D K sd₁ sd₂ ((n₁ : ℤ) - x₁) ((n₂ : ℤ) - x₂) hk₁ hk₂
      (by omega) (by omega)
      (by
        rw [e₁, hD₁]
        ext <;> simp only <;> ring)
      (by
        rw [e₂, hD₂]
        ext <;> simp only <;> ring)
    subst hsd
    have k1 : K.toInt.1 = C₁.toInt.1 + ↑n₁ * sd₁.1 := congrArg Prod.fst e₁
    have k2 : K.toInt.2 = C₁.toInt.2 + ↑n₁ * sd₁.2 := congrArg Prod.snd e₁
    have l1 : K.toInt.1 = C₂.toInt.1 + ↑n₂ * sd₁.1 := congrArg Prod.fst e₂
    have l2 : K.toInt.2 = C₂.toInt.2 + ↑n₂ * sd₁.2 := congrArg Prod.snd e₂
    rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
    · exfalso
      refine hblock C₁ C₂ X₁ X₂ hX₁ (Or.inr ⟨sd₁, hsd₂, hnorm₂, n₂, hn₂, hx₂, hy₂, hpc₂⟩)
        ((hi₂ C₁.toInt).mpr ⟨n₂ - n₁, by omega, by omega, ?_⟩) ns2
      rw [Nat.cast_sub hlt.le]
      ext
      · show C₁.toInt.1 = C₂.toInt.1 + (↑n₂ - ↑n₁) * sd₁.1
        rw [show (↑n₂ - ↑n₁) * sd₁.1 = ↑n₂ * sd₁.1 - ↑n₁ * sd₁.1 by ring]
        linarith
      · show C₁.toInt.2 = C₂.toInt.2 + (↑n₂ - ↑n₁) * sd₁.2
        rw [show (↑n₂ - ↑n₁) * sd₁.2 = ↑n₂ * sd₁.2 - ↑n₁ * sd₁.2 by ring]
        linarith
    · subst heq
      apply pos_eq_of_toInt
      ext
      · show C₁.toInt.1 = C₂.toInt.1
        linarith
      · show C₁.toInt.2 = C₂.toInt.2
        linarith
    · exfalso
      refine hblock C₂ C₁ X₂ X₁ hX₂ (Or.inr ⟨sd₁, hsd₁, hnorm₁, n₁, hn₁, hx₁, hy₁, hpc₁⟩)
        ((hi₁ C₂.toInt).mpr ⟨n₁ - n₂, by omega, by omega, ?_⟩) ns1
      rw [Nat.cast_sub hgt.le]
      ext
      · show C₂.toInt.1 = C₁.toInt.1 + (↑n₁ - ↑n₂) * sd₁.1
        rw [show (↑n₁ - ↑n₂) * sd₁.1 = ↑n₁ * sd₁.1 - ↑n₂ * sd₁.1 by ring]
        linarith
      · show C₂.toInt.2 = C₁.toInt.2 + (↑n₁ - ↑n₂) * sd₁.2
        rw [show (↑n₁ - ↑n₂) * sd₁.2 = ↑n₁ * sd₁.2 - ↑n₂ * sd₁.2 by ring]
        linarith

/-- No double check: in a periodic trace of at least one move satisfying 's
    premises, every state has at most one checking square. A single reply cannot
    lift checks along two lines to a king that never moves, and two checks along
    one ray would block each other. -/
theorem checker_unique_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (hlen : 0 < tr.len) (k : Fin (tr.len + 1)) (C₁ C₂ : Pos)
    (h₁ : tr.IsCheckerAt kp k C₁) (h₂ : tr.IsCheckerAt kp k C₂) : C₁ = C₂ := by
  by_cases hkl : k.val < tr.len
  · let i : Fin tr.len := ⟨k.val, hkl⟩
    have hki : k = i.castSucc := Fin.ext rfl
    rw [hki] at h₁ h₂
    exact checker_unique_before tr kp ht hs hk hsafe h0 hc hr hp i C₁ C₂ h₁ h₂
  · have hkl' : k = Fin.last tr.len := Fin.ext (by have := k.isLt; simp only [Fin.val_last]; omega)
    subst hkl'
    have hperiod : tr.states (Fin.last tr.len) = tr.states 0 := hp
    have hkpl := hp.kingPos_last hk
    have transfer : ∀ q, tr.IsCheckerAt kp (Fin.last tr.len) q →
        tr.IsCheckerAt kp (⟨0, hlen⟩ : Fin tr.len).castSucc q := by
      rintro q ⟨piece, hpq, hatk⟩
      refine ⟨piece, ?_, ?_⟩
      · change (tr.states 0).board.grid q = some piece
        rw [← hperiod]
        exact hpq
      · change attacksOriented (tr.states 0).board piece.owner piece.pieceType q
          (kp 0 piece.owner.opponent)
        rw [← hperiod, ← hkpl]
        exact hatk
    exact checker_unique_before tr kp ht hs hk hsafe h0 hc hr hp ⟨0, hlen⟩ C₁ C₂
      (transfer C₁ h₁) (transfer C₂ h₂)

/-- A reply lands on the side of the line where the checker stands. -/
theorem destination_side_of_checker (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (C : Pos) (h : tr.IsCheckerAt kp i.castSucc C)
    (s : ℤ) :
    0 < s * lineSide (kp 0 .sente) (kp 0 .gote) (tr.moves i).destination ↔
      0 < s * lineSide (kp 0 .sente) (kp 0 .gote) C := by
  obtain ⟨X, hX, hatk⟩ := h
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have ho := checker_owner_before tr kp ht hsafe h0 i C X hX hatk
  rw [show kp i.castSucc X.owner.opponent = kp i.castSucc (tr.before i).turn by
    rw [ho, Player.opponent_opponent]] at hatk
  have hcor := tr.destination_on_checker_line kp ht hs hsafe i
    (by rw [hkp i.succ, hkp i.castSucc]) C X hX ho hatk
  rcases hcor with hDC | ⟨hmem, hns⟩
  · rw [hDC]
  · rcases hatk with st | ⟨sd, hsd, hnorm, n, hn, hx, hy, _⟩
    · exact absurd st hns
    obtain ⟨_, hd0, e⟩ := slide_exact _ _ C _ sd hsd n hx hy
    obtain ⟨x, hx1, hxn, hDx⟩ := (mem_slidePath_iff_of_exact_steps C _ sd n hd0 hn hnorm
      (congrArg Prod.fst e) (congrArg Prod.snd e) _).mp hmem
    refine lineSide_pos_iff_of_between _ _ C _ _ sd x n s hDx e ?_ (by omega) (by omega)
    rw [hkp i.castSucc]
    exact lineSide_king (kp 0) _

/-- The checker of a discovered check lies on the side of the moved piece's source,
    and it is a checker after the move. -/
theorem unblockedChecker_side_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hu : hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)) :
    ∃ B : Pos, tr.IsCheckerAt kp i.succ B ∧
      ∀ s : ℤ, 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) B ↔
        0 < s * lineSide (kp 0 .sente) (kp 0 .gote) src := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  rw [hm] at hu
  obtain ⟨B, Q, _, _, hQ0, hQ1, hQo, hatk, hmem, _, _, _⟩ := hu
  have hQt : Q.owner.opponent = (tr.before i).turn.opponent := by
    rw [hQo, Player.opponent_opponent]
  refine ⟨B, ⟨Q, hQ1, by rw [hQt]; exact hatk⟩, fun s => ?_⟩
  rcases hatk with st | ⟨sd, hsd, hnorm, n, hn, hx, hy, _⟩
  · -- A step attack ignores the board, so the opponent was already in check.
    exfalso
    apply tr.before_opponent_not_inCheck kp ht hsafe h0 i
    refine ⟨B, Q, hQ0, hQo, Or.inl ?_⟩
    rw [hkp i.castSucc, ← hkp i.succ]
    exact st
  obtain ⟨_, hd0, e⟩ := slide_exact _ _ B _ sd hsd n hx hy
  obtain ⟨j, hj1, hjn, hsrc⟩ := (mem_slidePath_iff_of_exact_steps B _ sd n hd0 hn hnorm
    (congrArg Prod.fst e) (congrArg Prod.snd e) _).mp hmem
  refine (lineSide_pos_iff_of_between _ _ B src _ sd j n s hsrc e ?_ (by omega) (by omega)).symm
  rw [hkp i.succ]
  exact lineSide_king (kp 0) _

/-- Proposition 3.6 in half-plane terms: a checker never stands on the line through
    both kings. -/
theorem lineSide_ne_zero_of_checker (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (hde : tr.DropDestinationsEmpty) (hlen : 0 < tr.len)
    (k : Fin (tr.len + 1)) (C : Pos) (h : tr.IsCheckerAt kp k C) :
    lineSide (kp 0 .sente) (kp 0 .gote) C ≠ 0 := by
  intro h0'
  obtain ⟨piece, hpc, hatk⟩ := h
  exact tr.checker_off_kingLine_of_periodic kp ht hs hk hsafe h0 hc hr hp hde hlen k C
    ⟨piece, hpc, hatk, (lineSide_eq_zero_iff_collinear _ _ _).mp h0'⟩

end MoveTrace
end MPC
