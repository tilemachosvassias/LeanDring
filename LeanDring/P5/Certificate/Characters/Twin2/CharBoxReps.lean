/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharBox

/-!
# The 32 q=2 row-combination completeness certificates (Step 3, `k ≥ 4`, twin q=2)

The q=2 twin of `LeanDring/P5/Certificate/Characters/Twin1/CharBoxReps.lean`: for each `k ≥ 4` representative `116 … 147`,
`charsAtComplete_of_cert2` is fed the twin-invariant box multipliers together with
the **regenerated** q=2 row-combination coefficients (recomputed by Smith-normal-form
solving over `ZMod 25` against the q=2 constraint rows `repPR2`/`repCR2`, since the
twin's fifth-power map changed the power rows). Every hypothesis is a small kernel
`decide`.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-- **Completeness for representative 116** (q=2). -/
theorem charsAtComplete2_116 : CharsAtComplete ⟨116, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨116, by norm_num⟩ [5, 5, 5, 1]
    [[19, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [5, 0, 0, 0, 4, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 117** (q=2). -/
theorem charsAtComplete2_117 : CharsAtComplete ⟨117, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨117, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 13, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 118** (q=2). -/
theorem charsAtComplete2_118 : CharsAtComplete ⟨118, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨118, by norm_num⟩ [5, 5, 5, 1]
    [[24, 0, 0, 0, 21, 4, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 24, 1, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 119** (q=2). -/
theorem charsAtComplete2_119 : CharsAtComplete ⟨119, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨119, by norm_num⟩ [5, 5, 5, 1]
    [[19, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [20, 0, 0, 0, 3, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 120** (q=2). -/
theorem charsAtComplete2_120 : CharsAtComplete ⟨120, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨120, by norm_num⟩ [5, 5, 5, 1]
    [[19, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [5, 0, 0, 0, 4, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 121** (q=2). -/
theorem charsAtComplete2_121 : CharsAtComplete ⟨121, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨121, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 122** (q=2). -/
theorem charsAtComplete2_122 : CharsAtComplete ⟨122, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨122, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 123** (q=2). -/
theorem charsAtComplete2_123 : CharsAtComplete ⟨123, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨123, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 124** (q=2). -/
theorem charsAtComplete2_124 : CharsAtComplete ⟨124, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨124, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 125** (q=2). -/
theorem charsAtComplete2_125 : CharsAtComplete ⟨125, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨125, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 126** (q=2). -/
theorem charsAtComplete2_126 : CharsAtComplete ⟨126, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨126, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 19, 0, 18, 0, 0, 0, 0], [0, 20, 18, 0, 4, 12, 0, 0, 0, 0], [0, 15, 23, 1, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 127** (q=2). -/
theorem charsAtComplete2_127 : CharsAtComplete ⟨127, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨127, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 19, 0, 18, 0, 0, 0, 0], [0, 20, 18, 0, 4, 12, 0, 0, 0, 0], [0, 15, 23, 1, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 128** (q=2). -/
theorem charsAtComplete2_128 : CharsAtComplete ⟨128, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨128, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 19, 0, 18, 0, 0, 0, 0], [0, 20, 18, 0, 4, 12, 0, 0, 0, 0], [0, 15, 23, 1, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 129** (q=2). -/
theorem charsAtComplete2_129 : CharsAtComplete ⟨129, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨129, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 19, 0, 18, 0, 0, 0, 0], [0, 20, 18, 0, 4, 12, 0, 0, 0, 0], [0, 15, 23, 1, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 130** (q=2). -/
theorem charsAtComplete2_130 : CharsAtComplete ⟨130, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨130, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 19, 0, 18, 0, 0, 0, 0], [0, 20, 18, 0, 4, 12, 0, 0, 0, 0], [0, 15, 23, 1, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 131** (q=2). -/
theorem charsAtComplete2_131 : CharsAtComplete ⟨131, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨131, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 10, 0, 0, 19, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 132** (q=2). -/
theorem charsAtComplete2_132 : CharsAtComplete ⟨132, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨132, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 10, 0, 0, 19, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 133** (q=2). -/
theorem charsAtComplete2_133 : CharsAtComplete ⟨133, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨133, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 10, 0, 0, 19, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 134** (q=2). -/
theorem charsAtComplete2_134 : CharsAtComplete ⟨134, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨134, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 10, 0, 0, 19, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 135** (q=2). -/
theorem charsAtComplete2_135 : CharsAtComplete ⟨135, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨135, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 19, 0, 0, 0, 3, 0, 0, 0, 0], [0, 10, 0, 0, 19, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 4, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 136** (q=2). -/
theorem charsAtComplete2_136 : CharsAtComplete ⟨136, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨136, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 1, 1, 20, 23, 0, 0, 0, 0], [0, 5, 1, 1, 14, 23, 0, 0, 0, 0], [0, 10, 3, 3, 10, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 137** (q=2). -/
theorem charsAtComplete2_137 : CharsAtComplete ⟨137, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨137, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 1, 1, 20, 23, 0, 0, 0, 0], [0, 5, 1, 1, 14, 23, 0, 0, 0, 0], [0, 10, 3, 3, 10, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 138** (q=2). -/
theorem charsAtComplete2_138 : CharsAtComplete ⟨138, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨138, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 1, 1, 20, 23, 0, 0, 0, 0], [0, 5, 1, 1, 14, 23, 0, 0, 0, 0], [0, 10, 3, 3, 10, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 139** (q=2). -/
theorem charsAtComplete2_139 : CharsAtComplete ⟨139, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨139, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 1, 1, 20, 23, 0, 0, 0, 0], [0, 5, 1, 1, 14, 23, 0, 0, 0, 0], [0, 10, 3, 3, 10, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 140** (q=2). -/
theorem charsAtComplete2_140 : CharsAtComplete ⟨140, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨140, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 1, 1, 20, 23, 0, 0, 0, 0], [0, 5, 1, 1, 14, 23, 0, 0, 0, 0], [0, 10, 3, 3, 10, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 141** (q=2). -/
theorem charsAtComplete2_141 : CharsAtComplete ⟨141, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨141, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 142** (q=2). -/
theorem charsAtComplete2_142 : CharsAtComplete ⟨142, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨142, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 4, 0, 18, 0, 0, 0, 0], [0, 20, 13, 16, 4, 9, 0, 0, 0, 0], [0, 0, 23, 16, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 143** (q=2). -/
theorem charsAtComplete2_143 : CharsAtComplete ⟨143, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨143, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 4, 0, 18, 0, 0, 0, 0], [0, 20, 13, 16, 4, 9, 0, 0, 0, 0], [0, 0, 23, 16, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 144** (q=2). -/
theorem charsAtComplete2_144 : CharsAtComplete ⟨144, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨144, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 4, 0, 18, 0, 0, 0, 0], [0, 20, 13, 16, 4, 9, 0, 0, 0, 0], [0, 0, 23, 16, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 145** (q=2). -/
theorem charsAtComplete2_145 : CharsAtComplete ⟨145, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨145, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 4, 0, 18, 0, 0, 0, 0], [0, 20, 13, 16, 4, 9, 0, 0, 0, 0], [0, 0, 23, 16, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 146** (q=2). -/
theorem charsAtComplete2_146 : CharsAtComplete ⟨146, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨146, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 5, 4, 0, 18, 0, 0, 0, 0], [0, 20, 13, 16, 4, 9, 0, 0, 0, 0], [0, 0, 23, 16, 10, 24, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 147** (q=2). -/
theorem charsAtComplete2_147 : CharsAtComplete ⟨147, by norm_num⟩ :=
  charsAtComplete_of_cert2 ⟨147, by norm_num⟩ [5, 5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 24, 0, 8, 20, 10, 0, 1, 0, 22, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 20, 0, 0, 5, 19, 0, 16, 0, 13, 0, 0, 0, 0, 0], [0, 0, 0, 10, 5, 0, 0, 6, 0, 13, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
end Q2

end LeanDring.P5Presentation
