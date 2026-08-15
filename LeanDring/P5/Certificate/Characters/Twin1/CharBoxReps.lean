/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharBox

/-!
# Row-combination completeness certificates for the `k ≥ 4` representatives

One application of `charsAtComplete_of_cert` per representative `116 … 147`
(`k = 4`, plus the whole group `147`, `k = 5`). Each is a handful of small kernel
`decide`s over the embedded `ZMod 25` linear system — no `25^k` enumeration.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-- **Completeness for representative 116** (`k = 4`). -/
theorem charsAtComplete_116 : CharsAtComplete ⟨116, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨116, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 24, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 117** (`k = 4`). -/
theorem charsAtComplete_117 : CharsAtComplete ⟨117, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨117, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 9, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 118** (`k = 4`). -/
theorem charsAtComplete_118 : CharsAtComplete ⟨118, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨118, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 14, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 119** (`k = 4`). -/
theorem charsAtComplete_119 : CharsAtComplete ⟨119, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨119, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 13, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 120** (`k = 4`). -/
theorem charsAtComplete_120 : CharsAtComplete ⟨120, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨120, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 24, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 121** (`k = 4`). -/
theorem charsAtComplete_121 : CharsAtComplete ⟨121, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨121, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 122** (`k = 4`). -/
theorem charsAtComplete_122 : CharsAtComplete ⟨122, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨122, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 123** (`k = 4`). -/
theorem charsAtComplete_123 : CharsAtComplete ⟨123, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨123, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 124** (`k = 4`). -/
theorem charsAtComplete_124 : CharsAtComplete ⟨124, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨124, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 125** (`k = 4`). -/
theorem charsAtComplete_125 : CharsAtComplete ⟨125, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨125, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 126** (`k = 4`). -/
theorem charsAtComplete_126 : CharsAtComplete ⟨126, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨126, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 17, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 127** (`k = 4`). -/
theorem charsAtComplete_127 : CharsAtComplete ⟨127, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨127, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 17, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 128** (`k = 4`). -/
theorem charsAtComplete_128 : CharsAtComplete ⟨128, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨128, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 17, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 129** (`k = 4`). -/
theorem charsAtComplete_129 : CharsAtComplete ⟨129, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨129, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 17, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 130** (`k = 4`). -/
theorem charsAtComplete_130 : CharsAtComplete ⟨130, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨130, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 17, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 131** (`k = 4`). -/
theorem charsAtComplete_131 : CharsAtComplete ⟨131, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨131, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 132** (`k = 4`). -/
theorem charsAtComplete_132 : CharsAtComplete ⟨132, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨132, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 133** (`k = 4`). -/
theorem charsAtComplete_133 : CharsAtComplete ⟨133, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨133, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 134** (`k = 4`). -/
theorem charsAtComplete_134 : CharsAtComplete ⟨134, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨134, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 135** (`k = 4`). -/
theorem charsAtComplete_135 : CharsAtComplete ⟨135, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨135, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 6, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 136** (`k = 4`). -/
theorem charsAtComplete_136 : CharsAtComplete ⟨136, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨136, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 137** (`k = 4`). -/
theorem charsAtComplete_137 : CharsAtComplete ⟨137, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨137, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 138** (`k = 4`). -/
theorem charsAtComplete_138 : CharsAtComplete ⟨138, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨138, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 139** (`k = 4`). -/
theorem charsAtComplete_139 : CharsAtComplete ⟨139, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨139, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 140** (`k = 4`). -/
theorem charsAtComplete_140 : CharsAtComplete ⟨140, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨140, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 3, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 141** (`k = 4`). -/
theorem charsAtComplete_141 : CharsAtComplete ⟨141, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨141, by norm_num⟩ [5, 5, 5, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 142** (`k = 4`). -/
theorem charsAtComplete_142 : CharsAtComplete ⟨142, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨142, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 14, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 143** (`k = 4`). -/
theorem charsAtComplete_143 : CharsAtComplete ⟨143, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨143, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 14, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 144** (`k = 4`). -/
theorem charsAtComplete_144 : CharsAtComplete ⟨144, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨144, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 14, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 145** (`k = 4`). -/
theorem charsAtComplete_145 : CharsAtComplete ⟨145, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨145, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 14, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 146** (`k = 4`). -/
theorem charsAtComplete_146 : CharsAtComplete ⟨146, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨146, by norm_num⟩ [5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 24, 0, 0, 0, 0], [0, 0, 0, 0, 19, 14, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Completeness for representative 147** (`k = 5`). -/
theorem charsAtComplete_147 : CharsAtComplete ⟨147, by norm_num⟩ :=
  charsAtComplete_of_cert ⟨147, by norm_num⟩ [5, 5, 5, 1, 1]
    [[4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 19, 0, 14, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end LeanDring.P5Presentation
