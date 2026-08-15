/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C001
import LeanDring.P5.Data.ColRestCheap.C002
import LeanDring.P5.Data.ColRestCheap.C003
import LeanDring.P5.Data.ColRestCheap.C004
import LeanDring.P5.Data.ColRestCheap.C005
import LeanDring.P5.Data.ColRestCheap.C006
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestCheap.C008
import LeanDring.P5.Data.ColRestCheap.C009
import LeanDring.P5.Data.ColRestCheap.C010
import LeanDring.P5.Data.ColRestCheap.C011
import LeanDring.P5.Data.ColRestCheap.C012
import LeanDring.P5.Data.ColRestCheap.C013
import LeanDring.P5.Data.ColRestCheap.C014
import LeanDring.P5.Data.ColRestCheap.C015
import LeanDring.P5.Data.ColRestCheap.C016
import LeanDring.P5.Data.ColRestCheap.C017
import LeanDring.P5.Data.ColRestCheap.C018
import LeanDring.P5.Data.ColRestCheap.C019
import LeanDring.P5.Data.ColRestCheap.C020
import LeanDring.P5.Data.ColRestCheap.C021
import LeanDring.P5.Data.ColRestCheap.C022
import LeanDring.P5.Data.ColRestCheap.C023
import LeanDring.P5.Data.ColRestCheap.C024
import LeanDring.P5.Data.ColRestCheap.C025
import LeanDring.P5.Data.ColRestCheap.C026
import LeanDring.P5.Data.ColRestCheap.C027
import LeanDring.P5.Data.ColRestCheap.C028
import LeanDring.P5.Data.ColRestCheap.C029
import LeanDring.P5.Data.ColRestCheap.C030
import LeanDring.P5.Data.ColRestCheap.C031
import LeanDring.P5.Data.ColRestCheap.C032
import LeanDring.P5.Data.ColRestCheap.C033
import LeanDring.P5.Data.ColRestCheap.C034
import LeanDring.P5.Data.ColRestCheap.C035
import LeanDring.P5.Data.ColRestCheap.C036
import LeanDring.P5.Data.ColRestCheap.C037
import LeanDring.P5.Data.ColRestCheap.C038
import LeanDring.P5.Data.ColRestCheap.C039
import LeanDring.P5.Data.ColRestCheap.C040
import LeanDring.P5.Data.ColRestCheap.C041
import LeanDring.P5.Data.ColRestCheap.C042
import LeanDring.P5.Data.ColRestCheap.C043
import LeanDring.P5.Data.ColRestCheap.C044
import LeanDring.P5.Data.ColRestCheap.C045
import LeanDring.P5.Data.ColRestCheap.C046
import LeanDring.P5.Data.ColRestCheap.C047
import LeanDring.P5.Data.ColRestCheap.C048
import LeanDring.P5.Data.ColRestCheap.C049
import LeanDring.P5.Data.ColRestCheap.C050
import LeanDring.P5.Data.ColRestCheap.C051
import LeanDring.P5.Data.ColRestCheap.C052
import LeanDring.P5.Data.ColRestCheap.C053
import LeanDring.P5.Data.ColRestCheap.C054
import LeanDring.P5.Data.ColRestCheap.C055
import LeanDring.P5.Data.ColRestCheap.C056
import LeanDring.P5.Data.ColRestCheap.C057
import LeanDring.P5.Data.ColRestCheap.C058
import LeanDring.P5.Data.ColRestCheap.C059
import LeanDring.P5.Data.ColRestCheap.C060
import LeanDring.P5.Data.ColRestCheap.C061
import LeanDring.P5.Data.ColRestCheap.C062
import LeanDring.P5.Data.ColRestCheap.C063
import LeanDring.P5.Data.ColRestCheap.C064
import LeanDring.P5.Data.ColRestCheap.C065
import LeanDring.P5.Data.ColRestCheap.C066
import LeanDring.P5.Data.ColRestCheap.C067
import LeanDring.P5.Data.ColRestCheap.C068
import LeanDring.P5.Data.ColRestCheap.C069
import LeanDring.P5.Data.ColRestCheap.C070
import LeanDring.P5.Data.ColRestCheap.C071
import LeanDring.P5.Data.ColRestCheap.C072
import LeanDring.P5.Data.ColRestCheap.C073
import LeanDring.P5.Data.ColRestCheap.C074
import LeanDring.P5.Data.ColRestCheap.C075
import LeanDring.P5.Data.ColRestCheap.C076
import LeanDring.P5.Data.ColRestCheap.C077
import LeanDring.P5.Data.ColRestCheap.C078
import LeanDring.P5.Data.ColRestCheap.C079
import LeanDring.P5.Data.ColRestCheap.C080
import LeanDring.P5.Data.ColRestCheap.C081
import LeanDring.P5.Data.ColRestCheap.C082
import LeanDring.P5.Data.ColRestCheap.C083
import LeanDring.P5.Data.ColRestCheap.C084
import LeanDring.P5.Data.ColRestCheap.C085
import LeanDring.P5.Data.ColRestCheap.C086
import LeanDring.P5.Data.ColRestCheap.C087
import LeanDring.P5.Data.ColRestCheap.C088
import LeanDring.P5.Data.ColRestCheap.C089
import LeanDring.P5.Data.ColRestCheap.C090
import LeanDring.P5.Data.ColRestCheap.C091
import LeanDring.P5.Data.ColRestCheap.C092
import LeanDring.P5.Data.ColRestCheap.C093
import LeanDring.P5.Data.ColRestCheap.C094
import LeanDring.P5.Data.ColRestCheap.C095
import LeanDring.P5.Data.ColRestCheap.C096
import LeanDring.P5.Data.ColRestCheap.C097
import LeanDring.P5.Data.ColRestCheap.C098
import LeanDring.P5.Data.ColRestCheap.C099
import LeanDring.P5.Data.ColRestCheap.C100
import LeanDring.P5.Data.ColRestCheap.C101
import LeanDring.P5.Data.ColRestCheap.C102
import LeanDring.P5.Data.ColRestCheap.C103
import LeanDring.P5.Data.ColRestCheap.C104
import LeanDring.P5.Data.ColRestCheap.C105
import LeanDring.P5.Data.ColRestCheap.C106
import LeanDring.P5.Data.ColRestCheap.C107
import LeanDring.P5.Data.ColRestCheap.C108
import LeanDring.P5.Data.ColRestCheap.C109
import LeanDring.P5.Data.ColRestCheap.C110
import LeanDring.P5.Data.ColRestCheap.C111
import LeanDring.P5.Data.ColRestCheap.C112
import LeanDring.P5.Data.ColRestCheap.C113
import LeanDring.P5.Data.ColRestCheap.C114
import LeanDring.P5.Data.ColRestCheap.C115
import LeanDring.P5.Data.ColRestCheap.C116
import LeanDring.P5.Data.ColRestCheap.C117
import LeanDring.P5.Data.ColRestCheap.C118
import LeanDring.P5.Data.ColRestCheap.C119
import LeanDring.P5.Data.ColRestCheap.C120
import LeanDring.P5.Data.ColRestCheap.C121
import LeanDring.P5.Data.ColRestCheap.C122
import LeanDring.P5.Data.ColRestCheap.C123
import LeanDring.P5.Data.ColRestCheap.C124
import LeanDring.P5.Data.ColRestCheap.C125
import LeanDring.P5.Data.ColRestCheap.C126
import LeanDring.P5.Data.ColRestCheap.C127
import LeanDring.P5.Data.ColRestCheap.C128
import LeanDring.P5.Data.ColRestCheap.C129
import LeanDring.P5.Data.ColRestCheap.C130
import LeanDring.P5.Data.ColRestCheap.C131
import LeanDring.P5.Data.ColRestCheap.C132
import LeanDring.P5.Data.ColRestCheap.C133
import LeanDring.P5.Data.ColRestCheap.C134
import LeanDring.P5.Data.ColRestCheap.C135
import LeanDring.P5.Data.ColRestCheap.C136
import LeanDring.P5.Data.ColRestCheap.C137
import LeanDring.P5.Data.ColRestCheap.C138
import LeanDring.P5.Data.ColRestCheap.C139
import LeanDring.P5.Data.ColRestCheap.C140
import LeanDring.P5.Data.ColRestCheap.C141
import LeanDring.P5.Data.ColRestCheap.C142
import LeanDring.P5.Data.ColRestCheap.C143
import LeanDring.P5.Data.ColRestCheap.C144
import LeanDring.P5.Data.ColRestCheap.C145
import LeanDring.P5.Data.ColRestCheap.C146
import LeanDring.P5.Data.ColRestCheap.C147
import LeanDring.P5.Data.ColRestCheap.C148
import LeanDring.P5.Data.ColRestCheap.C149
import LeanDring.P5.Data.ColRestCheap.C150
import LeanDring.P5.Data.ColRestCheap.C151
import LeanDring.P5.Data.ColRestCheap.C152
import LeanDring.P5.Data.ColRestCheap.C153
import LeanDring.P5.Data.ColRestCheap.C154
import LeanDring.P5.Data.ColRestCheap.C155
import LeanDring.P5.Data.ColRestCheap.C156
import LeanDring.P5.Data.ColRestCheap.C157
import LeanDring.P5.Data.ColRestCheap.C158
import LeanDring.P5.Data.ColRestCheap.C159
import LeanDring.P5.Data.ColRestCheap.C160
import LeanDring.P5.Data.ColRestCheap.C161
import LeanDring.P5.Data.ColRestCheap.C162
import LeanDring.P5.Data.ColRestCheap.C163
import LeanDring.P5.Data.ColRestCheap.C164
import LeanDring.P5.Data.ColRestCheap.C165
import LeanDring.P5.Data.ColRestCheap.C166
import LeanDring.P5.Data.ColRestCheap.C167
import LeanDring.P5.Data.ColRestCheap.C168
import LeanDring.P5.Data.ColRestCheap.C169
import LeanDring.P5.Data.ColRestCheap.C170
import LeanDring.P5.Data.ColRestCheap.C171
import LeanDring.P5.Data.ColRestCheap.C172
import LeanDring.P5.Data.ColRestCheap.C173
import LeanDring.P5.Data.ColRestCheap.C174
import LeanDring.P5.Data.ColRestCheap.C175
import LeanDring.P5.Data.ColRestCheap.C176
import LeanDring.P5.Data.ColRestCheap.C177
import LeanDring.P5.Data.ColRestCheap.C178
import LeanDring.P5.Data.ColRestCheap.C179
import LeanDring.P5.Data.ColRestCheap.C180
import LeanDring.P5.Data.ColRestCheap.C181
import LeanDring.P5.Data.ColRestCheap.C182
import LeanDring.P5.Data.ColRestCheap.C183
import LeanDring.P5.Data.ColRestCheap.C184
import LeanDring.P5.Data.ColRestCheap.C185
import LeanDring.P5.Data.ColRestCheap.C186
import LeanDring.P5.Data.ColRestCheap.C187
import LeanDring.P5.Data.ColRestCheap.C188
import LeanDring.P5.Data.ColRestCheap.C189
import LeanDring.P5.Data.ColRestCheap.C190
import LeanDring.P5.Data.ColRestCheap.C191
import LeanDring.P5.Data.ColRestCheap.C192
import LeanDring.P5.Data.ColRestCheap.C193
import LeanDring.P5.Data.ColRestCheap.C194
import LeanDring.P5.Data.ColRestCheap.C195
import LeanDring.P5.Data.ColRestCheap.C196
import LeanDring.P5.Data.ColRestCheap.C197

/-!
# P5 Data family: ColRestCheap (197 chunks)

# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.

This index imports all 197 chunks of the `ColRestCheap` family in
`LeanDring/P5/Data/ColRestCheap/`. Files in this family are machine-emitted
data certificates (see the per-chunk docstrings and the emitter scripts
referenced there); they are not intended to be read chunk-by-chunk and are
skippable for readers auditing the hand-written mathematics in
`LeanDring/Theory/`, `LeanDring/P4/`, and `LeanDring/P5/Certificate/`.
-/

