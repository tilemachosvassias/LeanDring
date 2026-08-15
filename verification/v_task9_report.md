# Task 9: Maximal Subgroup Analysis of O7(3) and S6(3)

## Objective

Compare the maximal-subgroup structure of the ATLAS character tables "O7(3)" and "S6(3)" (same order 262537297024, both simple groups), specifically counting PERFECT maximal subgroups. This forms the top layer of an intrinsic D-ring invariant: the number of perfect self-normalizing subgroup classes equals the multiplicity of conductor 1.

## Methodology

For each simple group:
1. Loaded the character table via `CharacterTable(name)`
2. Retrieved the list of maximal subgroup names via `Maxes(table)`
3. For each maximal subgroup:
   - Loaded its character table
   - Computed its order via `Size(table)`
   - Determined perfectness by counting linear characters (degree-1 irreducible characters)
   - A group is **perfect** iff it has exactly 1 linear character (the trivial one)

## Results

### O7(3)

**Maximal Subgroups:** 15 classes

| Name | Order | Linear Chars | Perfect? |
|------|-------|--------------|----------|
| 2.U4(3).2_2 | 13063680 | 2 | NO |
| 3^5:U4(2):2 | 12597120 | 2 | NO |
| L4(3).2_2 | 12130560 | 2 | NO |
| **G2(3)** | 4245696 | 1 | **YES** |
| **O7(3)M5** | 4245696 | 1 | **YES** |
| **3^(3+3):L3(3)** | 4094064 | 1 | **YES** |
| **S6(2)** | 1451520 | 1 | **YES** |
| **O7(3)M8** | 1451520 | 1 | **YES** |
| O7(3)N3A | 1259712 | 2 | NO |
| A9.2 | 362880 | 2 | NO |
| O7(3)M11 | 362880 | 2 | NO |
| (2^2xU4(2)):2 | 207360 | 4 | NO |
| **2^6:A7** | 161280 | 1 | **YES** |
| S6xS4 | 17280 | 4 | NO |
| (A4x2(A4xA4).2).2 | 13824 | 4 | NO |

**Perfect Maximal Subgroups:** 6 classes
- G2(3) (order 4245696)
- O7(3)M5 (order 4245696)
- 3^(3+3):L3(3) (order 4094064)
- S6(2) (order 1451520)
- O7(3)M8 (order 1451520)
- 2^6:A7 (order 161280)

### S6(3)

**Maximal Subgroups:** 11 classes

| Name | Order | Linear Chars | Perfect? |
|------|-------|--------------|----------|
| **3^(1+4).2U4(2)** | 12597120 | 1 | **YES** |
| **3^6:L3(3)** | 4094064 | 1 | **YES** |
| 3^(3+4):2(S4xA4) | 1259712 | 6 | NO |
| 2.(A4xU4(2)) | 622080 | 3 | NO |
| 2^(2+6):3^3:S3 | 41472 | 6 | NO |
| L2(27).3 | 29484 | 3 | NO |
| 2xU3(3).2 | 24192 | 4 | NO |
| L3(3).2 | 11232 | 2 | NO |
| **L2(13)** | 1092 | 1 | **YES** |
| **L2(13)** | 1092 | 1 | **YES** |
| **A5** | 60 | 1 | **YES** |

**Perfect Maximal Subgroups:** 5 classes
- 3^(1+4).2U4(2) (order 12597120)
- 3^6:L3(3) (order 4094064)
- L2(13) (order 1092) [appears twice in the maximal list]
- L2(13) (order 1092)
- A5 (order 60)

## Summary Counts

| Statistic | O7(3) | S6(3) |
|-----------|-------|-------|
| Total maximal subgroup classes | 15 | 11 |
| Perfect maximal subgroup classes | 6 | 5 |

## Verdict

**DIFFER**

O7(3) has **6** perfect maximal subgroup classes, while S6(3) has **5** perfect maximal subgroup classes.

This difference in the count of perfect self-normalizing maximal subgroups indicates distinct structural differences in the maximal subgroup lattices of these two simple groups, despite their equal order. This contributes an observable discrepancy to the intrinsic D-ring invariant (conductor-1 multiplicity).

## Load Status

All character tables loaded successfully. No failures.
