# GAP Invariant Comparison: B3(3) vs C3(3)

## Groups Analyzed
- **B3(3) = Omega(7,3)** (character table identifier: "O7(3)")
- **C3(3) = PSp(6,3)** (character table identifier: "S6(3)")

Both groups have **order 4585351680** and share many structural properties, making them candidate D-ring-separating data.

---

## Summary: SIGNIFICANT DIFFERENCES FOUND

The two groups are **NOT conjugacy-equivalent** from a character-theoretic perspective. They differ on **every major invariant tested**.

---

## Detailed Results

### Task 1: Order Verification
| Invariant | Value |
|-----------|-------|
| Size(O7(3)) | 4585351680 |
| Size(S6(3)) | 4585351680 |
| **Status** | ✓ **SAME** |

---

### Task 2: Number of Conjugacy Classes
| Group | Count |
|-------|-------|
| O7(3) | 58 |
| S6(3) | 74 |
| **Status** | ✗ **DIFFERENT** (Δ = 16 classes) |

---

### Task 3: Element-Order Spectra
| Group | Orders |
|-------|--------|
| O7(3) | [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 18, 20] |
| S6(3) | [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 18, 20, **24, 30, 36**] |
| **Status** | ✗ **DIFFERENT** |

**Note:** S6(3) contains elements of orders 24, 30, 36 not found in O7(3).

---

### Task 4: INVOLUTION COUNT (CRITICAL)
| Group | Count |
|-------|-------|
| O7(3) | **354,159** |
| S6(3) | **196,911** |
| **Status** | ✗ **DIFFERENT** (Δ = 157,248 involutions; ~78% more in O7(3)) |

**Significance:** This is a major discrepancy. The involution count is an important structural invariant. O7(3) has significantly more elements of order 2.

---

### Task 5: Conjugacy Classes and Element Counts by Order

**O7(3):**
```
order | #classes | #elements
------|----------|----------
    1 |        1 | 1
    2 |        3 | 354159         ← O7(3) has 3 involution classes
    3 |        7 | 5307848
    4 |        4 | 41395536       ← Differs from S6(3)
    5 |        1 | 38211264
    6 |       16 | 275871960      ← Differs from S6(3)
    7 |        1 | 327525120
    8 |        2 | 573168960      ← Differs from S6(3)
    9 |        4 | 382112640      ← Differs from S6(3)
   10 |        2 | 343901376      ← Differs from S6(3)
   12 |        8 | 732382560      ← Differs from S6(3)
   13 |        2 | 705438720
   14 |        1 | 327525120
   15 |        1 | 305690112
   18 |        4 | 297198720
   20 |        1 | 229267584
```

**S6(3):**
```
order | #classes | #elements
------|----------|----------
    1 |        1 | 1
    2 |        2 | 196911         ← S6(3) has 2 involution classes
    3 |        7 | 5307848
    4 |        3 | 6014736        ← Differs from O7(3)
    5 |        1 | 38211264
    6 |       16 | 191115288      ← Differs from O7(3)
    7 |        1 | 327525120
    8 |        2 | 191056320      ← Differs from O7(3)
    9 |        8 | 382112640      ← Differs from O7(3)
   10 |        1 | 38211264       ← Differs from O7(3)
   12 |       14 | 513021600      ← Differs from O7(3)
   13 |        2 | 705438720
   14 |        1 | 327525120
   15 |        2 | 305690112      ← Differs from O7(3)
   18 |        6 | 382112640      ← Differs from O7(3)
   20 |        1 | 229267584
   24 |        2 | 382112640      ← Only in S6(3)
   30 |        2 | 305690112      ← Only in S6(3)
   36 |        2 | 254741760      ← Only in S6(3)
```

**Differences at orders:** 2, 4, 6, 8, 9, 10, 12, 15, 18 (plus new orders 24, 30, 36 in S6(3)).

**Status:** ✗ **DIFFERENT**

---

### Task 6: Rational-Class / Cyclic Subgroup Orbits

| Aspect | O7(3) | S6(3) |
|--------|-------|-------|
| Number of orbits | 56 | 49 |
| Orbit-size multiset | Mostly 1s, with two 2s: `[1,1,...,1,2,1,1,2,1,1,1]` | Many 2s: `[1,1,1,2,1,1,2,1,1,1,1,1,2,2,2,2,...]` |
| **Status** | ✗ **DIFFERENT** | |

**Significance:** This indicates different cyclic subgroup structures. S6(3) has more elements that are related by power maps with exponents coprime to their order, while O7(3) tends to have isolated rational classes.

---

### Task 7: Frobenius-Schur Indicators (2nd kind)

| Group | Indicator distribution |
|-------|------------------------|
| O7(3) | Mostly 1s (56 out of 58): two 0s in positions indicating orthogonal/pseudo-real characters |
| S6(3) | Many 0s (roughly half): complex characters significantly more prevalent |
| **Status** | ✗ **DIFFERENT** |

**Significance:** The Frobenius-Schur indicator determines whether irreducible complex representations are real (1), orthogonal (1), or complex (0). O7(3) has predominantly real representations, while S6(3) has a significantly higher proportion of non-real representations.

---

### Task 7: Character Degrees

| Aspect | O7(3) | S6(3) |
|--------|-------|-------|
| Total irreducible characters | 58 | 74 |
| Smallest degrees | 1, 78, 91, 105, 168, 182, 195, 260, 260, 273 | 1, 13, 13, 78, 91, 91, 105, 168, 195, 273 |
| **Status** | ✗ **DIFFERENT** | |

**Significance:** The character degree sets are completely different, with S6(3) having characters of degree 13 (multiplicity 2) not present in O7(3).

---

### Bonus Task 8: q=5 Case (O7(5) vs S6(5))

| Invariant | O7(5) | S6(5) | Status |
|-----------|-------|-------|--------|
| Order | 228,501,000,000,000 | 228,501,000,000,000 | ✓ Same |
| Conjugacy classes | 144 | 179 | ✗ **DIFFERENT** (Δ = 35) |
| Involution count | 138,345,375 | 153,969,375 | ✗ **DIFFERENT** (Δ = 15,624,000) |

**Significance:** The q=5 case shows the same pattern: these groups are consistently distinct across prime powers.

---

## Conclusion

### D-Ring Separating Data: YES

These two special groups B3(3) and C3(3), despite sharing:
- The same order (4585351680)
- Same element orders (mostly, with S6(3) having additional orders)

**DO NOT match** on any of the following invariants computable from the character table:
1. ✗ Number of conjugacy classes
2. ✗ Element-order spectra (S6(3) has elements of order 24, 30, 36)
3. ✗ **Involution count** (CRITICAL: 354,159 vs 196,911)
4. ✗ Conjugacy class structures by element order
5. ✗ Rational-class orbit structures
6. ✗ Frobenius-Schur indicator distributions
7. ✗ Character degree spectra

### Key Discriminants (in order of importance):

1. **Involution Count:** O7(3) has ~80% more involutions than S6(3)
2. **Element Order 24, 30, 36:** Present only in S6(3)
3. **Number of Conjugacy Classes:** O7(3) has 58, S6(3) has 74
4. **Character Degrees:** S6(3) has degree-13 characters; O7(3) does not
5. **Frobenius-Schur Indicators:** O7(3) is predominantly real; S6(3) has many complex characters

### Recommendation:

These groups are **strong candidates for D-ring-separating data** in the degree 3 case. The involution count difference alone is a powerful discriminant, supported by differences in conjugacy class structures and character representations.

The q=5 case (B3(5) vs C3(5)) exhibits the same pattern, suggesting this is a systematic feature of these type-B and type-C pairs.
