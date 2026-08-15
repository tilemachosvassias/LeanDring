# Task 11: Perfect Maximal Subgroup Comparison Report
## O7(q) vs S6(q) Extended q-Sweep

**Date:** 2026-08-05  
**Purpose:** Extend perfect-maximal-subgroup comparison from q=3 to q ∈ {5,7,9,11,13,17,19,23,25,27}

---

## Summary Table

| q | O7 maxes | O7 perfect | O7 unknown | S6 maxes | S6 perfect | S6 unknown | Verdict |
|---|----------|-----------|-----------|----------|-----------|-----------|---------|
| 3 | 15 | 6 | 0 | 11 | 5 | 0 | **DIFFER** |
| 5 | — | — | — | — | — | — | NO_MAXES |
| 7 | — | — | — | — | — | — | NO_TABLE |
| 9 | — | — | — | — | — | — | NO_TABLE |
| 11 | — | — | — | — | — | — | NO_TABLE |
| 13 | — | — | — | — | — | — | NO_TABLE |
| 17 | — | — | — | — | — | — | NO_TABLE |
| 19 | — | — | — | — | — | — | NO_TABLE |
| 23 | — | — | — | — | — | — | NO_TABLE |
| 25 | — | — | — | — | — | — | NO_TABLE |
| 27 | — | — | — | — | — | — | NO_TABLE |

---

## Results

### Sanity Check: q=3
✓ **Verified as expected.**
- **O7(3)**: 15 maximal classes, 6 perfect, 0 unknown
- **S6(3)**: 11 maximal classes, 5 perfect, 0 unknown
- **Status**: Data consistent with baseline (DIFFER confirmed: different numbers of maxes and perfect maximal subgroups)

### q=5
- **Status**: Character tables exist, but GAP's ctbllib does not provide Maxes data (maximal subgroup lists)
- **O7(5)**: table exists, no Maxes data
- **S6(5)**: table exists, no Maxes data
- **Conclusion**: Cannot analyze perfect maximal subgroups

### q ∈ {7, 9, 11, 13, 17, 19, 23, 25, 27}
- **Status**: No character tables in GAP's ctbllib for any of these q values
- **O7(q)**: NO_TABLE for all q
- **S6(q)**: NO_TABLE for all q
- **Conclusion**: Extension beyond q=5 not possible with current library

---

## Key Findings

1. **Sanity anchor confirmed**: q=3 data matches expected baseline (15 vs 11 maxes; 6 vs 5 perfect).

2. **Limited data availability**:
   - Only q=3 has complete Maxes data in GAP's character table library
   - q=5 has tables but no maximal subgroup lists
   - q ≥ 7: No character tables available

3. **Frontier accessibility**: The extension is blocked by library limitations, not computational infeasibility. The q-sweep cannot proceed beyond q=5 without additional external character table resources or direct group construction.

---

## Raw Data Source

- Script: `v_task11_qsweep.g`
- Output: `v_task11_out.txt`
- Package used: GAP 4.16.0, ctbllib (character table library)
- Perfect criterion: maximal subgroup M has exactly 1 linear character (iff M is perfect/semisimple)

---

## Conclusion

The comparison extends only to q=5 with available GAP data. For q ≥ 7, character tables are not in the ctbllib and would need to be sourced externally or computed directly from group definitions. No new structural differences can be documented beyond q=3.
