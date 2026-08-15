# cyclic_faithful_check_deep.py
# Task B follow-up: retry D8 and C2xC4 with a much larger node cap
# (default 2e6 capped out; results there were only lower bounds).

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0] + "/../lib")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from dring2 import cyclic, dihedral
from swaprigid import direct_product
from cyclic_faithful_check import check_group

CAP = 10**8

check_group("D8", lambda: dihedral(4), node_cap=CAP)
check_group("C2xC4", lambda: direct_product(cyclic(2), cyclic(4), "C2xC4"),
            node_cap=CAP)
