# Data

cert216_Qm7.json contains:
- points: the 119 points of Q-(7,2) as 0/1 vectors (x1..x4, z1..z4), with q(x|z) = x.z + x1 + z1
- lines (1071 index triples) and signs
- a: the non-singular vector used, and O_a: 756 line indices
- doilies_in_O_a: the 4032 doilies (each a list of 15 line indices)
- grids: for each such doily, its 10 grids (6 line indices each)
- coverage numbers 80 (doilies in O_a) and 96 (O_a' in Q-)

Line and point indices follow code/geometry.py: points in lexicographic order of the 8-bit vectors, lines sorted.
The Lean checker generates its own data in a different (bit-packed) order. Compare counts, not indices.
