# Code

Most scripts import `engine.py` and `geometry.py` from this folder. Run them from here. Some search scripts expect
instance files (`inst_*.txt`), which `python3 geometry.py <W|Q+|Q-> <n>` generates. They also expect the compiled
binary `./tabu`: `gcc -O2 -o tabu tabu.c`.

| script | purpose |
|---|---|
| lean_mirror.py | **reference for the Lean checker**: bit-packed, independent; reproduces every count of GEO-1/GEO-2 (~30 s) |
| cert216_full.py | elementary certificate for deg Q-(7,2) >= 216 over all 136 choices of a |
| cert216_data.py | writes data/cert216_Qm7.json (points, lines, signs, O_a, doilies, grids) |
| engine.py, geometry.py, known.py | Pauli algebra, signs, exact degree (CP-SAT), standard geometries |
| reduction.py, induced_red.py, grid_template.py | hardness constructions (sub-configuration and induced) |
| test_*.py, tractable.py | randomised verification of the constructions against brute force |
| tabu.c, gray.c, satlb.py | heuristic upper bounds, exhaustive small degrees, SAT lower bounds |
| cascade*.py, smallorbit.py, profile_qm7.py | target C: witness / integrality-cascade searches |
| classify_qm7.py, structure_qm7.py, estruct.py | target B: classification of optimal assignments of Q-(7,2) |
| RESULTS_session_log.md | older session log (superseded by ../blueprint) |
