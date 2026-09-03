"""Emit Lean chunk files + assembly for a pq_cert JSON (SPEC Bootstrap2 §6).

usage: python3 emit_chunks.py pq_cert.json <outdir> [chunk_size]
Writes ChunkNNN.lean files and CertData2.lean (assembly) into <outdir>.
"""
import json, sys, os

src = sys.argv[1]; outdir = sys.argv[2]
CH = int(sys.argv[3]) if len(sys.argv) > 3 else 256
c = json.load(open(src))
nodes = [[int(x) for x in n] for n in c['nodes']]
X = [int(x) for x in c['X']]; Y = [int(y) for y in c['Y']]
wa = c['wa']; wb = c['wb']
N = len(X)
os.makedirs(outdir, exist_ok=True)

def node_lit(n):
    return f"⟨{n[0]}, {n[1]}, {n[2]}, {n[3]}⟩"

def cell_lit(j):
    return (f"⟨{node_lit(nodes[j])}, {node_lit(nodes[j+1])}, {X[j]}, {Y[j]}, "
            f"{node_lit(nodes[wa[j]])}, {node_lit(nodes[wb[j]])}⟩")

nchunks = (N + CH - 1) // CH
names = []
for ci in range(nchunks):
    lo, hi = ci * CH, min((ci + 1) * CH, N)
    name = f"chunk{ci+1:03d}"
    names.append(name)
    cells = ",\n  ".join(cell_lit(j) for j in range(lo, hi))
    body = f"""import RamseyLean.Bootstrap2.Check

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

namespace RamseyLean.Bootstrap2.CertData2

def {name} : List Cell := [
  {cells}]

theorem {name}_ok : {name}.all checkCellFast = true := by decide +kernel

end RamseyLean.Bootstrap2.CertData2
"""
    open(os.path.join(outdir, f"Chunk{ci+1:03d}.lean"), "w").write(body)

imports = "\n".join(f"import RamseyLean.Bootstrap2.CertData2.Chunk{i+1:03d}"
                    for i in range(nchunks))
appends = names[-1]
for nm in reversed(names[:-1]):
    appends = f"{nm} ++ ({appends})"
# stepwise all_append fold
oksteps = []
suffix_ok_prev = f"{names[-1]}_ok"
oksteps.append(f"  have h{nchunks} : ({names[-1]}).all checkCellFast = true := {names[-1]}_ok")
expr = names[-1]
for i in range(nchunks - 2, -1, -1):
    new_expr = f"{names[i]} ++ ({expr})"
    oksteps.append(
        f"  have h{i+1} : ({new_expr}).all checkCellFast = true := by\n"
        f"    rw [List.all_append, {names[i]}_ok, h{i+2}]; rfl")
    expr = new_expr
assembly = f"""{imports}

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

namespace RamseyLean.Bootstrap2.CertData2

def allCells : List Cell := {appends}

theorem allCells_ok : allCells.all checkCellFast = true := by
{chr(10).join(oksteps)}
  exact h1

end RamseyLean.Bootstrap2.CertData2
"""
open(os.path.join(outdir, "CertData2.lean"), "w").write(assembly)
print(f"emitted {nchunks} chunks of ≤{CH} cells + CertData2.lean to {outdir}")
print(f"N={N}, F_N={nodes[-1][1]}")
