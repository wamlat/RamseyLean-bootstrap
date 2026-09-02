#!/bin/bash
# Memory-capped chunk build: at most K concurrent kernel jobs (each needs
# ~3.4 GB baseline + ~40 MB/cell; lake has no jobs cap in this version, so
# we pass exactly K leaf targets per invocation).
set -uo pipefail
cd "$(dirname "$0")"
K=${K:-3}
echo "batch build, K=$K, start $(date '+%H:%M:%S')"
lake build RamseyLean.Bootstrap.CertCheck 2>&1 | tail -1
mods=$(ls RamseyLean/Bootstrap/CertData/Chunk*.lean | sed 's|\.lean$||; s|/|.|g')
total=$(echo "$mods" | wc -l | tr -d ' ')
i=0
echo "$mods" | xargs -n "$K" | while read -r group; do
  i=$((i + K))
  lake build $group >/dev/null 2>&1 || { echo "FAILED in group: $group"; exit 1; }
  echo "[$(date '+%H:%M:%S')] built ~$i / $total"
done || exit 1
echo "chunks done $(date '+%H:%M:%S'); building final target"
lake build RamseyLean.Bootstrap.Main 2>&1 | grep -vE '^info:' | tail -5
printf 'import RamseyLean.Bootstrap.Main\n#print axioms RamseyLean.Bootstrap.main_bootstrap\n#print axioms RamseyLean.Bootstrap.bootstrap_diagonal\n' > /tmp/ax_final.lean
lake env lean /tmp/ax_final.lean
echo "==== VERIFICATION COMPLETE $(date '+%H:%M:%S') ===="
