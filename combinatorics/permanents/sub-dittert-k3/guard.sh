#!/bin/sh
# Run a compute job under HARD resource caps.  Use this for every solve.
#
# On 2026-07-28 an unguarded interior-point solve took 61 GB of RAM plus 20 GB of
# swap and crashed the machine.  `ulimit -v` would not have prevented that: it
# caps address space, but the kernel will still swap, and swap thrashing is what
# kills the box.  A cgroup limit with MemorySwapMax=0 makes the kernel kill the
# job instead -- noisy, local, recoverable.
#
#   GUARD_MEM=8G GUARD_CPUS=400% ./guard.sh python3 dittert/run.py 5
#
# Defaults are deliberately modest: this machine has other work on it.

MEM=${GUARD_MEM:-8G}
CPUS=${GUARD_CPUS:-400%}
THREADS=${GUARD_THREADS:-4}

export OMP_NUM_THREADS="$THREADS"
export OPENBLAS_NUM_THREADS="$THREADS"
export MKL_NUM_THREADS="$THREADS"
export NUMEXPR_NUM_THREADS="$THREADS"
export VECLIB_MAXIMUM_THREADS="$THREADS"

echo "[guard] MemoryMax=$MEM  swap=off  CPUQuota=$CPUS  threads=$THREADS" >&2

# Per-job caps are NOT enough on their own.  With several agents running, N jobs
# each obeying a 1-core cap still add up to N cores.  So every job also joins one
# shared slice, mathsguard.slice, which carries an AGGREGATE ceiling (see
# ~/.config/systemd/user/mathsguard.slice: CPUQuota=1000% of 2400%, MemoryMax=18G
# of 61G, swap off).  However many jobs start, the total cannot exceed that.
exec systemd-run --user --scope --quiet \
    --slice=mathsguard.slice \
    -p MemoryMax="$MEM" \
    -p MemorySwapMax=0 \
    -p CPUQuota="$CPUS" \
    nice -n 15 "$@"
