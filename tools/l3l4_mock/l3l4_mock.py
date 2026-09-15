#!/usr/bin/env python3
"""l3l4_mock.py -- dependency-free mock of mac-consistency-runtime's L3 and L4
measurement drivers, transcribed line for line from src/l3_sequencer.rs and
src/l4_registry.rs, so their generators can be examined without cargo.

The question: is the reported baseline `1000/1000` a measurement or a
construction?
"""
M64 = (1 << 64) - 1


class XorShift:
    """src/l3_sequencer.rs lines 1-18, exactly."""
    def __init__(self, seed):
        self.s = max(seed, 1) & M64

    def next(self):
        x = self.s
        x ^= x >> 12
        x &= M64
        x ^= (x << 25) & M64
        x &= M64
        x ^= x >> 27
        x &= M64
        self.s = x
        return (x * 0x2545F4914F6CDD1D) & M64

    def below(self, n):
        return self.next() % max(n, 1)


# --------------------------------------------------------------------- L3
def a6_witness(io, co):
    return len(io) >= 2 and len(io) == len(co) and io != co


def l3_run_once(w, mode, rng, reject_identity=True):
    """Mode: 'unsequenced' | 'sequenced'."""
    sched = list(range(w))
    while True:
        for k in range(w - 1, 0, -1):
            j = rng.below(k + 1)
            sched[k], sched[j] = sched[j], sched[k]
        if not reject_identity:
            break
        if any(v != p for p, v in enumerate(sched)):
            break
    if mode == "unsequenced":
        return sched
    completed = [False] * w
    emitted = []
    nxt = 0
    for i in sched:
        completed[i] = True
        while nxt < w and completed[nxt]:
            emitted.append(nxt)
            nxt += 1
    return emitted


def l3_experiment(runs, width, mode, seed, reject_identity=True):
    rng = XorShift(seed)
    io = list(range(width))
    pos = 0
    for _ in range(runs):
        co = l3_run_once(width, mode, rng, reject_identity)
        assert len(co) == width
        if a6_witness(io, co):
            pos += 1
    return pos


# --------------------------------------------------------------------- L4
def l4_run_once(w, mode, rng, force_pinned_churn=True):
    """src/l4_registry.rs run_once, transcribed LITERALLY including the
    snapshot vector, so the guarded branch is not simplified by hand."""
    registry = [rng.next() for _ in range(w)]
    t = rng.below(w)
    snapshot = list(registry)               # registry.clone()
    pinned_sig = snapshot[t]
    churn = 1 + rng.below(w)
    for _ in range(churn):
        victim = rng.below(w)
        registry[victim] ^= 1 + rng.below((1 << 64) - 1)
        registry[victim] &= M64
    if force_pinned_churn:
        registry[t] = (pinned_sig ^ (1 + rng.below(0xFFFF_FFFF))) & M64
    dispatched = snapshot[t] if mode == "snapshot" else registry[t]
    return pinned_sig, dispatched


def l4_experiment(runs, width, mode, seed, force_pinned_churn=True):
    rng = XorShift(seed)
    pos = 0
    for _ in range(runs):
        pinned, dispatched = l4_run_once(width, mode, rng, force_pinned_churn)
        if pinned != dispatched:
            pos += 1
    return pos


def main():
    RUNS = 1000
    print("L3 (A6): baseline is 'Unsequenced'. The shipped run_once rejects the")
    print("         identity permutation in a loop before returning.\n")
    print(f"  {'width':>6} {'shipped base':>13} {'shipped L3':>11} "
          f"{'base w/o rejection':>19} {'P(identity)=1/w!':>17}")
    import math
    for w in (2, 4, 8):
        b = l3_experiment(RUNS, w, "unsequenced", 0xC0FFEE + w)
        g = l3_experiment(RUNS, w, "sequenced", 0xC0FFEE + w)
        b2 = l3_experiment(RUNS, w, "unsequenced", 0xC0FFEE + w,
                           reject_identity=False)
        print(f"  {w:6d} {b:>7}/{RUNS} {g:>6}/{RUNS} {b2:>13}/{RUNS} "
              f"{1/math.factorial(w):>17.5f}")

    print("\n  seed-independence of the shipped baseline:")
    seeds = [1, 7, 42, 1234, 0xC0FFEE, 2**40 + 9]
    for w in (2, 4, 8):
        vals = {l3_experiment(200, w, "unsequenced", s) for s in seeds}
        print(f"    width {w}: baseline over {len(seeds)} seeds -> {sorted(vals)}"
              f"  (200 runs each)")

    print("\nL4 (A2): baseline is 'Unpinned'. The shipped run_once XORs the")
    print("         pinned slot with a nonzero value AFTER the churn loop.\n")
    print(f"  {'width':>6} {'shipped base':>13} {'shipped L4':>11} "
          f"{'base w/o forced churn':>22}")
    for w in (2, 4, 8):
        b = l4_experiment(RUNS, w, "unpinned", 7 + w)
        g = l4_experiment(RUNS, w, "snapshot", 7 + w)
        b2 = l4_experiment(RUNS, w, "unpinned", 7 + w, force_pinned_churn=False)
        print(f"  {w:6d} {b:>7}/{RUNS} {g:>6}/{RUNS} {b2:>16}/{RUNS}")

    print("\n  seed-independence of the shipped baseline:")
    for w in (2, 4, 8):
        vals = {l4_experiment(200, w, "unpinned", s) for s in seeds}
        print(f"    width {w}: baseline over {len(seeds)} seeds -> {sorted(vals)}"
              f"  (200 runs each)")


if __name__ == "__main__":
    main()
