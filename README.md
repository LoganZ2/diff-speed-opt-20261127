# diff-speed-opt-20261127

[![make.fun · diff-speed-01-run-20261126](https://make.fun/badge/diff-speed-01-run-20261126.svg)](https://make.fun/bounty/diff-speed-01-run-20261126?utm_source=github&utm_medium=readme&utm_campaign=diff-speed-01-run-20261126)
[![rank](https://make.fun/badge/diff-speed-01-run-20261126/LoganZ2/diff-speed-opt-20261127/rank.svg)](https://make.fun/bounty/diff-speed-01-run-20261126/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=diff-speed-01-run-20261126)
[![reward](https://make.fun/badge/diff-speed-01-run-20261126/LoganZ2/diff-speed-opt-20261127/reward.svg)](https://make.fun/bounty/diff-speed-01-run-20261126?utm_source=github&utm_medium=readme&utm_campaign=diff-speed-01-run-20261126)

Exact, zero-dependency drop-in replacement for `makefun-diff 1.0.0` built for the [make.fun Diff two texts faster bounty](https://make.fun/bounty/diff-speed-01-run-20261126).

## Highlights
- **100% byte-for-byte identical** to `makefun-diff 1.0.0` (exact Myers greedy tie-breaking: furthest `oldPos`, deletion wins ties, no edge diagonal pruning, exact `\r\n` and bare-EOF `%` handling).
- **Zero-allocation line scanning & generation-stamped sampled-hash interning** with sequential next-line prediction.
- **Provably admissible suffix lower-bound pruning** (`A`-only/`B`-only counts + 1-to-1 unique-line LIS divergence + monotone chain of disjoint crossing pairs) paired with a tight anchor-based upper bound and periodic pruning checks.
- **Sentinel-terminated ping-pong `Int32Array` Myers + compact `Uint16Array` trace** (with automatic `Int32Array` fallback for texts with >65,534 lines) and Maglev-focused V8 flags (`--no-incremental-marking --no-turbofan --no-concurrent-recompilation`).

## Usage
```bash
node main.ts
```
