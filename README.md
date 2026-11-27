# diff-speed-opt-20261127

Exact, zero-dependency drop-in replacement for `makefun-diff 1.0.0` (`diff-speed-01-run-20261126`).

## Highlights
- **100% byte-for-byte identical** to `makefun-diff 1.0.0` (exact Myers greedy tie-breaking: furthest `oldPos`, deletion wins ties, no edge diagonal pruning, exact `\r\n` and bare-EOF `%` handling).
- **Zero-allocation line scanning & generation-stamped sampled-hash interning** with sequential next-line prediction (~86%+ hit rate).
- **Provably admissible suffix lower-bound pruning** (`A`-only/`B`-only counts + 1-to-1 unique-line LIS divergence + monotone chain of disjoint crossing pairs) paired with a tight anchor-based upper bound and periodic pruning checks (`d & 15 === 0`).
- **Sentinel-terminated ping-pong `Int32Array` Myers + compact `Uint16Array` trace** (with automatic `Int32Array` fallback for texts with >65,534 lines) and Maglev-only V8 flags (`--no-incremental-marking --no-turbofan --no-concurrent-recompilation`) to eliminate short-lived process TurboFan compiler thread overhead.
