# Benchmarks

These benchmarks measure native execution of polynomial queries, initial extraction, rank comparison, and specified-variable pseudo-division on sparse integer polynomials, plus general pseudo-division by a nonzero rational constant and successive remainders over an ordered rational divisor list.

Run from the repository root; the script builds the native executable first:

```bash
./bench/run.sh list
./bench/run.sh verify
./bench/run.sh run --tag pseudo --export-file pseudo.json
./bench/run.sh run --tag main --export-file before.json
./bench/run.sh run --tag main --baseline before.json --export-file after.json
```

`list` shows the available benchmarks; use `--tag main,supplement` to include the supplementary cases. Each configuration is sampled three times, and JSON exports retain the samples for later comparison. In the results, `param` counts input terms for the query benchmarks; for `pseudo`, it is the dividend degree (`successive`) or half that degree (`degreeJump`), while `constant` counts rational dividend terms and `sequence` is the degree d in x*y^d+d. `per-call` is the time per operation, including full result hashing. The `pseudo` cases exercise successive elimination, degree jumps, rational division by 2, and right-to-left division by [x+1, y+1], with inputs prepared outside the timer. The verdict describes how the measured time scales with input size; it is a diagnostic, not a proof of complexity.
