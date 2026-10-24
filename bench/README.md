# Benchmarks

These benchmarks measure native execution of polynomial queries, initial extraction, and rank comparison on sparse integer polynomials.

Run from the repository root; the script builds the native executable first:

```bash
./bench/run.sh list
./bench/run.sh run --tag main --export-file before.json
./bench/run.sh run --tag main --baseline before.json --export-file after.json
```

`list` shows the available benchmarks; use `--tag main,supplement` to include the supplementary cases. Each configuration is sampled three times, and JSON exports retain the samples for later comparison. In the results, `param` is the number of input terms and `per-call` is the time per operation, including result hashing. The verdict describes how the measured time scales with input size; it is a diagnostic, not a proof of complexity.
