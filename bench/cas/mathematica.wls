Clear[x, y];
p = @LHS@;
q = @RHS@;
r = Expand[p*q];
encode[poly_] := If[poly === 0, {}, Map[
  Function[rule, With[{c = Last[rule]},
    <|"powers" -> First[rule], "num" -> ToString[Numerator[c], InputForm],
      "den" -> ToString[Denominator[c], InputForm]|>]],
  CoefficientRules[poly, {x, y}]]];
samples = Table[
  inputs = Table[q + trial*@BATCH@ + k, {k, @BATCH@}];
  ClearSystemCache[];
  elapsed = First[AbsoluteTiming[outputs = Map[Expand[p*#] &, inputs];]];
  <|"seconds" -> elapsed, "outputs" -> Map[encode, outputs]|>,
  {trial, 0, @TRIALS@-1}];
Print["CSBENCH_VERSION:", $Version];
Print["CSBENCH_RESULT:", ExportString[<|"terms" -> encode[r], "samples" -> samples|>, "RawJSON", "Compact" -> True]];
Exit[0];
