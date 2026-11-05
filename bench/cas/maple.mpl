# Input expressions are rendered from validated integer/rational JSON data.
restart:
p := @LHS@:
q := @RHS@:
r := expand(p*q):
printf("CSBENCH_VERSION:%s\n", kernelopts(version)):
emit := proc(poly)
local r,pieces,n,i,j,c;
r := poly:
pieces := table():
n := 0:
if r <> 0 then
  for i from 0 to degree(r,x) do
    for j from 0 to degree(r,y) do
      c := coeff(coeff(r,x,i),y,j):
      if c <> 0 then
        n := n+1:
        pieces[n] := sprintf("{\"powers\":[%d,%d],\"num\":\"%d\",\"den\":\"%d\"}",
          i, j, numer(c), denom(c)):
      end if:
    end do:
  end do:
end if:
printf("[%s]", StringTools:-Join([seq(pieces[i],i=1..n)], ",")):

end proc:
printf("CSBENCH_RESULT:{\"terms\":"):
emit(r):
printf(",\"samples\":["):
for trial from 0 to @TRIALS@-1 do
  inputs := [seq(q + trial*@BATCH@ + k, k=1..@BATCH@)]:
  start := time[real]():
  outputs := [seq(expand(p*inputs[k]), k=1..@BATCH@)]:
  elapsed := time[real]() - start:
  if trial > 0 then printf(","): end if:
  printf("{\"seconds\":%.9f,\"outputs\":[", elapsed):
  for k from 1 to @BATCH@ do
    if k > 1 then printf(","): end if:
    emit(outputs[k]):
  end do:
  printf("]}"):
end do:
printf("]}\n"):
quit:
