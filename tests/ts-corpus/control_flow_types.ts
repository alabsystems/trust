function sum(xs: number[]): number {
  let acc: number = 0;
  for (let i: number = 0; i < xs.length; i++) { acc += xs[i]; }
  for (const x of xs as number[]) { acc += x; }
  return acc;
}
function safe(): string {
  try { throw new Error("boom"); }
  catch (e: unknown) { return e instanceof Error ? e.message : "?"; }
}
console.log(sum([1, 2, 3]), safe());
