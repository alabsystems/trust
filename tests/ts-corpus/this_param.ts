function describe(this: void, x: number): string { return "#" + x; }
const counter = {
  n: 0,
  inc(this: { n: number }): number { this.n += 1; return this.n; },
};
console.log(describe.call(undefined, 3), counter.inc(), counter.inc());
